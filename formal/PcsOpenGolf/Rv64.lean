import PcsOpenGolf.Field
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter.Decode

/-! # RV64IM core

The instruction set both tracks' verifiers run on: a raw instruction image, memory checks, the
RV64IM decoder, one ordinary step and its price. System calls differ between the tracks and are
defined in `Machine` (app) and `OpeningMachine` (opening).

Adapted from sig.golf's `SigGolf/Riscv.lean` at commit `ab2a83af` (Apache-2.0,
https://github.com/Layr-Labs/sig.golf): images, memory checks, the W-suffixed word operations,
the decoder, `ordinaryStep`, `instructionCycles` and `fetch` are sig.golf's, unchanged except for
names. The base RV64IM decoder and instruction semantics come from the pinned `riscv-zkvm` model.
The imported executable decoder is not formally related to the upstream Sail decoder. -/

namespace PcsOpenGolf.Rv64
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

/-! ### Images -/

/-- Instruction encodings and the data bytes loaded at `dataBase`. -/
structure Image where
  code : List (BitVec 32)
  data : List Byte

def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length

/-- Embedded data sits at the top of memory, 16-byte aligned; `sp` starts here. -/
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)

/-- Two buffers `(address, length)` do not overlap; an empty buffer overlaps nothing. -/
abbrev DisjointBuffers (left right : Nat × Nat) : Prop :=
  left.2 = 0 ∨ right.2 = 0 ∨ left.1 + left.2 ≤ right.1 ∨ right.1 + right.2 ≤ left.1

/-- Input buffers are 8-byte aligned, end at or below `dataBase`, and do not overlap. -/
abbrev BuffersValid (buffers : List (Nat × Nat)) (image : Image) : Prop :=
  (∀ buffer ∈ buffers, buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ dataBase image) ∧
    buffers.Pairwise DisjointBuffers

/-! ### Memory -/

def initialMachine : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }

/-- Memory holds only the embedded data and the given buffers; `sp`, register `x2`, starts at
`dataBase`. -/
def loadMachine (image : Image) (buffers : List (Nat × List Byte)) : MachineState :=
  let base := BitVec.ofNat 64 (dataBase image)
  let withData := initialMachine.writeBytesAsWords base image.data
  let loaded := buffers.foldl
    (fun state (offset, data) => state.writeBytesAsWords (BitVec.ofNat 64 offset) data) withData
  loaded.setReg .x2 base

def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)

def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)

/-- `n` bytes at `address`, in order. -/
def readBytes (state : MachineState) (address n : Nat) : List Byte :=
  (List.range n).map fun i => state.getByte (BitVec.ofNat 64 (address + i))

/-- Little-endian read of `n` bytes at `address`. -/
def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  ofBytes n (readBytes state address n)

/-- Write bytes one by one from `address`, leaving the rest of each doubleword alone. -/
def writeBytes (state : MachineState) (address : Nat) (bytes : List Byte) : MachineState :=
  (List.range bytes.length).foldl
    (fun s i => s.setByte (BitVec.ofNat 64 (address + i)) (bytes.getD i 0)) state

/-! ### Decoding -/

/-- The 32-bit, `W`-suffixed register operations `ADDW` to `REMUW`, decoded here in place of the
upstream decoder, which models only two of the ten. -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq

inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)

/-- Decode one 32-bit encoding: `ECALL` and `EBREAK` exactly, the W-suffixed operations and
`SRAIW`, then the upstream decoder. Other SYSTEM encodings, the CSR instructions, do not decode;
assembler pseudo-instructions have no encoding. -/
def decodeInstruction (word : BitVec 32) : Option Instruction := do
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x73 then
    if word = 0x00000073 then return .base .ECALL
    else if word = 0x00100073 then return .base .EBREAK
    else none
  else if opcode = 0x3b then
    let op ← match f7, f3 with
      | 0, 0 => some WordOp.add
      | 0x20, 0 => some .sub
      | 0, 1 => some .sll
      | 0, 5 => some .srl
      | 0x20, 5 => some .sra
      | 1, 0 => some .mul
      | 1, 4 => some .div
      | 1, 5 => some .divu
      | 1, 6 => some .rem
      | 1, 7 => some .remu
      | _, _ => none
    return .word op rd rs1 rs2
  else if opcode = 0x1b && f3 = 5 && f7 = 0x20 then
    return .sraiw rd rs1 (word.extractLsb' 20 5)
  else
    return .base (← decode word)

/-- The 32-bit result of a `W` operation: shifts use the low five bits of `b`; division by zero
gives all ones and remainder by zero gives `a`, as RISC-V specifies. -/
def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b

/-! ### One step -/

/-- Every data access is bounds- and alignment-checked; address zero is an ordinary valid
address. -/
def memoryArgumentsValid (state : MachineState) (instruction : Instr) : Bool :=
  match memAccess state instruction with
  | some (address, width, _) => accessValid address width
  | none => true

/-- One ordinary instruction. Of the first two arms only `EBREAK` is reachable: the machines
handle `ECALL` first, and `decodeInstruction` never produces CSR or pseudo-instructions. They are
listed so this does not depend on that. -/
def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base .ECALL | .base .EBREAK | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base .NOP => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))

/-- `ECALL` is priced by each machine. -/
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1

def fetch (image : Image) (state : MachineState) : Option Instruction :=
  if 0x1000 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0 then
    match image.code[(state.pc.toNat - 0x1000) / 4]? with
    | some word => decodeInstruction word
    | none => none
  else none

/-! ### Field multiplication -/

/-- `FMUL`'s arguments: both inputs and the output 8-byte aligned and inside memory. -/
def fmulArgumentsValid (state : MachineState) : Bool :=
  [state.getReg .x10, state.getReg .x11, state.getReg .x12].all fun address =>
    decide (address.toNat % 8 = 0) && rangeValid address 24

/-- Multiply the `E` elements at `a0` and `a1` and write the product at `a2`; both inputs are
read before the output is written, so the buffers may overlap. -/
def fmul (state : MachineState) : MachineState :=
  let a := E.decode (readBuffer state (state.getReg .x10).toNat 24)
  let b := E.decode (readBuffer state (state.getReg .x11).toNat 24)
  (writeBytes state (state.getReg .x12).toNat (bytesOf (a * b).encode)).setPC (state.pc + 4)

end PcsOpenGolf.Rv64
