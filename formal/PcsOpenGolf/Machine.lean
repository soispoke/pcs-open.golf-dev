import PcsOpenGolf.Oracle
import PcsOpenGolf.Rv64
import PcsOpenGolf.Keccak

/-! # The verifier machine

The app verifier stands in for the contract. It runs on the RV64IM core (`Rv64`) with five
system calls, selected by `t0`:

| `t0` | Service | Cycles |
| ---: | --- | --- |
| 1 | `HALT`: exit code in `a0`, 0 to accept | 1 |
| 2 | `READ`: copy the next `a1` proof bytes to `a0` and append them to the transcript buffer | `1 + ⌈n / 8⌉` |
| 3 | `SQUEEZE`: write the next 32-byte challenge at `a0` | 8 per Keccak-f permutation |
| 4 | `FMUL`: multiply the `E` elements at `a0` and `a1`, write the product at `a2` | 8 |
| 5 | `CLAIM`: record the claim whose descriptor is at `a0` | 0 |

The proof is not in memory: `READ` takes it from a tape in order. Halting with 0 accepts only
once the whole tape has been read. The transcript keeps a 32-byte state `s` and a byte buffer
`β`. It starts with `s = T(DOMAIN ‖ x)`; `READ` appends to `β`; `SQUEEZE` sets `s ← T(s ‖ β)`,
empties `β` and returns `s`. A `CLAIM` costs no cycles here because the score prices claims
separately (`CLAIM_CYCLES`, published outside the contract). A malformed descriptor, a root
already claimed, a claim beyond `MAX_CLAIMS`, any misaligned or out-of-range buffer, and any
other `t0` are faults, and a fault rejects. -/

namespace PcsOpenGolf.Machine
open RiscvZkvm.Rv64 OracleComp OracleSpec Rv64

/-! ### Layout -/

/-- Where the verifier finds its inputs: the 96-byte public input at δₓ and the fixed roots,
32 bytes each in the order the submission declares them, at δ_vk. -/
structure Layout where
  publicInput : Nat
  fixedRoots : Nat

def Layout.buffers (layout : Layout) (fixedCount : Nat) : List (Nat × Nat) :=
  [(layout.publicInput, 96), (layout.fixedRoots, 32 * fixedCount)]

/-- Within the program size limit, with aligned, nonoverlapping input buffers below its data. -/
abbrev ImageValid (image : Image) (layout : Layout) (fixedCount : Nat) : Prop :=
  image.byteSize < MAX_PROGRAM_BYTES ∧ BuffersValid (layout.buffers fixedCount) image

/-! ### Run state -/

/-- The ASCII string `pcs_open.golf v0`, absorbed before the public input. -/
def DOMAIN : List Byte := "pcs_open.golf v0".toUTF8.toList.map fun b => b.toBitVec

/-- The transcript's state `s` and buffer `β`. -/
structure Transcript where
  state : Bytes 32
  buffer : List Byte

/-- Everything a run changes besides the machine: the unread proof bytes, the transcript, and
the claims made so far, in order. -/
structure Run where
  machine : MachineState
  tape : List Byte
  transcript : Transcript
  claims : List Claim

/-- How a run ended: `HALT` with exit code 0 after reading the whole proof; any fault, nonzero
exit code or early accept; or still running when the step limit was reached. -/
inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq

/-- `cycles` counts every instruction and system call except `CLAIM`, which is free here. -/
structure Execution where
  exit : Exit
  run : Run
  cycles : Nat

def Execution.charge (result : Execution) (cycles : Nat) : Execution :=
  { result with cycles := cycles + result.cycles }

/-- The claims a finished run made. -/
def Execution.claims (result : Execution) : List Claim := result.run.claims

/-! ### System calls -/

/-- What a system call did: halted with an exit decision, faulted, or continued with a new run
state after spending some cycles. -/
inductive Service where
  | halt (accept : Bool)
  | fault
  | next (run : Run) (cycles : Nat)

/-- `READ`: `a0` is the destination, `a1` the byte count `n`. Reading past the end of the proof
is a fault. -/
def read (run : Run) : Service :=
  let state := run.machine
  let destination := state.getReg .x10
  let n := (state.getReg .x11).toNat
  if destination.toNat % 8 = 0 ∧ rangeValid destination n ∧ n ≤ run.tape.length then
    let bytes := run.tape.take n
    .next { run with
        machine := (writeBytes state destination.toNat bytes).setPC (state.pc + 4),
        tape := run.tape.drop n,
        transcript := { run.transcript with buffer := run.transcript.buffer ++ bytes } }
      (1 + (n + 7) / 8)
  else .fault

/-- `SQUEEZE`: `a0` is the destination. Hashing `s ‖ β`, `32 + m` bytes, costs 8 cycles per
Keccak-f permutation. -/
def squeeze (run : Run) : OracleComp HashSpec Service := do
  let state := run.machine
  let destination := state.getReg .x10
  if destination.toNat % 8 = 0 ∧ rangeValid destination 32 then
    let input := bytesOf run.transcript.state ++ run.transcript.buffer
    let answer ← HashSpec.query input
    return .next { run with
        machine := (writeBytes state destination.toNat (bytesOf answer)).setPC (state.pc + 4),
        transcript := ⟨answer, []⟩ }
      (8 * Keccak.permutations input.length)
  else return .fault

/-- `FMUL`, `MUL_FIELD`'s stand-in: twice a 64-bit multiplication, since one product in `E` takes
six products in `K`. -/
def fieldMul (run : Run) : Service :=
  if fmulArgumentsValid run.machine then .next { run with machine := fmul run.machine } 8
  else .fault

/-- `CLAIM`: `a0` is the descriptor's address. The header is read and checked first, then the
whole descriptor must fit in memory, its root must be new to this run, and the run must have
made fewer than `MAX_CLAIMS` claims. -/
def claim (run : Run) : Service :=
  let state := run.machine
  let address := state.getReg .x10
  if address.toNat % 8 = 0 ∧ rangeValid address HEADER_BYTES then
    match Header.parse (readBytes state address.toNat HEADER_BYTES) with
    | none => .fault
    | some header =>
      let size := descriptorBytes header.vars header.count
      if rangeValid address size ∧ run.claims.all (·.root ≠ header.root) ∧
          run.claims.length < MAX_CLAIMS then
        let made := header.claim (readBytes state address.toNat size)
        .next { run with machine := state.setPC (state.pc + 4), claims := run.claims ++ [made] } 0
      else .fault
  else .fault

def systemCall (run : Run) : OracleComp HashSpec Service :=
  match (run.machine.getReg .x5).toNat with
  | 1 => pure (.halt (run.machine.getReg .x10 = 0 ∧ run.tape = []))
  | 2 => pure (read run)
  | 3 => squeeze run
  | 4 => pure (fieldMul run)
  | 5 => pure (claim run)
  | _ => pure .fault

/-! ### Execution -/

/-- A program still running after `steps` instructions is reported `unfinished`. `CLAIM` costs no
cycles, so such a run may show slightly fewer than `steps` cycles; `Termination` therefore rules
out `unfinished` explicitly as well as bounding cycles. -/
def execute (image : Image) : Nat → Run → OracleComp HashSpec Execution
  | 0, run => pure { exit := .unfinished, run := run, cycles := 0 }
  | steps + 1, run =>
    match fetch image run.machine with
    | none => pure { exit := .failure, run := run, cycles := 0 }
    | some (.base .ECALL) => do
      match ← systemCall run with
      | .halt accept => pure { exit := if accept then .success else .failure, run := run, cycles := 1 }
      | .fault => pure { exit := .failure, run := run, cycles := 1 }
      | .next next cycles => do
        let result ← execute image steps next
        return result.charge cycles
    | some instruction =>
      match ordinaryStep run.machine instruction with
      | none => pure { exit := .failure, run := run, cycles := 1 }
      | some next => do
        let result ← execute image steps { run with machine := next }
        return result.charge (instructionCycles instruction)

/-- One verifier run on public input `x`, fixed roots `fixedRoots` and proof bytes `proof`:
absorb `DOMAIN ‖ x`, charged like `SQUEEZE`, then execute for at most `CYCLE_LIMIT` steps. An
image that fails `ImageValid` is run as is; the statements are meant together with
`Admission`. -/
def verify (image : Image) (layout : Layout) (fixedRoots : List Root) (x : PublicInput)
    (proof : List Byte) : OracleComp HashSpec Execution := do
  let input := DOMAIN ++ bytesOf x
  let state ← HashSpec.query input
  let machine := loadMachine image
    [(layout.publicInput, bytesOf x), (layout.fixedRoots, fixedRoots.flatMap bytesOf)]
  let result ← execute image CYCLE_LIMIT ⟨machine, proof, ⟨state, []⟩, []⟩
  return result.charge (8 * Keccak.permutations input.length)

end PcsOpenGolf.Machine
