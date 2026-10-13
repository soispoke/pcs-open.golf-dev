import PcsOpenGolf.Opening.Oracle
import PcsOpenGolf.Rv64

/-! # Opening track: the verifier machine

The opening verifier runs on the RV64IM core (`Rv64`) with three system calls, selected by `t0`:

| `t0` | Service | Cycles |
| ---: | --- | --- |
| 0 | `HASH`: `H` on `a1` bytes at `a0`, the 32-byte answer written at `a2` | 8 per 64-byte block |
| 1 | `HALT`: exit code in `a0`, 0 to accept | 1 |
| 2 | `FMUL`: multiply the `E` elements at `a0` and `a1`, write the product at `a2` | 8 |

`HASH` is sig.golf's, with its argument rules: both addresses 8-byte aligned, a positive length
that is a multiple of 64, and both buffers inside memory. There is no transcript service:
Fiat-Shamir is the entrant's own code built on `HASH`, and it must start from the whole claim
descriptor. Before the run, memory is zero except for embedded data, the descriptor at δ_claim
and the opening proof at δ_proof; the verifier pays `⌈|proof| / 256⌉` cycles for receiving the
proof. Any other `t0`, and any malformed argument, is a fault, and a fault rejects. -/

namespace PcsOpenGolf.Opening.Machine
open RiscvZkvm.Rv64 OracleComp OracleSpec Rv64

/-! ### Layout -/

/-- Where the verifier finds its inputs: a `MAX_DESCRIPTOR_BYTES` buffer for the claim descriptor
and a `MAX_OPENING_BYTES` buffer for the opening proof, each zero after its contents. -/
structure Layout where
  descriptor : Nat
  proof : Nat

def Layout.buffers (layout : Layout) : List (Nat × Nat) :=
  [(layout.descriptor, MAX_DESCRIPTOR_BYTES), (layout.proof, MAX_OPENING_BYTES)]

abbrev ImageValid (image : Image) (layout : Layout) : Prop :=
  image.byteSize < MAX_PROGRAM_BYTES ∧ BuffersValid layout.buffers image

/-! ### HASH -/

/-- `HASH` takes the input address in `a0`, the byte length in `a1`, and the output address in
`a2`; it reads whole blocks only. -/
def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bytes := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && decide (0 < bytes ∧ bytes % 64 = 0) &&
    rangeValid source bytes && decide (destination.toNat % 8 = 0) && rangeValid destination 32

/-- The input bytes as a `Query` of `a1 / 64` blocks. -/
def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat / 64 - 1
  ⟨n, readBuffer state (state.getReg .x10).toNat (64 * (n + 1))⟩

def writeHash (state : MachineState) (answer : Bytes 32) : MachineState :=
  (writeBytes state (state.getReg .x12).toNat (bytesOf answer)).setPC (state.pc + 4)

/-! ### Execution and costs -/

inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq

structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat

def Execution.charge (result : Execution) (cycles : Nat) : Execution :=
  { result with cycles := cycles + result.cycles }

/-- A program still running after `steps` instructions is reported `unfinished`. -/
def execute (image : Image) : Nat → MachineState → OracleComp HashSpec Execution
  | 0, state => pure { exit := .unfinished, state := state, cycles := 0 }
  | steps + 1, state =>
    match fetch image state with
    | none => pure { exit := .failure, state := state, cycles := 0 }
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute image steps (writeHash state answer)
        return result.charge (8 * input.blocks)
      else if state.getReg .x5 = 1 then
        pure { exit := if state.getReg .x10 = 0 then .success else .failure, state := state,
               cycles := 1 }
      else if state.getReg .x5 = 2 && fmulArgumentsValid state then do
        let result ← execute image steps (fmul state)
        return result.charge 8
      else pure { exit := .failure, state := state, cycles := 1 }
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure { exit := .failure, state := state, cycles := 1 }
      | some next => do
        let result ← execute image steps next
        return result.charge (instructionCycles instruction)

/-- One verifier run on descriptor bytes and proof bytes, each loaded into its buffer, for at
most `OPENING_CYCLE_LIMIT` steps, plus the receiving charge. Inputs longer than their buffers are
the statements' concern: they quantify only over inputs that fit. -/
def verify (image : Image) (layout : Layout) (descriptor proof : List Byte) :
    OracleComp HashSpec Execution := do
  let machine := loadMachine image [(layout.descriptor, descriptor), (layout.proof, proof)]
  let result ← execute image OPENING_CYCLE_LIMIT machine
  return result.charge ((proof.length + 255) / 256)

end PcsOpenGolf.Opening.Machine
