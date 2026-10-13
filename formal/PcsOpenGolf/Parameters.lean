import Mathlib.Data.ENNReal.Inv

/-! # Parameters

The competition's constants, byte types and the shapes shared by both tracks. Read this file
first; `Field`, `Keccak`, `Relation`, `Oracle`, `Polynomial`, `Machine`, `Submission`, `Security`
and `Statements` build on it in that order.

The values here form parameter set v0 (`docs/rules-app.md`, "Parameters"). The claim price
`CLAIM_CYCLES` is deliberately absent: it is published separately and never enters a
certificate, so a change re-ranks entries without new proofs. -/

namespace PcsOpenGolf

/-! ### Statement -/

/-- Depth of the Merkle tree in the withdrawal statement. -/
def DEPTH : Nat := 32

/-! ### Security -/

/-- Soundness target: with at most `Q` oracle calls, an adversary wins with probability at most
`Q / 2 ^ SECURITY_BITS`, before the per-root margin. -/
def SECURITY_BITS : Nat := 128

/-- Extra soundness charged per root taken from the proof, and the opening track's largest
list, in bits. A real commitment that binds a root only to a list of `2 ^ LIST_BITS` polynomials costs
up to this much per root for every challenge drawn after the root is published. -/
def LIST_BITS : Nat := 12

/-- Zero-knowledge target. -/
def ZK_BITS : Nat := 128

/-- Largest allowed probability, over the oracles and the prover's coins, that an honest proof
fails. -/
noncomputable def FAILURE : ENNReal := 1 / 2 ^ 128

/-! ### Limits -/

def MAX_PROOF_BYTES : Nat := 2 ^ 14

/-- Most `PCS_open` claims in one verifier run. -/
def MAX_CLAIMS : Nat := 8

/-- Most points in one claim. -/
def MAX_POINTS : Nat := 4

/-- Largest committed polynomial is `2 ^ MAX_WORDS_LOG` 64-bit words. -/
def MAX_WORDS_LOG : Nat := 28

/-- Every verifier run halts below this many cycles. Execution is also cut off after this many
instructions, which loses nothing since every instruction costs at least one cycle. -/
def CYCLE_LIMIT : Nat := 2 ^ 24

/-- Data memory, 16 MiB. -/
def MEMORY_BYTES : Nat := 2 ^ 24

/-- Bound on `4 × instructions + embedded data bytes` of the verifier image. -/
def MAX_PROGRAM_BYTES : Nat := 2 ^ 20

/-! ### Opening track -/

/-- The scored instance is a bit polynomial in 26 variables, `2 ^ 20` words, opened at two
points. -/
def SCORED_VARS : Nat := 26

def SCORED_POINTS : Nat := 2

/-- Largest opening proof, and the size of the verifier's proof buffer. -/
def MAX_OPENING_BYTES : Nat := 2 ^ 20

/-- Every opening verifier run halts below this many cycles. -/
def OPENING_CYCLE_LIMIT : Nat := 2 ^ 28

/-! ### Bytes -/

abbrev Byte := BitVec 8

/-- `n` bytes as one little-endian bit vector. -/
abbrev Bytes (n : Nat) := BitVec (8 * n)

/-- `root ‖ nullifier ‖ context`. -/
abbrev PublicInput := Bytes 96

/-- `secret ‖ index ‖ siblings`: 32 + 4 + 32 × 32 bytes. -/
abbrev Witness := Bytes 1060

/-- A commitment's 32-byte root. -/
abbrev Root := Bytes 32

/-- The little-endian bytes of a fixed-size value. -/
def bytesOf {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

/-- The fixed-size value whose little-endian bytes are `data`, padded with zeros or truncated. -/
def ofBytes (n : Nat) (data : List Byte) : Bytes n :=
  (List.range n).foldl (fun acc i => acc ||| ((data.getD i 0).zeroExtend (8 * n) <<< (8 * i))) 0

/-! ### Committed polynomials -/

/-- Whether a committed polynomial's values are bits or 64-bit words of `K`. -/
inductive Kind where
  | bits | words
  deriving DecidableEq, Repr

/-- The descriptor byte for a kind: 0 for bits, 1 for words. -/
def Kind.code : Kind → Nat
  | .bits => 0
  | .words => 1

def Kind.ofCode : Nat → Option Kind
  | 0 => some .bits
  | 1 => some .words
  | _ => none

/-- Base-2 logarithm of a committed polynomial's size in 64-bit words: bits are packed 64 to a
word. -/
def Kind.wordsLog (kind : Kind) (n : Nat) : Nat :=
  match kind with
  | .bits => n - 6
  | .words => n

/-- A polynomial in `n` variables of this kind fits in `2 ^ MAX_WORDS_LOG` words. -/
def Kind.Fits (kind : Kind) (n : Nat) : Prop := kind.wordsLog n ≤ MAX_WORDS_LOG

instance (kind : Kind) (n : Nat) : Decidable (kind.Fits n) := by
  unfold Kind.Fits; infer_instance

end PcsOpenGolf
