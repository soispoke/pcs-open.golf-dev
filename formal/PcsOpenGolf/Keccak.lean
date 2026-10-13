import PcsOpenGolf.Parameters

/-! # Keccak

Keccak-f[1600] and Keccak-256 with Ethereum's original padding (`0x01 … 0x80`), as computed by the
EVM's `KECCAK256`; this is not SHA3-256, whose padding differs. The state is 25 lanes of 64 bits,
lane `x + 5y` holding coordinates `(x, y)`, and bytes enter lanes little-endian.

The withdrawal relation (`Relation`) uses this function concretely, so a proof must compute it in
its constraints. The verifier's Fiat-Shamir hash is the same function in practice, but the model
treats it as an independent random oracle (`Oracle`). -/

namespace PcsOpenGolf.Keccak

/-- Bytes absorbed per permutation. -/
def RATE : Nat := 136

def roundConstants : List (BitVec 64) :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
   0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
   0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offset of lane `(x, y)`, listed by `x` then `y`. -/
def rotationOffsets : List (List Nat) :=
  [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
   [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]

abbrev State := List (BitVec 64)

def lane (a : State) (x y : Nat) : BitVec 64 := a.getD (x + 5 * y) 0

/-- One round: θ, ρ and π, χ, then ι with round constant `rc`. -/
def round (a : State) (rc : BitVec 64) : State :=
  let c := (List.range 5).map fun x =>
    lane a x 0 ^^^ lane a x 1 ^^^ lane a x 2 ^^^ lane a x 3 ^^^ lane a x 4
  let d := (List.range 5).map fun x =>
    c.getD ((x + 4) % 5) 0 ^^^ (c.getD ((x + 1) % 5) 0).rotateLeft 1
  let theta := (List.range 25).map fun i => a.getD i 0 ^^^ d.getD (i % 5) 0
  -- π sends lane (x, y) to (y, 2x + 3y); lane (X, Y) therefore comes from y = X and
  -- x = 3 (Y - 3X) mod 5, since 3 is the inverse of 2 modulo 5.
  let b := (List.range 25).map fun j =>
    let bx := j % 5
    let by_ := j / 5
    let y := bx
    let x := (3 * ((by_ + 15 - 3 * bx) % 5)) % 5
    (lane theta x y).rotateLeft ((rotationOffsets.getD x []).getD y 0)
  let chi := (List.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b.getD i 0 ^^^ ((~~~ (b.getD ((x + 1) % 5 + 5 * y) 0)) &&& b.getD ((x + 2) % 5 + 5 * y) 0)
  chi.set 0 (chi.getD 0 0 ^^^ rc)

/-- Keccak-f[1600]: 24 rounds. -/
def permute (a : State) : State := roundConstants.foldl round a

/-- A 64-bit lane from 8 bytes, little-endian. -/
def laneOfBytes (bytes : List Byte) : BitVec 64 :=
  (List.range 8).foldl (fun acc i => acc ||| ((bytes.getD i 0).zeroExtend 64 <<< (8 * i))) 0

/-- Ethereum's padding: append `0x01`, zeros to a multiple of `RATE`, and set the top bit of the
last byte. -/
def pad (msg : List Byte) : List Byte :=
  let withOne := msg ++ [1]
  let padded := withOne ++ List.replicate ((RATE - withOne.length % RATE) % RATE) 0
  padded.set (padded.length - 1) (padded.getD (padded.length - 1) 0 ||| 0x80)

/-- Permutations used to hash `n` bytes: `⌈(n + 1) / RATE⌉`. -/
def permutations (n : Nat) : Nat := (n + 1 + RATE - 1) / RATE

def absorb (state : State) (block : List Byte) : State :=
  permute ((List.range 25).map fun i =>
    if i < RATE / 8 then state.getD i 0 ^^^ laneOfBytes (block.drop (8 * i)) else state.getD i 0)

/-- Keccak-256 of a byte string. -/
def keccak256 (msg : List Byte) : Bytes 32 :=
  let padded := pad msg
  let blocks := (List.range (padded.length / RATE)).map fun k => (padded.drop (RATE * k)).take RATE
  let state := blocks.foldl absorb (List.replicate 25 0)
  ((lane state 3 0 ++ lane state 2 0 ++ lane state 1 0 ++ lane state 0 0 : BitVec 256) :)

/-- `H64(a, b) = Keccak-256(a ‖ b)` for two 32-byte strings: one permutation. -/
def H64 (a b : Bytes 32) : Bytes 32 := keccak256 (bytesOf a ++ bytesOf b)

end PcsOpenGolf.Keccak
