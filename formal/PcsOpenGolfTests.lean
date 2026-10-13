import PcsOpenGolf

/-! Regression checks on the executable parts of the contract: Keccak against Ethereum and OpenSSL
vectors, the fields, descriptors, claim truth, and small hand-assembled verifier runs. -/

namespace PcsOpenGolf.Tests
open OracleComp OracleSpec Keccak Rv64 Machine RiscvZkvm.Rv64

/-- Bytes from a hex string, two digits per byte. -/
def hex (s : String) : List Byte :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let ds := s.toList.map digit
  (List.range (ds.length / 2)).map fun i => BitVec.ofNat 8 (16 * ds.getD (2 * i) 0 + ds.getD (2 * i + 1) 0)

/-! ### Keccak -/

-- Ethereum's KECCAK256 of the empty string and of `abc`.
#guard bytesOf (keccak256 []) =
  hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard bytesOf (keccak256 (hex "616263")) =
  hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

-- 135, 136 and 200 bytes of `a`: one block, the padding's second block, two blocks. Digests from
-- OpenSSL 3.6 `dgst -keccak-256`.
#guard bytesOf (keccak256 (List.replicate 135 0x61)) =
  hex "34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446"
#guard bytesOf (keccak256 (List.replicate 136 0x61)) =
  hex "a6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e"
#guard bytesOf (keccak256 (List.replicate 200 0x61)) =
  hex "96ea54061def936c4be90b518992fdc6f12f535068a256229aca54267b4d084d"
example : permutations 135 = 1 ∧ permutations 136 = 2 ∧ permutations 200 = 2 := by decide

-- `ofBytes` inverts `bytesOf`.
#guard bytesOf (ofBytes 32 (hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")) =
  hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

/-! ### Fields -/

-- `x^63 · x = x^64 = x^4 + x^3 + x + 1` in `K`.
#guard kmul (1 <<< 63) 2 = 0x1B
-- `y^3 = y + 1` in `E`.
#guard (let y : E := ⟨0, 1, 0⟩; y * (y * y)) = ⟨1, 1, 0⟩
-- Multiplication commutes and distributes on a sample.
private def a : E := ⟨0x0123456789abcdef, 0xfedcba9876543210, 0x1b⟩
private def b : E := ⟨0xdeadbeefcafebabe, 0x1, 0x8000000000000000⟩
private def c : E := ⟨0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 0x0f0f0f0f0f0f0f0f⟩
#guard a * b = b * a
#guard a * (b + c) = a * b + a * c
#guard (a * b) * c = a * (b * c)
-- `E.decode` inverts `E.encode`.
#guard E.decode a.encode = a

/-! ### Polynomials, descriptors and claims -/

private def f : Poly := ⟨2, .words, [3, 5, 7, 11]⟩
private def zero : E := 0
private def one : E := 1
-- A Boolean point reads the table: `(1, 0)` is index 1, `(0, 1)` is index 2.
#guard f.eval [one, zero] = E.ofK 5
#guard f.eval [zero, one] = E.ofK 7
-- A bit polynomial: word 0 holds bits 0 to 63; `(1, 1, 0, 0, 0, 0)` is index 3.
#guard (Poly.eval ⟨6, .bits, [0b1000]⟩ [one, one, zero, zero, zero, zero]) = one
example : f.Valid := by decide
example : ¬ (Poly.Valid ⟨2, .words, [3, 5, 7]⟩) := by decide

private def root : Root := ofBytes 32 (List.replicate 32 0xab)
private def claimAt (p : List E) : Claim := ⟨root, 2, .words, [p], [f.eval p]⟩
#guard Header.parse (claimAt [a, b]).descriptor = some ⟨root, 2, .words, 1⟩
#guard (Header.parse (claimAt [a, b]).descriptor).map (·.claim (claimAt [a, b]).descriptor) =
  some (claimAt [a, b])
-- No points, too many points, an unknown kind, nonzero padding, a polynomial too large.
private def header (n kind k pad : Nat) : List Byte :=
  bytesOf root ++ [BitVec.ofNat 8 n, BitVec.ofNat 8 kind, BitVec.ofNat 8 k, BitVec.ofNat 8 pad,
    0, 0, 0, 0]
#guard (Header.parse (header 2 1 1 0)).isSome
#guard (Header.parse (header 2 1 0 0)).isNone
#guard (Header.parse (header 2 1 5 0)).isNone
#guard (Header.parse (header 2 2 1 0)).isNone
#guard (Header.parse (header 2 1 1 1)).isNone
#guard (Header.parse (header 28 1 1 0)).isSome ∧ (Header.parse (header 29 1 1 0)).isNone
#guard (Header.parse (header 34 0 1 0)).isSome ∧ (Header.parse (header 35 0 1 0)).isNone

-- A claim is true of the first polynomial committed under its root, and only with the right
-- size, kind and values.
private def tables : Tables := { commits := [(root, f), (root, ⟨2, .words, [0, 0, 0, 0]⟩)] }
#guard decide ((claimAt [a, b]).Holds tables)
#guard !decide (({ claimAt [a, b] with values := [0] } : Claim).Holds tables)
#guard !decide (({ claimAt [a, b] with kind := .bits } : Claim).Holds tables)
#guard !decide ((claimAt [a, b]).Holds {})

/-! ### Verifier runs -/

private def addi (rd rs : Nat) (immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def ecall : BitVec 32 := 0x73
/-- `t0 ← service; ecall`. -/
private def call (service : Nat) : List (BitVec 32) := [addi 5 0 service, ecall]
private def halt (code : Nat) : List (BitVec 32) := [addi 10 0 code] ++ call 1

/-- `T` is Keccak-256, as it is natively. -/
private def keccakHash : Hash := fun input => keccak256 input
private def layout : Layout := ⟨0x40, 0x100⟩
private def x : PublicInput := ofBytes 96 (List.range 96 |>.map (BitVec.ofNat 8))
private def run (image : Image) (proof : List Byte) (fixedRoots : List Root := []) : Execution :=
  evalWithAnswerFn keccakHash (verify image layout fixedRoots x proof)

-- Accept at once: the initial absorb (8) and two instructions.
#guard (run ⟨halt 0, []⟩ []).exit = .success ∧ (run ⟨halt 0, []⟩ []).cycles = 8 + 3
-- A nonzero exit code, an unread proof byte, an unknown service, and running off the code.
#guard (run ⟨halt 1, []⟩ []).exit = .failure
#guard (run ⟨halt 0, []⟩ [7]).exit = .failure
#guard (run ⟨call 6, []⟩ []).exit = .failure
#guard (run ⟨[addi 10 0 0], []⟩ []).exit = .failure

/-- `READ` 8 bytes to `0x200`, `SQUEEZE` to `0x300`, accept. -/
private def readSqueeze : Image :=
  ⟨[addi 10 0 0x200, addi 11 0 8] ++ call 2 ++ [addi 10 0 0x300] ++ call 3 ++ halt 0, []⟩
private def proof8 : List Byte := hex "0102030405060708"
private def squeezed : Execution := run readSqueeze proof8
#guard squeezed.exit = .success
-- 8 + 2 (addi) + 1 + 2 (READ) + 1 + 1 + 8 (SQUEEZE of 40 bytes) + 2 + 1 (HALT)
#guard squeezed.cycles = 8 + 2 + 1 + 2 + 1 + 1 + 8 + 2 + 1
#guard readBytes squeezed.run.machine 0x200 8 = proof8
#guard readBytes squeezed.run.machine 0x300 32 =
  bytesOf (keccak256 (bytesOf (keccak256 (DOMAIN ++ bytesOf x)) ++ proof8))
#guard squeezed.run.transcript.buffer = []
-- Reading past the end faults.
#guard (run readSqueeze (proof8.take 7)).exit = .failure
-- The public input is in memory at δₓ.
#guard readBytes squeezed.run.machine 0x40 96 = bytesOf x

/-- `FMUL` of the elements in data at `sp` and `sp + 24`, product at `0x400`. -/
private def multiply : Image :=
  ⟨[addi 10 2 0, addi 11 2 24, addi 12 0 0x400] ++ call 4 ++ halt 0,
    bytesOf a.encode ++ bytesOf b.encode⟩
#guard (run multiply []).exit = .success
#guard E.decode (readBuffer (run multiply []).run.machine 0x400 24) = a * b

/-- `CLAIM` the descriptor at `sp` once, or twice. -/
private def claimOnce : Image := ⟨[addi 10 2 0] ++ call 5 ++ halt 0, (claimAt [a, b]).descriptor⟩
private def claimTwice : Image :=
  ⟨[addi 10 2 0] ++ call 5 ++ call 5 ++ halt 0, (claimAt [a, b]).descriptor⟩
#guard (run claimOnce []).exit = .success ∧ (run claimOnce []).claims = [claimAt [a, b]]
-- `CLAIM` is free: 8 + 1 + 1 + 0 + 2 + 1.
#guard (run claimOnce []).cycles = 8 + 1 + 1 + 0 + 2 + 1
-- The same root twice faults.
#guard (run claimTwice []).exit = .failure
-- A fixed root appears at δ_vk.
#guard readBytes (run ⟨halt 0, []⟩ [] [root]).run.machine 0x100 32 = bytesOf root

/-! ### Opening verifier runs -/

namespace Opening
open PcsOpenGolf.Opening PcsOpenGolf.Opening.Machine

/-- `H` answers with the input's first 32 bytes, so tests can see what was hashed. -/
private def echo : PcsOpenGolf.Opening.Hash := fun query => query.2.truncate 256
private def openingLayout : PcsOpenGolf.Opening.Machine.Layout := ⟨0x1000, 0x10000⟩
private def runOpening (image : Image) (descriptor proof : List Byte) :
    PcsOpenGolf.Opening.Machine.Execution :=
  evalWithAnswerFn echo (PcsOpenGolf.Opening.Machine.verify image openingLayout descriptor proof)

-- `HASH` one block of the descriptor to `0x200`, then accept: 3 + 1 + 8 + 2 + 1 cycles, plus one
-- cycle for receiving a 1-byte proof.
private def hashDescriptor : Image :=
  ⟨[addi 10 0 0, addi 11 0 64, addi 12 0 0x200, addi 10 10 0x400, addi 10 10 0x400,
    addi 10 10 0x400, addi 10 10 0x400, addi 5 0 0, ecall] ++ halt 0, []⟩
#guard (runOpening hashDescriptor (claimAt [a, b]).descriptor [1]).exit = .success
#guard (runOpening hashDescriptor (claimAt [a, b]).descriptor [1]).cycles = 8 + 8 + 2 + 1 + 1
#guard readBytes (runOpening hashDescriptor (claimAt [a, b]).descriptor []).state 0x200 32 =
  ((claimAt [a, b]).descriptor.take 32)
-- Receiving costs ⌈|proof| / 256⌉.
#guard (runOpening ⟨halt 0, []⟩ [] []).cycles = 3
#guard (runOpening ⟨halt 0, []⟩ [] (List.replicate 257 0)).cycles = 3 + 2
-- A length that is not a multiple of 64 faults.
#guard (runOpening ⟨[addi 11 0 63, addi 5 0 0, ecall] ++ halt 0, []⟩ [] []).exit = .failure
-- `FMUL` is service 2 here.
private def multiplyOpening : Image :=
  ⟨[addi 10 2 0, addi 11 2 24, addi 12 0 0x400, addi 5 0 2, ecall] ++ halt 0,
    bytesOf a.encode ++ bytesOf b.encode⟩
#guard (runOpening multiplyOpening [] []).exit = .success
#guard E.decode (readBuffer (runOpening multiplyOpening [] []).state 0x400 24) = a * b
-- Service 5, the app's `CLAIM`, does not exist here.
#guard (runOpening ⟨call 5 ++ halt 0, []⟩ [] []).exit = .failure

-- The descriptor bound: bits in 34 variables at 4 points.
example : MAX_DESCRIPTOR_BYTES = 40 + 24 * 4 * 34 + 24 * 4 := by decide

end Opening

end PcsOpenGolf.Tests
