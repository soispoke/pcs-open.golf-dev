import PcsOpenGolf.Parameters

/-! # Fields

`K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, an element being a 64-bit vector whose bit `i` is the
coefficient of `x^i`, and `E = K[y] / (y^3 + y + 1)`, an element being `c0 + c1·y + c2·y^2`. These
are leanVM's base and extension fields: committed data lives in `K`, points and values in `E`.
`y^3 + y + 1` is irreducible over `K` because its roots lie in `GF(8)`, which `K` does not contain.

Everything here is executable, so the tests can check it on concrete values. Field laws are not
proved in the contract; entrants who need them prove them in their own modules. -/

namespace PcsOpenGolf

/-! ### `K` -/

abbrev K := BitVec 64

/-- Carry-less product of two 64-bit vectors: polynomial multiplication over `GF(2)`. -/
def clmul (a b : K) : BitVec 128 :=
  (List.range 64).foldl
    (fun acc i => if b.getLsbD i then acc ^^^ ((a.zeroExtend 128) <<< i) else acc) 0

/-- One fold of the bits above 63: `x^64 = x^4 + x^3 + x + 1`. -/
def kfold (r : BitVec 128) : BitVec 128 :=
  let hi := r >>> 64
  (r &&& ((1 <<< 64) - 1)) ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4)

/-- Reduction modulo `x^64 + x^4 + x^3 + x + 1`. Two folds suffice: after one, at most the bits
64 to 66 are set. -/
def kreduce (r : BitVec 128) : K := (kfold (kfold r)).truncate 64

def kmul (a b : K) : K := kreduce (clmul a b)

/-! ### `E` -/

/-- `c0 + c1·y + c2·y^2`. -/
structure E where
  c0 : K
  c1 : K
  c2 : K
  deriving DecidableEq, Repr

namespace E

def zero : E := ⟨0, 0, 0⟩
def one : E := ⟨1, 0, 0⟩

/-- `K` inside `E`. -/
def ofK (k : K) : E := ⟨k, 0, 0⟩

instance : Zero E := ⟨zero⟩
instance : One E := ⟨one⟩

/-- Addition is XOR, coefficient by coefficient. -/
instance : Add E := ⟨fun a b => ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2⟩⟩

/-- Schoolbook product, then `y^3 = y + 1` and `y^4 = y^2 + y`. -/
def mul (a b : E) : E :=
  let d0 := clmul a.c0 b.c0
  let d1 := clmul a.c0 b.c1 ^^^ clmul a.c1 b.c0
  let d2 := clmul a.c0 b.c2 ^^^ clmul a.c1 b.c1 ^^^ clmul a.c2 b.c0
  let d3 := clmul a.c1 b.c2 ^^^ clmul a.c2 b.c1
  let d4 := clmul a.c2 b.c2
  ⟨kreduce (d0 ^^^ d3), kreduce (d1 ^^^ d3 ^^^ d4), kreduce (d2 ^^^ d4)⟩

instance : Mul E := ⟨mul⟩

/-- The 24-byte encoding `c0 ‖ c1 ‖ c2`, little-endian. -/
def encode (a : E) : Bytes 24 := (a.c2 ++ a.c1 ++ a.c0 : BitVec 192)

def decode (b : Bytes 24) : E :=
  ⟨b.extractLsb' 0 64, b.extractLsb' 64 64, b.extractLsb' 128 64⟩

end E

end PcsOpenGolf
