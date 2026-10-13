import PcsOpenGolf.Field

/-! # Polynomials and claims

A committed polynomial is multilinear in `n` variables and given by its values on `{0,1}^n`, the
value at `b` being table entry `Σ b_j 2^j`, so coordinate 0 is the least significant index bit.
Its kind says whether the values are bits or 64-bit words of `K`; bits are packed 64 to a word,
entry `i` being bit `i mod 64` of word `⌊i / 64⌋`.

A claim says "the polynomial behind root `R` has `n` variables, this kind, and value `v_j` at
point `p_j` for every `j`". Its descriptor is the byte string `PCS_open` receives: the root, then
`n`, the kind code and the number of points `k` as one byte each, five zero bytes, the `k · n`
coordinates point by point, and the `k` values, each element of `E` in its 24-byte encoding. -/

namespace PcsOpenGolf

/-! ### Polynomials -/

structure Poly where
  vars : Nat
  kind : Kind
  words : List K
  deriving DecidableEq

/-- The table has exactly the words its size and kind call for, and fits in `MAX_WORDS_LOG`. -/
def Poly.Valid (f : Poly) : Prop :=
  f.kind.Fits f.vars ∧ f.words.length = 2 ^ f.kind.wordsLog f.vars

instance (f : Poly) : Decidable f.Valid := by unfold Poly.Valid; infer_instance

/-- The value at the point of `{0,1}^vars` whose coordinate `j` is bit `j` of `i`. -/
def Poly.entry (f : Poly) (i : Nat) : K :=
  match f.kind with
  | .words => f.words.getD i 0
  | .bits => if (f.words.getD (i / 64) 0).getLsbD (i % 64) then 1 else 0

/-- `eq(b, p) = Π_j (b_j ? p_j : 1 + p_j)` for the point `b` with index `i`; `1 + p_j` is
`1 - p_j` in characteristic 2. -/
def eqWeight (p : List E) (i : Nat) : E :=
  (List.range p.length).foldl
    (fun acc j => acc * (if i.testBit j then p.getD j 0 else 1 + p.getD j 0)) 1

/-- The multilinear extension at `p`: `f(p) = Σ_b f(b) · eq(b, p)`. -/
def Poly.eval (f : Poly) (p : List E) : E :=
  (List.range (2 ^ f.vars)).foldl (fun acc i => acc + E.ofK (f.entry i) * eqWeight p i) 0

/-! ### Claims -/

structure Claim where
  root : Root
  vars : Nat
  kind : Kind
  points : List (List E)
  values : List E
  deriving DecidableEq

/-- The claim is true of `f`: same size and kind, a valid table, and every claimed value. -/
def Claim.HoldsFor (claim : Claim) (f : Poly) : Prop :=
  f.Valid ∧ f.vars = claim.vars ∧ f.kind = claim.kind ∧
    claim.points.length = claim.values.length ∧
    ∀ j < claim.points.length, f.eval (claim.points.getD j []) = claim.values.getD j 0

instance (claim : Claim) (f : Poly) : Decidable (claim.HoldsFor f) := by
  unfold Claim.HoldsFor; infer_instance

/-! ### Descriptors -/

/-- Root, `n`, kind and `k`, then five zero bytes. -/
def HEADER_BYTES : Nat := 40

/-- Bytes in a descriptor with `k` points in `n` variables. -/
def descriptorBytes (n k : Nat) : Nat := HEADER_BYTES + 24 * k * n + 24 * k

/-- The longest descriptor that can pass `Header.parse`: bits in `MAX_WORDS_LOG + 6` variables
at `MAX_POINTS` points. The opening verifier's descriptor buffer has this size. -/
def MAX_DESCRIPTOR_BYTES : Nat := descriptorBytes (MAX_WORDS_LOG + 6) MAX_POINTS

/-- What the header fixes before the points are read. -/
structure Header where
  root : Root
  vars : Nat
  kind : Kind
  count : Nat
  deriving DecidableEq

/-- Parse and check a header: a known kind, `1 ≤ k ≤ MAX_POINTS`, zero padding, and a size that
fits. -/
def Header.parse (bytes : List Byte) : Option Header := do
  let kind ← Kind.ofCode (bytes.getD 33 0).toNat
  let vars := (bytes.getD 32 0).toNat
  let count := (bytes.getD 34 0).toNat
  if 1 ≤ count ∧ count ≤ MAX_POINTS ∧ ((bytes.drop 35).take 5).all (· = 0) ∧ kind.Fits vars then
    some ⟨ofBytes 32 (bytes.take 32), vars, kind, count⟩
  else none

/-- Elements of `E` from consecutive 24-byte encodings. -/
def decodeElements (bytes : List Byte) (count : Nat) : List E :=
  (List.range count).map fun i => E.decode (ofBytes 24 ((bytes.drop (24 * i)).take 24))

/-- The claim whose descriptor is `bytes`, given its parsed header. -/
def Header.claim (header : Header) (bytes : List Byte) : Claim :=
  let body := bytes.drop HEADER_BYTES
  let coordinates := decodeElements body (header.count * header.vars)
  { root := header.root, vars := header.vars, kind := header.kind,
    points := (List.range header.count).map fun j =>
      (coordinates.drop (header.vars * j)).take header.vars,
    values := decodeElements (body.drop (24 * header.count * header.vars)) header.count }

/-- The descriptor of a claim, for provers and tests. -/
def Claim.descriptor (claim : Claim) : List Byte :=
  bytesOf claim.root ++ [BitVec.ofNat 8 claim.vars, BitVec.ofNat 8 claim.kind.code,
    BitVec.ofNat 8 claim.points.length, 0, 0, 0, 0, 0] ++
    (claim.points.flatten ++ claim.values).flatMap fun e => bytesOf e.encode

end PcsOpenGolf
