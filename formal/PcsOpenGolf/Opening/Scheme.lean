import PcsOpenGolf.Opening.Machine

/-! # Opening track: schemes

What an opening entry consists of, and the honest experiment: commit to a polynomial, either
hiding or, for a public polynomial, deterministically; make the true claim at some points; open
it; and run the verifier on the claim's descriptor and the opening proof. -/

namespace PcsOpenGolf.Opening
open OracleComp OracleSpec

/-- The numbers a certificate proves: `S`, the largest honest opening in bytes on the scored
instance; `C`, the most cycles the verifier spends on it; and `L`, the list size in bits for
which evaluation soundness holds. The score is `S × C`. -/
structure Claimed where
  openingBytes : Nat
  cycles : Nat
  listBits : Nat

/-- A claim without its root: everything a zero-knowledge simulator sees. -/
structure Request where
  vars : Nat
  kind : Kind
  points : List (List E)
  values : List E

/-- An opening entry.

* `commit`: the hiding commitment, from a polynomial and coins to a root and the prover's
  private opening state.
* `commitPublic`: the deterministic commitment setup uses for public polynomials.
* `prove`: the opening proof for a claim, from the polynomial and its opening state.
* `image` and `layout`: the verifier program and where it finds the descriptor and the proof.
* `extractor`: given `H`'s answers so far, oldest first, and a root being published, a list of
  polynomials that root is held to.
* `simulator`: given only the request, a root and an opening proof. It may program `H` on
  inputs nobody has queried yet. -/
structure Scheme where
  commit : Poly → OracleComp World (Root × List Byte)
  commitPublic : Poly → OracleComp HashSpec (Root × List Byte)
  prove : Poly → List Byte → Claim → OracleComp World (List Byte)
  image : Rv64.Image
  layout : Machine.Layout
  extractor : List (Query × Bytes 32) → Root → List Poly
  simulator : Request → OracleComp (World + ProgramSpec) (Root × List Byte)

/-- Points a claim on `f` may have: between one and `MAX_POINTS`, each with `f.vars`
coordinates. -/
def PointsFor (f : Poly) (points : List (List E)) : Prop :=
  1 ≤ points.length ∧ points.length ≤ MAX_POINTS ∧ ∀ p ∈ points, p.length = f.vars

instance (f : Poly) (points : List (List E)) : Decidable (PointsFor f points) := by
  unfold PointsFor; infer_instance

/-- The true claim about `f` at `points`, under `root`. -/
def trueClaim (root : Root) (f : Poly) (points : List (List E)) : Claim :=
  ⟨root, f.vars, f.kind, points, points.map f.eval⟩

namespace Scheme

/-- Commit (deterministically when `isPublic`), open the true claim at `points`, and verify.
Returns the opening proof and the verifier's run. -/
def honest (scheme : Scheme) (f : Poly) (points : List (List E)) (isPublic : Bool) :
    OracleComp World (List Byte × Machine.Execution) := do
  let (root, state) ← if isPublic then liftM (scheme.commitPublic f) else scheme.commit f
  let claim := trueClaim root f points
  let proof ← scheme.prove f state claim
  let result ← liftM (Machine.verify scheme.image scheme.layout claim.descriptor proof)
  return (proof, result)

/-- The honest experiment with fresh oracles. -/
def completenessExperiment (scheme : Scheme) (f : Poly) (points : List (List E))
    (isPublic : Bool) : ProbComp ((List Byte × Machine.Execution) × Tables) :=
  (simulateQ worldImpl (scheme.honest f points isPublic)).run {}

end Scheme

end PcsOpenGolf.Opening
