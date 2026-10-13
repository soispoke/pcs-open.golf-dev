import PcsOpenGolf.Machine
import PcsOpenGolf.Relation

/-! # Submissions

What an app entry consists of, the setup that commits its fixed polynomials, and the honest
experiment: setup, the honest prover on a statement and witness, then the verifier on the proof.
The run succeeds when the verifier accepts and every claim it made is true of the committed
polynomials. -/

namespace PcsOpenGolf
open OracleComp OracleSpec

/-- The numbers a certificate proves: `B` proof bytes, `N` claims and at most `C₀` cycles outside
them on an honest proof, and `M`, the claims on roots taken from the proof rather than from the
fixed roots. The score is `B × (C₀ + N × CLAIM_CYCLES)`; the price `CLAIM_CYCLES` is published
separately and never enters a certificate. -/
structure Claimed where
  proofBytes : Nat
  claims : Nat
  cycles : Nat
  proofRoots : Nat

/-- An app entry.

* `image` and `layout`: the verifier program and where it finds `x` and the fixed roots.
* `fixed`: the public polynomials the verifier relies on, committed by setup in this order.
* `prover`: the honest prover, given the fixed roots, `x` and `w`. It may use coins, `T` and
  `COMMIT`.
* `extractor`: given `x`, an accepted proof and everything the oracles remember, including every
  committed polynomial, returns a witness.
* `simulator`: given the fixed roots and `x` only, returns a proof. It may also program `T` on
  inputs nobody has queried yet. -/
structure Submission where
  proofBytes : Nat
  image : Rv64.Image
  layout : Machine.Layout
  fixed : List Poly
  prover : List Root → PublicInput → Witness → OracleComp World (Bytes proofBytes)
  extractor : PublicInput → Bytes proofBytes → Tables → Witness
  simulator : List Root → PublicInput → OracleComp (World + ProgramSpec) (Bytes proofBytes)

namespace Submission

/-- Commit each fixed polynomial, in order. -/
def setup (submission : Submission) : OracleComp World (List Root) :=
  submission.fixed.mapM fun f => query (spec := World) (.inr f)

/-- The verifier on proof bytes `proof`; it is given exactly `B` of them. -/
def verify (submission : Submission) (fixedRoots : List Root) (x : PublicInput)
    (proof : Bytes submission.proofBytes) : OracleComp HashSpec Machine.Execution :=
  Machine.verify submission.image submission.layout fixedRoots x (bytesOf proof)

end Submission

/-- The verifier accepted, and every claim it made is true of the committed polynomials. -/
def Succeeded (result : Machine.Execution) (tables : Tables) : Prop :=
  result.exit = .success ∧ ∀ claim ∈ result.claims, claim.Holds tables

instance (result : Machine.Execution) (tables : Tables) : Decidable (Succeeded result tables) := by
  unfold Succeeded; infer_instance

namespace Submission

/-- The honest experiment: setup, the prover on `(x, w)`, then the verifier on its proof. -/
def honest (submission : Submission) (x : PublicInput) (w : Witness) :
    OracleComp World Machine.Execution := do
  let fixedRoots ← submission.setup
  let proof ← submission.prover fixedRoots x w
  liftM (submission.verify fixedRoots x proof)

/-- The honest experiment with fresh oracles, returning the run and what the oracles remember. -/
def completenessExperiment (submission : Submission) (x : PublicInput) (w : Witness) :
    ProbComp (Machine.Execution × Tables) :=
  (simulateQ worldImpl (submission.honest x w)).run {}

end Submission

end PcsOpenGolf
