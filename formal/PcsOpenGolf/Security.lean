import PcsOpenGolf.Submission

/-! # Security

The knowledge-soundness and zero-knowledge experiments.

**Knowledge soundness.** An adversary receives the fixed roots, queries coins, `T` and `COMMIT`,
and submits a public input and a proof, or gives up. It wins if the verifier accepts, every claim
is true, and either the extractor fails to return a valid witness or the run claimed more than
`M` roots that are not fixed roots. Every call to `T` and `COMMIT` in the experiment counts toward
the budget `Q`: setup, the adversary's and the verifier's.

**Zero knowledge.** A distinguisher receives the fixed roots and queries coins, `T`, `COMMIT` and
a proving oracle that takes `(x, w)` and answers `none` unless `R(x, w)`. In the real world the
proving oracle runs the honest prover; in the ideal world it runs the simulator on `x` alone,
which may program `T` on inputs nobody has queried. Only the distinguisher's own calls count
toward `Q`, one per call to `T`, `COMMIT` or the proving oracle, so the count does not depend on
which world it is in.

The adversary and the distinguisher are `OracleComp`s: computations that make finitely many
queries and then answer. A strategy that could run for ever is represented by its truncations,
so a bound over all of them bounds every adaptive strategy. Local computation is unrestricted;
only oracle answers and coins reveal information. -/

namespace PcsOpenGolf
open OracleComp OracleSpec

/-! ### Knowledge soundness -/

/-- Given the fixed roots, submit a public input and a proof, or give up with `none`. -/
abbrev Adversary (B : Nat) := List Root → OracleComp World (Option (PublicInput × Bytes B))

/-- A submitted proof and the verifier's run on it. -/
structure Attempt (B : Nat) where
  fixedRoots : List Root
  x : PublicInput
  proof : Bytes B
  result : Machine.Execution

/-- Claims whose root is not one of the fixed roots. -/
def proofRootClaims (fixedRoots : List Root) (claims : List Claim) : Nat :=
  (claims.filter fun claim => claim.root ∉ fixedRoots).length

namespace Submission

/-- Setup, the adversary, then the verifier on what it submits. -/
def soundnessGame (submission : Submission) (adversary : Adversary submission.proofBytes) :
    OracleComp World (Option (Attempt submission.proofBytes)) := do
  let fixedRoots ← submission.setup
  let some (x, proof) ← adversary fixedRoots | return none
  let result ← liftM (submission.verify fixedRoots x proof)
  return some ⟨fixedRoots, x, proof, result⟩

/-- The game with fresh, counted oracles. -/
def soundnessExperiment (submission : Submission) (adversary : Adversary submission.proofBytes) :
    ProbComp (Option (Attempt submission.proofBytes) × Tables) :=
  (simulateQ countedWorldImpl (submission.soundnessGame adversary)).run {}

/-- The adversary won: an accepted run with true claims, and either more than `M` claims on
proof roots or an extracted witness that fails `R`. -/
def Wins (submission : Submission) (M : Nat) :
    Option (Attempt submission.proofBytes) × Tables → Prop
  | (none, _) => False
  | (some attempt, tables) =>
    Succeeded attempt.result tables ∧
      (M < proofRootClaims attempt.fixedRoots attempt.result.claims ∨
        ¬ Relation attempt.x (submission.extractor attempt.x attempt.proof tables))

end Submission

/-! ### Zero knowledge -/

/-- The proving oracle: `(x, w)` to a proof, or `none` when `R(x, w)` fails. -/
abbrev ProveSpec (B : Nat) : OracleSpec (PublicInput × Witness) :=
  (PublicInput × Witness) →ₒ Option (Bytes B)

/-- Given the fixed roots, query coins, `T`, `COMMIT` and the proving oracle, then guess. -/
abbrev Distinguisher (B : Nat) := List Root → OracleComp (World + ProveSpec B) Bool

namespace Submission

/-- The real proving oracle: the honest prover. -/
def realProve (submission : Submission) (fixedRoots : List Root) :
    QueryImpl (ProveSpec submission.proofBytes) Experiment := fun (x, w) =>
  if Relation x w then some <$> simulateQ worldImpl (submission.prover fixedRoots x w)
  else pure none

/-- The ideal proving oracle: the simulator, which sees `x` but not `w`. -/
def simulatedProve (submission : Submission) (fixedRoots : List Root) :
    QueryImpl (ProveSpec submission.proofBytes) Experiment := fun (x, w) =>
  if Relation x w then some <$> simulateQ (worldImpl + programImpl) (submission.simulator fixedRoots x)
  else pure none

/-- Setup, then the distinguisher against the given proving oracle; only its own calls count. -/
def zkExperiment (submission : Submission) (distinguisher : Distinguisher submission.proofBytes)
    (prove : List Root → QueryImpl (ProveSpec submission.proofBytes) Experiment) :
    ProbComp (Bool × Tables) :=
  (do
    let fixedRoots ← simulateQ worldImpl submission.setup
    simulateQ (countedWorldImpl + counted (prove fixedRoots)) (distinguisher fixedRoots)).run {}

end Submission

end PcsOpenGolf
