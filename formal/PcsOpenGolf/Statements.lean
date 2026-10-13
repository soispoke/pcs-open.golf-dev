import PcsOpenGolf.Security

/-! # Statements

The six statements an app certificate proves, in the order `docs/rules-app.md` lists them, and
the certificate itself. Probabilities live in `ENNReal`, the nonnegative reals with infinity. -/

namespace PcsOpenGolf
open OracleComp OracleComp.EvalDist

namespace Submission

/-- **Admission.** The declared proof size matches the prover's and fits, the claim count fits,
the image is within the size limit with aligned, nonoverlapping input buffers below its data,
and every fixed polynomial is valid. -/
def Admission (submission : Submission) (claimed : Claimed) : Prop :=
  submission.proofBytes = claimed.proofBytes ∧ claimed.proofBytes ≤ MAX_PROOF_BYTES ∧
    claimed.claims ≤ MAX_CLAIMS ∧
    Machine.ImageValid submission.image submission.layout submission.fixed.length ∧
    ∀ f ∈ submission.fixed, f.Valid

instance (submission : Submission) (claimed : Claimed) :
    Decidable (submission.Admission claimed) := by
  unfold Admission; infer_instance

/-- **Completeness.** For every statement and witness in `R`, the honest run succeeds with
probability at least `1 - FAILURE` over the oracles and the prover's coins. -/
def Completeness (submission : Submission) : Prop :=
  ∀ x w, Relation x w →
    1 - FAILURE ≤ Pr[fun (result, tables) => Succeeded result tables |
      submission.completenessExperiment x w]

/-- **Cost.** Every successful honest run makes exactly `N` claims and spends at most `C₀`
cycles outside them. Claims are on distinct roots because `CLAIM` faults on a repeated root. -/
def Cost (submission : Submission) (N C₀ : Nat) : Prop :=
  ∀ x w, Relation x w →
    Pr[fun (result, tables) => Succeeded result tables ∧
        ¬ (result.claims.length = N ∧ result.cycles ≤ C₀) |
      submission.completenessExperiment x w] = 0

/-- **Knowledge soundness.** No bound on the adversary's computation or private randomness; only
calls to `T` and `COMMIT` count. The margin of `LIST_BITS` per proof root pays for a real
commitment binding a root only to a list (`docs/rules-app.md`, "Knowledge soundness"). -/
def KnowledgeSoundness (submission : Submission) (M : Nat) : Prop :=
  ∀ (adversary : Adversary submission.proofBytes) (Q : Nat), 1 ≤ Q →
    Pr[fun outcome => submission.Wins M outcome ∧ outcome.2.calls ≤ Q |
      submission.soundnessExperiment adversary]
      ≤ (Q : ENNReal) / 2 ^ (SECURITY_BITS + LIST_BITS * M)

/-- **Zero knowledge.** A distinguisher making at most `Q` calls tells the real proving oracle
from the simulator with advantage at most `Q / 2 ^ ZK_BITS`, in either direction. -/
def ZeroKnowledge (submission : Submission) : Prop :=
  ∀ (distinguisher : Distinguisher submission.proofBytes) (Q : Nat),
    let real := Pr[fun (guess, tables) => guess = true ∧ tables.calls ≤ Q |
      submission.zkExperiment distinguisher submission.realProve]
    let ideal := Pr[fun (guess, tables) => guess = true ∧ tables.calls ≤ Q |
      submission.zkExperiment distinguisher submission.simulatedProve]
    real ≤ ideal + (Q : ENNReal) / 2 ^ ZK_BITS ∧ ideal ≤ real + (Q : ENNReal) / 2 ^ ZK_BITS

/-- **Termination.** For every function `T`, every list of fixed roots of the declared length,
every public input and every proof, the verifier finishes in fewer than `CYCLE_LIMIT` cycles. -/
def Termination (submission : Submission) : Prop :=
  ∀ (hash : Hash) (fixedRoots : List Root) (x : PublicInput) (proof : Bytes submission.proofBytes),
    fixedRoots.length = submission.fixed.length →
    let result := evalWithAnswerFn hash (submission.verify fixedRoots x proof)
    result.exit ≠ .unfinished ∧ result.cycles < CYCLE_LIMIT

end Submission

/-- The score is `B × (C₀ + N × CLAIM_CYCLES)` for the claimed numbers, with `CLAIM_CYCLES` from
the published parameter set. -/
structure Certificate (submission : Submission) (claimed : Claimed) : Prop where
  admission : submission.Admission claimed
  completeness : submission.Completeness
  cost : submission.Cost claimed.claims claimed.cycles
  knowledgeSoundness : submission.KnowledgeSoundness claimed.proofRoots
  zeroKnowledge : submission.ZeroKnowledge
  termination : submission.Termination

end PcsOpenGolf
