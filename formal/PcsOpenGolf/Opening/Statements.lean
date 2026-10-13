import PcsOpenGolf.Opening.Security

/-! # Opening track: statements

The seven statements an opening certificate proves, in the order `docs/rules-opening.md` lists
them, and the certificate itself. -/

namespace PcsOpenGolf.Opening
open OracleComp OracleComp.EvalDist

namespace Scheme

/-- **Admission.** The image is within the size limit with aligned, nonoverlapping input buffers
below its data; `S` fits in the proof buffer; `L ≤ LIST_BITS`. -/
def Admission (scheme : Scheme) (claimed : Claimed) : Prop :=
  Machine.ImageValid scheme.image scheme.layout ∧ claimed.openingBytes ≤ MAX_OPENING_BYTES ∧
    claimed.listBits ≤ LIST_BITS

instance (scheme : Scheme) (claimed : Claimed) : Decidable (scheme.Admission claimed) := by
  unfold Admission; infer_instance

/-- **Completeness.** For every valid polynomial of either kind and every size, every admitted
set of points, and both commitments, the honest opening of the true claim is accepted with
probability at least `1 - FAILURE`. -/
def Completeness (scheme : Scheme) : Prop :=
  ∀ f points isPublic, f.Valid → PointsFor f points →
    1 - FAILURE ≤ Pr[fun (outcome, _) => outcome.2.exit = .success |
      scheme.completenessExperiment f points isPublic]

/-- **Cost.** On the scored instance, a hiding commitment to a bit polynomial in `SCORED_VARS`
variables opened at `SCORED_POINTS` points, no honest run has an opening above `S` bytes or a
verification above `C` cycles, receiving charge included, whatever `H` and the coins are. -/
def Cost (scheme : Scheme) (S C : Nat) : Prop :=
  ∀ f points, f.Valid → f.kind = .bits → f.vars = SCORED_VARS → PointsFor f points →
    points.length = SCORED_POINTS →
    Pr[fun ((proof, result), _) => ¬ (proof.length ≤ S ∧ result.cycles ≤ C) |
      scheme.completenessExperiment f points false] = 0

/-- **Opening size.** Every honest opening, of every supported size, kind and point count and
for both commitments, fits in `MAX_OPENING_BYTES`. -/
def OpeningSize (scheme : Scheme) : Prop :=
  ∀ f points isPublic, f.Valid → PointsFor f points →
    Pr[fun ((proof, _), _) => MAX_OPENING_BYTES < proof.length |
      scheme.completenessExperiment f points isPublic] = 0

/-- **Evaluation soundness** with lists of at most `2 ^ L` polynomials. No bound on the
adversary's computation or private randomness; only calls to `H` count. -/
def Soundness (scheme : Scheme) (L : Nat) : Prop :=
  ∀ (adversary : Adversary) (Q : Nat), 1 ≤ Q →
    Pr[fun outcome => Wins L outcome ∧ outcome.2.calls ≤ Q |
      scheme.soundnessExperiment adversary] ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

/-- **Zero knowledge.** A distinguisher making at most `Q` calls tells real openings from
simulated ones with advantage at most `Q / 2 ^ ZK_BITS`, in either direction. -/
def ZeroKnowledge (scheme : Scheme) : Prop :=
  ∀ (distinguisher : Distinguisher) (Q : Nat),
    let real := Pr[fun (guess, tables) => guess = true ∧ tables.calls ≤ Q |
      zkExperiment distinguisher scheme.realOpen]
    let ideal := Pr[fun (guess, tables) => guess = true ∧ tables.calls ≤ Q |
      zkExperiment distinguisher scheme.simulatedOpen]
    real ≤ ideal + (Q : ENNReal) / 2 ^ ZK_BITS ∧ ideal ≤ real + (Q : ENNReal) / 2 ^ ZK_BITS

/-- **Termination.** For every function `H` and all inputs that fit their buffers, the verifier
finishes in fewer than `OPENING_CYCLE_LIMIT` cycles, and in at most `4 × C` when the descriptor
is well formed, so a bad opening costs a node at most four times a good one. -/
def Termination (scheme : Scheme) (C : Nat) : Prop :=
  ∀ (hash : Hash) (descriptor proof : List Byte),
    descriptor.length ≤ MAX_DESCRIPTOR_BYTES → proof.length ≤ MAX_OPENING_BYTES →
    let result := evalWithAnswerFn hash
      (Machine.verify scheme.image scheme.layout descriptor proof)
    result.exit ≠ .unfinished ∧ result.cycles < OPENING_CYCLE_LIMIT ∧
      ((Header.parse descriptor).isSome → result.cycles ≤ 4 * C)

end Scheme

/-- The score is `S × C` for the claimed numbers. -/
structure Certificate (scheme : Scheme) (claimed : Claimed) : Prop where
  admission : scheme.Admission claimed
  completeness : scheme.Completeness
  cost : scheme.Cost claimed.openingBytes claimed.cycles
  openingSize : scheme.OpeningSize
  soundness : scheme.Soundness claimed.listBits
  zeroKnowledge : scheme.ZeroKnowledge
  termination : scheme.Termination claimed.cycles

end PcsOpenGolf.Opening
