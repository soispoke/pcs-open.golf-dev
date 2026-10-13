import PcsOpenGolf.Opening.Scheme

/-! # Opening track: security

The evaluation-soundness and zero-knowledge experiments.

**Evaluation soundness.** An adversary queries coins and `H`, and two game oracles. Publishing a
root runs the extractor on `H`'s answers so far; the list it returns is the one that root is held
to from then on, and a later publication of the same root changes nothing. Asking the game to
commit a public polynomial runs `commitPublic` and holds the resulting root to exactly that
polynomial. The adversary finally submits descriptors and opening proofs. It wins if some
extracted list is longer than `2 ^ L`, or if the verifier accepts a descriptor whose root is
public or published and whose claim holds for no polynomial in that root's list. Every call to
`H` in the experiment counts toward `Q`: the adversary's, `commitPublic`'s and the verifier's.

**Zero knowledge.** A distinguisher queries coins, `H` and an opening oracle that takes a
polynomial and points and answers `none` unless they are valid. In the real world the oracle
commits and opens honestly; in the ideal world it runs the simulator on the claim's size, kind,
points and values alone. Only the distinguisher's own calls count. Each call to the opening
oracle commits afresh, so every root is opened once, which is all the app track allows. -/

namespace PcsOpenGolf.Opening
open OracleComp OracleSpec

/-! ### Evaluation soundness -/

/-- Publish a root. -/
abbrev PublishSpec : OracleSpec Root := Root →ₒ Unit

/-- Have the game commit a public polynomial deterministically. -/
abbrev PublicSpec : OracleSpec Poly := Poly →ₒ Root

/-- Queries coins as `.inl (.inl (.inl _))`, `H` as `.inl (.inl (.inr _))`, publication as
`.inl (.inr _)` and public commitments as `.inr _`, then submits descriptors and opening
proofs. -/
abbrev Adversary := OracleComp (World + PublishSpec + PublicSpec) (List (List Byte × List Byte))

/-- The list a root is held to: exactly its polynomial for a public root, otherwise the list it
received when first published. -/
def Tables.listFor (tables : Tables) (root : Root) : Option (List Poly) :=
  match tables.publicRoots.lookup root with
  | some f => some [f]
  | none => tables.published.lookup root

/-- A submitted descriptor and opening proof, with the verifier's run on them. -/
structure Attempt where
  descriptor : List Byte
  proof : List Byte
  result : Machine.Execution

namespace Scheme

def publishImpl (scheme : Scheme) : QueryImpl PublishSpec Experiment := fun root => do
  let tables ← get
  if (tables.published.lookup root).isNone then
    set { tables with published := tables.published ++ [(root, scheme.extractor tables.hash root)] }

def publicImpl (scheme : Scheme) : QueryImpl PublicSpec Experiment := fun f => do
  let (root, _) ← simulateQ (counted hashImpl) (scheme.commitPublic f)
  modify fun tables => { tables with publicRoots := tables.publicRoots ++ [(root, f)] }
  return root

/-- The adversary with fresh, counted oracles, then the verifier on each submission. -/
def soundnessExperiment (scheme : Scheme) (adversary : Adversary) :
    ProbComp (List Attempt × Tables) :=
  (do
    let submitted ← simulateQ (countedWorldImpl + scheme.publishImpl + scheme.publicImpl) adversary
    submitted.mapM fun (descriptor, proof) => do
      let result ← simulateQ (counted hashImpl)
        (Machine.verify scheme.image scheme.layout descriptor proof)
      return (⟨descriptor, proof, result⟩ : Attempt)).run {}

/-- The verifier accepted a well-formed submission that fits its buffers, about a public or
published root, whose claim holds for no polynomial in the root's list. -/
def AcceptsFalseClaim (tables : Tables) (attempt : Attempt) : Prop :=
  attempt.descriptor.length ≤ MAX_DESCRIPTOR_BYTES ∧
    attempt.proof.length ≤ MAX_OPENING_BYTES ∧ attempt.result.exit = .success ∧
    ∃ header, Header.parse attempt.descriptor = some header ∧
      ∃ list, tables.listFor header.root = some list ∧
        ∀ g ∈ list, ¬ (header.claim attempt.descriptor).HoldsFor g

/-- An extracted list longer than `2 ^ L`, or an accepted false claim. -/
def Wins (L : Nat) : List Attempt × Tables → Prop
  | (attempts, tables) =>
    (∃ entry ∈ tables.published, 2 ^ L < entry.2.length) ∨
      ∃ attempt ∈ attempts, AcceptsFalseClaim tables attempt

end Scheme

/-! ### Zero knowledge -/

/-- Commit to a polynomial and open it at points: a root and an opening proof, or `none` when
the polynomial or the points are invalid. -/
abbrev OpenSpec : OracleSpec (Poly × List (List E)) :=
  (Poly × List (List E)) →ₒ Option (Root × List Byte)

abbrev Distinguisher := OracleComp (World + OpenSpec) Bool

namespace Scheme

/-- The real opening oracle: hiding commitment, then the honest opening of the true claim. -/
def realOpen (scheme : Scheme) : QueryImpl OpenSpec Experiment := fun (f, points) =>
  if f.Valid ∧ PointsFor f points then
    some <$> simulateQ worldImpl (do
      let (root, state) ← scheme.commit f
      let proof ← scheme.prove f state (trueClaim root f points)
      return (root, proof))
  else pure none

/-- The ideal opening oracle: the simulator, which sees the size, kind, points and values. -/
def simulatedOpen (scheme : Scheme) : QueryImpl OpenSpec Experiment := fun (f, points) =>
  if f.Valid ∧ PointsFor f points then
    some <$> simulateQ (worldImpl + programImpl)
      (scheme.simulator ⟨f.vars, f.kind, points, points.map f.eval⟩)
  else pure none

end Scheme

/-- The distinguisher against the given opening oracle; only its own calls count. -/
def zkExperiment (distinguisher : Distinguisher) (opening : QueryImpl OpenSpec Experiment) :
    ProbComp (Bool × Tables) :=
  (simulateQ (countedWorldImpl + counted opening) distinguisher).run {}

end PcsOpenGolf.Opening
