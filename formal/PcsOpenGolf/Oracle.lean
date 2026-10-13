import PcsOpenGolf.Polynomial
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! # Oracles

The app track's two oracles and how every experiment answers them.

* `T`, the transcript hash, maps any byte string to 32 bytes. Natively it is Keccak-256; here it
  is a lazy random oracle, so each new input gets an independent uniform answer.
* `COMMIT`, the ideal `PCS_open` commitment, takes a polynomial and returns a fresh uniform root,
  remembering which polynomial it belongs to. A root therefore reveals nothing about its
  polynomial, and a claim on it is true or false according to the first polynomial committed
  under it. Committing the same polynomial twice gives two unrelated roots, as a hiding
  commitment does.

Both answer from one table, `Tables`, which also counts calls where an experiment says so.

VCVio vocabulary used here and below. An `OracleComp spec α` is a computation that may query
the oracles in `spec`; `A →ₒ B` specifies one oracle from `A` to `B`, and `spec₁ + spec₂`
offers both, a query being tagged `.inl` or `.inr`. `unifSpec` is the coin oracle and `ProbComp`
is `OracleComp unifSpec`. A `QueryImpl spec m` answers each query of `spec` by a computation in
the monad `m`; for `m = Id` it is just a function from queries to answers. `simulateQ impl c`
runs `c` with every query answered by `impl`, and `evalWithAnswerFn f c` does so for a plain
function `f`. `liftM` embeds a computation over fewer oracles into one over more. Two notations:
`$ᵗ T` draws a uniform element of `T`; `Pr[p | c]` is the probability that `c` returns a
value satisfying `p`. -/

namespace PcsOpenGolf
open OracleComp OracleSpec

/-- `T`: byte strings of any length to 32 bytes. The length is part of the input. -/
abbrev HashSpec : OracleSpec (List Byte) := List Byte →ₒ Bytes 32

/-- `COMMIT`: a polynomial to its root. -/
abbrev CommitSpec : OracleSpec Poly := Poly →ₒ Root

/-- Programming `T`: set its answer on an input nobody has queried yet. The answer is `true` when
the input was new and is now set, `false` when it already had an answer, which stays. Only
zero-knowledge simulators get this oracle. -/
abbrev ProgramSpec : OracleSpec (List Byte × Bytes 32) := (List Byte × Bytes 32) →ₒ Bool

/-- Private coins, `T` and `COMMIT`. An entrant's computation queries coins as `.inl (.inl _)`,
`T` as `.inl (.inr _)` and `COMMIT` as `.inr _`. -/
abbrev World := unifSpec + HashSpec + CommitSpec

/-- One particular function `T`, for statements that must hold for every `T`. -/
abbrev Hash := QueryImpl HashSpec Id

/-- Everything the oracles remember: `T`'s answers, the commitments in order, and a call count. -/
structure Tables where
  hash : List (List Byte × Bytes 32) := []
  commits : List (Root × Poly) := []
  calls : Nat := 0

/-- The polynomial behind a root: the first one committed under it. -/
def Tables.committed (tables : Tables) (root : Root) : Option Poly := tables.commits.lookup root

/-- A claim is true when its root was committed and the claim holds for that polynomial. -/
def Claim.Holds (claim : Claim) (tables : Tables) : Prop :=
  ∃ f, tables.committed claim.root = some f ∧ claim.HoldsFor f

instance (claim : Claim) (tables : Tables) : Decidable (claim.Holds tables) :=
  match h : tables.committed claim.root with
  | some f =>
    if hf : claim.HoldsFor f then isTrue ⟨f, h, hf⟩
    else isFalse fun ⟨g, hg, hg'⟩ => hf (by rw [h] at hg; cases hg; exact hg')
  | none => isFalse fun ⟨g, hg, _⟩ => by rw [h] at hg; cases hg

/-- Every experiment runs in this monad: coins, plus the tables as state. -/
abbrev Experiment := StateT Tables ProbComp

/-! ### Answering queries -/

/-- Coins pass through and leave the tables alone. -/
def coinImpl : QueryImpl unifSpec Experiment :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget Experiment

/-- A stored answer if the input has one, otherwise a fresh uniform answer, stored. -/
def hashImpl : QueryImpl HashSpec Experiment := fun input => do
  let tables ← get
  match tables.hash.lookup input with
  | some answer => return answer
  | none =>
    let answer ← liftM ($ᵗ Bytes 32 : ProbComp (Bytes 32))
    set { tables with hash := (input, answer) :: tables.hash }
    return answer

/-- A fresh uniform root, recorded with the polynomial. -/
def commitImpl : QueryImpl CommitSpec Experiment := fun f => do
  let root ← liftM ($ᵗ Root : ProbComp Root)
  modify fun tables => { tables with commits := tables.commits ++ [(root, f)] }
  return root

def programImpl : QueryImpl ProgramSpec Experiment := fun (input, answer) => do
  let tables ← get
  match tables.hash.lookup input with
  | some _ => return false
  | none =>
    set { tables with hash := (input, answer) :: tables.hash }
    return true

/-- Coins, `T` and `COMMIT`, uncounted. -/
def worldImpl : QueryImpl World Experiment := coinImpl + hashImpl + commitImpl

/-- Add one to the call count, then answer as `impl` does. -/
def counted {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Experiment) :
    QueryImpl spec Experiment := fun query => do
  modify fun tables => { tables with calls := tables.calls + 1 }
  impl query

/-- Coins free; one unit per call to `T` or `COMMIT`, a repeated `T` input included. -/
def countedWorldImpl : QueryImpl World Experiment :=
  coinImpl + counted hashImpl + counted commitImpl

end PcsOpenGolf
