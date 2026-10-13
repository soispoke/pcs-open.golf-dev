import PcsOpenGolf.Polynomial
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! # Opening track: oracles

The opening track's hash `H` is sig.golf's: a random oracle on byte strings of one or more
64-byte blocks, each block charged as one compression. Natively it is unkeyed BLAKE2s-256 of the
whole input. Merkle hashing, Fiat-Shamir and any grinding all use it, so every hash anyone
computes counts toward the adversary's budget.

`Tables` records `H`'s answers in the order they were first given, which is what an extractor
reads, together with the lists the soundness game assigns to published roots and the public
polynomials it commits. VCVio's vocabulary is introduced in `PcsOpenGolf.Oracle`. -/

namespace PcsOpenGolf.Opening
open OracleComp OracleSpec

/-- Byte strings of one or more 64-byte blocks: `⟨n, bytes⟩` holds `n + 1` blocks, so the empty
input is unrepresentable. The length is part of the input. -/
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))

/-- Blocks in an input, each charged as one compression. -/
def Query.blocks (query : Query) : Nat := query.1 + 1

abbrev HashSpec : OracleSpec Query := Query →ₒ Bytes 32

/-- One particular function `H`, for statements that must hold for every `H`. -/
abbrev Hash := QueryImpl HashSpec Id

/-- Programming `H` on an input nobody has queried yet; only simulators get it. -/
abbrev ProgramSpec : OracleSpec (Query × Bytes 32) := (Query × Bytes 32) →ₒ Bool

/-- Private coins and `H`: queried as `.inl _` and `.inr _`. -/
abbrev World := unifSpec + HashSpec

structure Tables where
  /-- `H`'s answers, oldest first. -/
  hash : List (Query × Bytes 32) := []
  /-- Calls to `H` counted so far. -/
  calls : Nat := 0
  /-- The list each published root received when it was first published. -/
  published : List (Root × List Poly) := []
  /-- Public polynomials committed by the game, with their roots. -/
  publicRoots : List (Root × Poly) := []

abbrev Experiment := StateT Tables ProbComp

def coinImpl : QueryImpl unifSpec Experiment :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget Experiment

/-- A stored answer if the input has one, otherwise a fresh uniform answer, stored. -/
def hashImpl : QueryImpl HashSpec Experiment := fun input => do
  let tables ← get
  match tables.hash.lookup input with
  | some answer => return answer
  | none =>
    let answer ← liftM ($ᵗ Bytes 32 : ProbComp (Bytes 32))
    set { tables with hash := tables.hash ++ [(input, answer)] }
    return answer

def programImpl : QueryImpl ProgramSpec Experiment := fun (input, answer) => do
  let tables ← get
  match tables.hash.lookup input with
  | some _ => return false
  | none =>
    set { tables with hash := tables.hash ++ [(input, answer)] }
    return true

def worldImpl : QueryImpl World Experiment := coinImpl + hashImpl

def counted {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Experiment) :
    QueryImpl spec Experiment := fun query => do
  modify fun tables => { tables with calls := tables.calls + 1 }
  impl query

/-- Coins free; one unit per call to `H`, a repeated input included. -/
def countedWorldImpl : QueryImpl World Experiment := coinImpl + counted hashImpl

end PcsOpenGolf.Opening
