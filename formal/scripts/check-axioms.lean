/-
Audit of the protected contract: every declaration in a protected module may depend only on
`propext`, `Classical.choice` and `Quot.sound`, and no protected module may declare an axiom.
Rendered challenge stubs are excluded, since they hold the `sorry` placeholders entries fill.

    lake env lean scripts/check-axioms.lean
-/
import Lean
import PcsOpenGolf.Statements
import PcsOpenGolf.Opening.Statements

open Lean

def whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Protected modules: the contract library, without the rendered challenge stubs. -/
def protectedModule (m : Name) : Bool :=
  (`PcsOpenGolf).isPrefixOf m && !(`PcsOpenGolf.Challenge).isPrefixOf m

open Elab.Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut decls : Array Name := #[]
  let mut declared : Array (Name × Name) := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let m := mods[idx.toNat]!
      if protectedModule m then
        if ci.isAxiom then declared := declared.push (name, m)
        unless name.isInternal do decls := decls.push name
  for (n, m) in declared do
    IO.eprintln s!"::error::axiom declaration `{n}` in protected module `{m}`"
  let mut failed := !declared.isEmpty
  for decl in decls do
    let axioms ← collectAxioms decl
    for ax in axioms.toList.filter (fun a => !whitelist.contains a) do
      failed := true
      IO.eprintln s!"::error::contract declaration `{decl}` depends on `{ax}`"
  if failed then throwError "the contract declares or depends on non-whitelisted axioms"
  IO.println s!"ok: {decls.size} contract declarations use only propext, Classical.choice and Quot.sound, and no protected module declares an axiom"
