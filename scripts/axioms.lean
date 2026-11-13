import PBRExclusion
import Lean

/-!
This script checks every theorem of the library. Run it from the repository's root after
`lake build`, with this command.

    lake env lean scripts/axioms.lean

It fails if a theorem depends on an axiom other than the three that Lean and Mathlib use
throughout (`propext`, `Classical.choice` and `Quot.sound`). A `sorry` would show up here as the
axiom `sorryAx`.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let ours (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => (`PBRExclusion).isPrefixOf modNames[i.toNat]!
    | none => false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let theorems : Array Name := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ => if ours n && !n.isInternal then acc.push n else acc
    | _ => acc
  let mut bad : Array (Name × Name) := #[]
  let mut inResults := 0
  for n in theorems do
    if (`PBRExclusion.Results).isPrefixOf n then inResults := inResults + 1
    for a in (← liftCoreM (collectAxioms n)) do
      unless allowed.contains a do bad := bad.push (n, a)
  for (n, a) in bad do
    logError m!"{n} depends on the axiom {a}"
  unless bad.isEmpty do throwError "{bad.size} dependencies on other axioms"
  IO.println s!"{theorems.size} theorems checked, {inResults} of them in PBRExclusion.Results."
  IO.println "Each depends on no axiom other than propext, Classical.choice and Quot.sound."
