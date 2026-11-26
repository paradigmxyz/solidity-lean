import Lean

/-!
# Axiom audit

`#axiom_audit "out" "prefix"*` reports every theorem and definition declared in a module
whose name starts with one of the prefixes that depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` (`sorryAx` and `Lean.ofReduceBool` among them), and writes
the source path of every module the importing file's environment contains to `out`, for the
closure grep in `scripts/refinement/axiom-audit.sh`. Each declaration's axioms come from
`Lean.collectAxioms`, which reads an imported declaration's from the table its module's olean
records, so the sweep walks no bodies. `#print axioms` stays the authority on each headline
theorem; this sweep covers the rest of their modules.
-/

namespace SolidCore.Refinement.AxiomAudit

open Lean Elab Command

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#axiom_audit " out:str prefixes:str* : command => do
  let env ← getEnv
  let ps := prefixes.toList.map (·.getString)
  let mods := env.header.moduleNames
  let inScope (n : Name) : Bool := Id.run do
    let some i := env.getModuleIdxFor? n | return false
    return ps.any ((mods[i.toNat]!).toString.startsWith ·)
  let targets := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    if !n.isInternal && inScope n && (ci matches .thmInfo _ || ci matches .defnInfo _) then
      acc.push (n, ci matches .thmInfo _) else acc
  let mut bad : Nat := 0
  for (n, _) in targets do
    let extra := (← collectAxioms n).toList.filter (!allowed.contains ·)
    unless extra.isEmpty do
      bad := bad + 1
      logInfo m!"AXIOM-VIOLATION {n}: {extra}"
  let thms := (targets.filter (·.2)).size
  logInfo m!"axiom sweep: {targets.size} declarations ({thms} theorems) under {ps}, {bad} with axioms outside [propext, Classical.choice, Quot.sound]"
  let sp ← getSrcSearchPath
  let lines ← mods.mapM fun m => return s!"{m} {(← sp.findModuleWithExt "lean" m).getD "?"}"
  IO.FS.writeFile out.getString (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"closure: {mods.size} modules written to {out.getString}"

end SolidCore.Refinement.AxiomAudit
