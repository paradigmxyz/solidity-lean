import Lean
import Verify.SourceText.TestRuns
import Verify.SourceText.Instances.Flag

/-!
# The production closure's axioms, with Flag's instance

Every constant of every `Verify.SourceText` module in this file's import closure, and of this
file, through `Lean.collectAxioms` (the full dependency walk, not selected names). The run fails
unless the union is within Lean's three axioms (no `sorryAx`, no `Lean.ofReduceBool`, no
native_decide axiom, no declared axiom), and unless no `Verify.SourceText.Diagnostics` module (a name
reserved for native or other diagnostic witnesses, outside this policy) is imported. `check.sh` runs it as is, with Flag's instance (`AuditFlag.lean`), and with tampered copies
that must fail.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames
  for m in mods do
    if (`Verify.SourceText.Diagnostics).isPrefixOf m then
      throwError "diagnostic module {m} in the production closure"
  let mut n : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array (Name × Name) := #[]
  for (c, _) in env.constants.toList do
    let inScope := match env.getModuleIdxFor? c with
      | some i => (`Verify.SourceText).isPrefixOf mods[i.toNat]!
      | none => true
    if !inScope then continue
    n := n + 1
    for a in (← collectAxioms c) do
      used := used.insert a
      if !allowed.contains a then bad := bad.push (c, a)
  let mods' := (mods.filter fun m => (`Verify.SourceText).isPrefixOf m).toList
  logInfo m!"modules: {mods'}"
  logInfo m!"constants audited: {n}; axioms used: {used.toList}"
  unless bad.isEmpty do
    throwError "not allowed: {bad.toList.take 10}"
