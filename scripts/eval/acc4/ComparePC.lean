import Lean
open Lean
/-! Compare each original generated run theorem with its bench copy: statement and proof value. -/
unsafe def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := ["Evm1", "Evm2", "Evm3", "Evm4", "Evm5", "Sched"]
  let imps := mods.flatMap fun m => [{ module := ("flag_4ce5cf9a.Proofs.Runs." ++ m).toName : Import }, { module := ("PerPC.Runs." ++ m).toName }]
  let env ← importModules imps.toArray {} (loadExts := true)
  let base := `SolarTV.Milestone.Flag4ce5cf9a
  for (n, ci) in env.constants.toList do
    if base.isPrefixOf n && !(`SolarTV.Milestone.Flag4ce5cf9a.PC).isPrefixOf n then
      if let .thmInfo t := ci then
        let pc := (`SolarTV.Milestone.Flag4ce5cf9a.PC) ++ (n.replacePrefix base .anonymous)
        if let some (.thmInfo t') := env.find? pc then
          IO.println s!"{n},{t.type == t'.type},{t.value == t'.value}"
  return 0
