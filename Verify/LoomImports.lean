import Verify.CounterBump
import Verify.Fuel

/-! The certified Loom path does not reach Loom's SMT layer (lean-auto, z3, cvc5), its
VC tactic layer or `Verify.Finite` (which uses `native_decide`): elaboration fails
if any of these modules is in this file's import closure. -/

open Lean Elab Command in
run_cmd do
  let forbidden := [`Loom.SMT, `Auto, `Loom.TacticAsync, `Loom.Meta,
    `Loom.MonadAlgebras.WP.Tactic, `Verify.Finite, `Verify.Tactic]
  let mods := (← getEnv).header.moduleNames
  for f in forbidden do
    if mods.any (fun m => m == f || f.isPrefixOf m) then
      throwError m!"certified Loom path imports {f}"
  logInfo m!"import closure: {mods.size} modules, none forbidden"
