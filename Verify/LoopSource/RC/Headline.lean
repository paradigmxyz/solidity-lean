import SolidCore.Refinement.Generic.LoopRun
import SolidCore.Refinement.Generic.SourceCall
import Contracts.VerifyCounter.SourceBump

/-!
# The expected headline for Counter.bump's loop, stated apart from its proof

This module states, from the source semantics alone, what the loop route must prove for
`Counter.bump`: whenever a function's body is bump's source AST (`bumpBody`) and its call starts
in bump's entry state (`S0`), its body runs, for all enough fuel, to the branch tree `bumpBr`
under the source erasure semantics (`Loop.BodyRuns`). It imports only the source semantics
(`LoopRun`, `SourceCall`) and Counter's source model (`SourceBump`: the AST, entry state, tree and
environment), never the proof or solar-verify's obligations; the `#assert_not_imported` checks below
fail the build if it ever does. `HeadlineCheck.lean` then checks the proof against this statement.
-/

namespace Verify.LoopSource.RC.Headline
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source

/-- **The expected headline**: bump's body, from its entry state, runs to `bumpBr` for all fuel at
least `2 ^ 256 + 8`, for every event list, function table and function with that body. -/
def CounterBumpLoopHeadline : Prop :=
  ∀ (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef),
    fn.body = bumpBody → initState fn = S0 →
      ∀ fuel : Nat, 2 ^ 256 + 8 ≤ fuel → BodyRuns (env ev tbl) fuel fn bumpBr

end Verify.LoopSource.RC.Headline

open Lean Elab Command in
/-- `#assert_not_imported M`: the module `M` is not in this file's import closure. -/
elab "#assert_not_imported " m:ident : command => do
  let found := (← getEnv).header.moduleNames.contains m.getId
  logInfo m!"{m.getId} imported: {found}"

/-- info: Contracts.VerifyCounter.LoopVC imported: false -/
#guard_msgs in
#assert_not_imported Contracts.VerifyCounter.LoopVC

/-- info: Contracts.VerifyCounter.LoopBinding imported: false -/
#guard_msgs in
#assert_not_imported Contracts.VerifyCounter.LoopBinding

/-- info: SolidCore.Refinement.Generic.LoopErased imported: false -/
#guard_msgs in
#assert_not_imported SolidCore.Refinement.Generic.LoopErased

/-- info: Verify.LoopSource.LoopMap imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.LoopMap

/-- info: Verify.LoopSource.CheckRaw imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.CheckRaw

/-- info: Verify.LoopSource.RC.Counter.Obligations imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.RC.Counter.Obligations

/-- info: Verify.LoopSource.RC.Counter.Map imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.RC.Counter.Map

/-- info: Verify.LoopSource.RC.Counter.Script imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.RC.Counter.Script

