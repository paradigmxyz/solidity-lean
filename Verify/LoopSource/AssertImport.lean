import Lean

/-!
# `#assert_not_imported`: a module is not in the current file's import closure

Statement modules use it to show that they import no proof: the check's message names the module
and whether it is imported, and `#guard_msgs` fails the build if it is.
-/

open Lean Elab Command in
/-- `#assert_not_imported M`: the module `M` is not in this file's import closure. -/
elab "#assert_not_imported " m:ident : command => do
  let found := (← getEnv).header.moduleNames.contains m.getId
  logInfo m!"{m.getId} imported: {found}"
