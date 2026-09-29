import Lean
import SolidCore.Solidity.Checked
import SolidCore.Contest.Observable

/-! Native host for a single harness-generated Lean input. Linked semantic
functions are visible to Lean's evaluator through `supportInterpreter`.
Each invocation has its own environment and state, just like `lean file.lean`.
-/
unsafe def main (args : List String) : IO UInt32 := do
  let [fileName] := args | do
    IO.eprintln "usage: specHuntRunner generated.lean"
    return 2
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let input ← IO.FS.readFile fileName
  let result ← Lean.Elab.runFrontend input {} fileName `SpecHuntInput
  return if result.isSome then 0 else 1
