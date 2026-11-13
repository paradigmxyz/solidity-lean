-- import AeneasMeta.Utils
import Loom.Meta

-- namespace Loom.Async

open Lean Elab Term Meta Tactic

/-!
# Asynchronous execution
-/

/-
I noticed a bit too late that I could have used `Lean.Elab.Term.wrapAsyncAsSnapshot` instead of
`Lean.Core.wrapAsyncAsSnapshot` but I guess it shouldn't make much difference.
-/
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken) :
  TacticM (IO.Promise (Array Bool) × (α → BaseIO Language.SnapshotTree)) := do
  withMainContext do
  let mut mvars <- getUnsolvedGoals
  let promise : IO.Promise (Array Bool) ← IO.Promise.new
  let runTac? (x : α) : TermElabM Unit := do
    let mut results := #[]
    try
      for mvar in mvars do
        let ngoals <- Tactic.run mvar (tactic x)
        if ngoals.isEmpty then
          results := results.push true
        else
          results := results.push false
    catch _ =>
      results := results.append <| Array.replicate mvars.length false
    promise.resolve results
  let tac ← Lean.Elab.Term.wrapAsyncAsSnapshot runTac? cancelTk?
  pure (promise, tac)

def asyncRunTactic (tactic : TacticM Unit) (cancelTk? : Option IO.CancelToken := none)
  (prio : Task.Priority := Task.Priority.default)
  (stx? : Option Syntax := none) :
  TacticM (IO.Promise (Array Bool)) := do
  let (promise, tactic) ← wrapTactic (fun () => tactic) cancelTk?
  let task ← BaseIO.asTask (tactic ()) prio
  Core.logSnapshotTask { stx?, task := task, cancelTk? := cancelTk? }
  pure promise

/- Run `tac` on the current goals in parallel -/
def asyncRunTacticOnGoals (tac : TacticM Unit) (mvarIds : Array (Array MVarId))
  (cancelTk? : Option IO.CancelToken := none) (prio : Task.Priority := Task.Priority.default)
  (stx? : Option Syntax := none) :
  TacticM (Array (IO.Promise (Array Bool))) := do
  let mut results := #[]
  -- Create tasks
  for mvarId in mvarIds do
    -- unless (← mvarId.isAssigned) do
    setGoals mvarId.toList
    results := results.push (← asyncRunTactic tac cancelTk? prio stx?)
  pure results

partial def splitListInNParts (arr : Array α) (n : Nat) : Array (Array α) := Id.run do
  let mut parts := Array.replicate n #[]
  for h : i in [0:arr.size] do
    parts := parts.modify (i % n) (·.push arr[i])
  parts

/- Run `tac` on the current goals in parallel -/
def allGoalsAsync
  (tac : TacticM Unit)
  (numTasks : Option Nat := none)
  (cancelTk? : Option IO.CancelToken := none)
  (prio : Task.Priority := Task.Priority.default)
  (stx? : Option Syntax := none) :
  TacticM Unit := do
  let goals <- getUnsolvedGoals
  let mvarIdArrays := splitListInNParts goals.toArray (numTasks.getD goals.length)
  let promises ← asyncRunTacticOnGoals tac mvarIdArrays cancelTk? prio stx?
  -- Wait for the tasks
  let mut unsolved := #[]
  for (mvarIds, promise) in mvarIdArrays.zip promises do
    match promise.result?.get with
    | none =>
      unsolved := unsolved.append mvarIds
    | some results =>
      for (mvarId, result) in mvarIds.zip results do
        if result then
            mvarId.admit
        else
          unsolved := unsolved.push mvarId
  setGoals unsolved.toList
