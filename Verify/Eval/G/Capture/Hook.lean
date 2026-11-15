import W1Proofs.Tactic

/-!
# Lane G: capture the real side conditions of W1Proofs' sym_mem discharger

A second elaborator for the syntax of SolarTV.Milestone.W1's sym_mem_disch, tried before the
original: it prints each side condition, with its whole local context, as a standalone theorem
(names exposed, full names, numeric types), runs the original sym_mem_disch_core, and records
whether it proved it and how long it took, appending to the file G_CAPTURE_OUT names. The files beside this one run stage proofs of
Certified/<name>/Proofs/Runs, unchanged, with this hook.

Not part of any build; run with scripts under this directory only (it needs abi_hash's generated
stages compiled).
-/

open Lean Meta Elab Tactic

namespace Verify.Eval.G.Capture

/-- The goal as the text of a standalone theorem. -/
def goalText (mvarId : MVarId) : MetaM String := do
  let mvarId ← mvarId.exposeNames
  mvarId.withContext do
    let mut binders := ""
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      binders := binders ++ s!" ({d.userName} : {← ppExpr ty})"
    let t ← ppExpr (← instantiateMVars (← mvarId.getType))
    return s!"theorem CAPNAME{binders} :\n    {t}"

@[tactic SolarTV.Milestone.W1.tacticSym_mem_disch] def captureDisch : Tactic := fun _ => do
  let g ← getMainGoal
  -- exposeNames assigns the goal: print from a copy of the state.
  let txt ← withoutModifyingState <| withOptions (fun o => (pp.fullNames.set (pp.numericTypes.set (pp.funBinderTypes.set
    (pp.proofs.set (pp.deepTerms.set (pp.maxSteps.set o 100000000) true) true) true) true) true)) <|
    goalText g
  let t0 ← IO.monoNanosNow
  let (ok, err) ← try
      withoutRecover (evalTactic (← `(tactic| sym_mem_disch_core)))
      pure (true, "")
    catch e => pure (false, ← e.toMessageData.toString)
  let t1 ← IO.monoNanosNow
  -- simp drops the messages a discharger logs, so the record goes to a file.
  let out := (← IO.getEnv "G_CAPTURE_OUT").getD "/tmp/g-capture.txt"
  let h ← IO.FS.Handle.mk out .append
  h.putStrLn s!"CAPTURE ok={ok} ms={(t1 - t0).toFloat / 1000000.0}\n{txt}\nENDCAPTURE"
  unless ok do h.putStrLn s!"ERROR {(err.take 300).replace "\n" " "}"
  h.flush
  unless ok do throwError "sym_mem_disch: not proved"

end Verify.Eval.G.Capture
