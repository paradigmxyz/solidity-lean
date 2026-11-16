import W1Proofs.Tactic

/-! Bench only: sym_exec whose normalization loop skips the sym_eval pass that follows a
successful sym_eval. sym_eval is one dsimp call, which already runs to a fixpoint, so that pass
can only fail after a full traversal; a failed pass leaves no proof term. The other steps, and
their order, are sym_norm's: each round tries sym_eval (unless the last step was sym_eval),
then sym_cond, then sym_mem, and stops when none applies. Everything else is copied from
W1Proofs.Tactic. -/

namespace SolarTV.Milestone.W1
open EvmRules Machine
open Lean Elab Tactic

/-- Counts of sym_eval passes skipped, across the file. -/
initialize skipped : IO.Ref Nat ← IO.mkRef 0

def tryStep (stx : Syntax) : TacticM Bool :=
  (do evalTactic stx; pure true) <|> pure false

partial def symNormSkip (lastEval : Bool) : TacticM Unit := do
  if lastEval then
    skipped.modify (· + 1)
  else if ← tryStep (← `(tactic| sym_eval)) then
    return ← symNormSkip true
  if ← tryStep (← `(tactic| sym_cond)) then return ← symNormSkip false
  if ← tryStep (← `(tactic| sym_mem)) then return ← symNormSkip false

elab "sym_norm_skip" : tactic => symNormSkip false

elab "#sym_eval_skipped" : command => do
  logInfo m!"sym_eval passes skipped: {← skipped.get}"

set_option hygiene false in
macro "sym_exec_skip" : tactic => `(tactic| (
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  sym_norm_skip
  repeat' ((first | split_cond | split_table) <;> sym_norm_skip)
  all_goals first
    | with_reducible rfl
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)
    | (exfalso; sym_comm_contra)
    | sym_select
    | sym_agree
    | sym_expand
    | (sym_mem_order <;> first
        | with_reducible rfl
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | sym_select
        | sym_agree)
    | fail "sym_exec: the runs end in different results on this path, or the procedure cannot tell"))

end SolarTV.Milestone.W1
