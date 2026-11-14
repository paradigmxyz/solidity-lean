import SolidCore.Refinement.Generic.Loop

/-! # Blocks and statement lists, for composing a body around a loop -/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

theorem eval_block_of {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt : Runtime}
    {ss : List Stmt} {r : Result} (h : Stmt.evalList n tbl ctx rt.pushScope ss = .done (.ok r)) :
    Stmt.eval (n + 1) tbl ctx rt (.block ss) = .done (.ok (r.mapRuntime Runtime.popScope)) := by
  rw [Stmt.eval]
  simp only [h, bind, EvmCompiler.Simulation.Interaction.bind]
  rfl

theorem evalList_nil (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) :
    Stmt.evalList n tbl ctx rt [] = .done (.ok (.normal rt)) := by
  simp only [Stmt.evalList]
  rfl

theorem evalList_cons_normal {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt rt' : Runtime}
    {s : Stmt} {rest : List Stmt} (h : Stmt.eval n tbl ctx rt s = .done (.ok (.normal rt'))) :
    Stmt.evalList n tbl ctx rt (s :: rest) = Stmt.evalList n tbl ctx rt' rest := by
  simp only [Stmt.evalList]
  rw [h, bind_done_ok]

/-- A statement that does not end normally ends the list it starts. -/
theorem evalList_cons_stop {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt : Runtime}
    {s : Stmt} {rest : List Stmt} {r : Result} (h : Stmt.eval n tbl ctx rt s = .done (.ok r))
    (hr : ∀ rt', r ≠ .normal rt') :
    Stmt.evalList n tbl ctx rt (s :: rest) = .done (.ok r) := by
  simp only [Stmt.evalList]
  rw [h, bind_done_ok]
  cases r with
  | normal rt' => exact absurd rfl (hr rt')
  | _ => rfl

theorem Result.mapRuntime_reverted (f : Runtime → Runtime) (rt : Runtime) (e : RevertData) :
    (Result.reverted rt e).mapRuntime f = .reverted (f rt) e := rfl

theorem Facts.hold_nil (ρ : Val) : Facts.Hold ρ [] := fun _ h => absurd h List.not_mem_nil

end SolidCore.Refinement.Generic.Loop
