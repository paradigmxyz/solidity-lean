import Verify.Phase3.RecSource.Source
import SolidCore.Refinement.Generic.LoopSeq

/-!
# RecSum's source runs, by induction on `sum`'s measure

`sum(n)` calls itself at `n - 1`, so its body has no finite erasure: the generic source stage
(`eraseStmt`, `eval_stmt`) inlines every call it erases and never ends here. This file runs it by
induction on the measure `n` (`@custom:decreases n`): the statements around the recursive call run
as their erasure (`eval_stmt`), and the call itself (`call_runs`) runs the callee's body by the
induction hypothesis, at the lower measure, through SolidCore's own internal-call semantics
(`internalCallEnter?`, `internalCallFinish`). Nothing about the callee is assumed: the hypothesis is
the theorem at `n - 1`.
-/

namespace Verify.Phase3.RecSource
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- `0 + 1 + ... + n`. -/
def tri (n : Nat) : Nat := n * (n + 1) / 2

theorem tri_succ (m : Nat) : tri (m + 1) = tri m + (m + 1) := by
  unfold tri
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by
    rw [show m + 1 + 1 = m + 2 from rfl, Nat.mul_add (m + 1) m 2, Nat.mul_comm (m + 1) m,
      Nat.mul_comm (m + 1) 2]
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem tri_le : ∀ n, n ≤ 64 → tri n ≤ 2080 := by
  intro n hn
  have : n * (n + 1) ≤ 64 * 65 := Nat.mul_le_mul hn (by omega)
  unfold tri; omega

/-- The erasure environment of RecSum's bodies, with the contract's function table. -/
def envT (tbl : FunctionTable) : EraseEnv :=
  { fields := [], events := [], tbl := tbl, facts := argFacts [2 ^ 256 - 1] 0 }

/-- The first symbolic state of a call of `sum` or `total`: `n` is argument 0. -/
def S0 : SymState := { scopes := [[("n", .arg 0), ("_ret0", .lit 0)]], writes := [], logs := [] }

theorem leaf_normal {ρ : Val} {E : EraseEnv} {ctx : Context} {r : Result} {S : SymState}
    (h : LeafRel ρ E ctx r (.normal S)) : ∃ rt, r = .normal rt ∧ StmtRel ρ E ctx rt S := by
  cases r <;> simp only [LeafRel] at h
  exact ⟨_, rfl, h⟩

theorem leaf_returned {ρ : Val} {E : EraseEnv} {ctx : Context} {r : Result} {S : SymState}
    {ws : List WExpr} (h : LeafRel ρ E ctx r (.returned S ws [])) :
    ∃ rt, r = .returned rt (ws.map fun e => Value.word (e.eval ρ)) ∧ StmtRel ρ E ctx rt S := by
  cases r <;> simp only [LeafRel] at h
  obtain ⟨h1, rfl⟩ := h
  exact ⟨_, rfl, h1⟩

/-- A statement with an erasure at fuel 10 runs as it at every fuel from 10 on. -/
theorem run_erased {ρ : Val} {E : EraseEnv} {ctx : Context} {s : Stmt} {S : SymState} {b : Br}
    (h : eraseStmt E 10 s S = some b) {rt : Runtime} (hrel : StmtRel ρ E ctx rt S) {n : Nat}
    (hn : 10 ≤ n) : ∃ r, Stmt.eval n E.tbl ctx rt s = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ) := by
  obtain ⟨r, hr, hl⟩ := eval_stmt ρ E ctx 10 s S b h rt hrel
  exact ⟨r, eval_mono hn hr, hl⟩

theorem eval_skip (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) :
    Stmt.eval (n + 1) tbl ctx rt .skip = .done (.ok (.normal rt)) := by
  rw [Stmt.eval]; rfl

/-! ## The erasures of the statements around the call -/

def S1 : SymState := S0.push
def S2 : SymState := S1.push
def S3 : SymState := { S2 with scopes := [[("_sol_hoist_0", .lit 0)], [], [("n", .arg 0), ("_ret0", .lit 0)]] }

/-- The state where a body calls `sum`: its argument `a` in `_ic_arg_0`, `_ret_sum_0` at 0. -/
def Sc (a : WExpr) : SymState :=
  { S3 with scopes := [[("_ret_sum_0", .lit 0), ("_ic_arg_0", a)], [("_sol_hoist_0", .lit 0)], [],
      [("n", .arg 0), ("_ret0", .lit 0)]] }

/-- After the call: `_ret_sum_0` holds the callee's result `t`. -/
def Sd (a : WExpr) (t : Nat) : SymState :=
  { S3 with scopes := [[("_ret_sum_0", .lit t), ("_ic_arg_0", a)], [("_sol_hoist_0", .lit 0)], [],
      [("n", .arg 0), ("_ret0", .lit 0)]] }

/-- After `_sol_hoist_0 = _ret_sum_0`. -/
def Se (a : WExpr) (t : Nat) : SymState :=
  { S3 with scopes := [[("_ret_sum_0", .lit t), ("_ic_arg_0", a)], [("_sol_hoist_0", .lit t)], [],
      [("n", .arg 0), ("_ret0", .lit 0)]] }

/-- Past the call's block. -/
def Sf (t : Nat) : SymState :=
  { S3 with scopes := [[("_sol_hoist_0", .lit t)], [], [("n", .arg 0), ("_ret0", .lit 0)]] }

def nSub : WExpr := .bin .sub (.arg 0) (.lit 1)

theorem e_assign (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 (.assign (.var "n") cn) S1 = some (.leaf (.normal S1)) := rfl

theorem e_base (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 baseIf S2 =
      some (.ite (.bin .eq (.arg 0) (.lit 0)) (.leaf (.returned S2 [.lit 0] [])) (.leaf (.normal S2))) := rfl

theorem e_hoist (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 (.varDecl .uint256 "_sol_hoist_0" none) S2 = some (.leaf (.normal S3)) := rfl

theorem e_recArg (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 (.varDecl .uint256 "_ic_arg_0" (some recArg)) S3.push =
      some (.ite (.bin .lt (.arg 0) (.lit 1)) (.leaf (.reverted (.panic 17)))
        (.leaf (.normal { S3 with scopes := [[("_ic_arg_0", nSub)], [("_sol_hoist_0", .lit 0)], [],
          [("n", .arg 0), ("_ret0", .lit 0)]] }))) := rfl

theorem e_ret (tbl : FunctionTable) (a : WExpr) :
    eraseStmt (envT tbl) 10 (.varDecl .uint256 "_ret_sum_0" none)
      { S3 with scopes := [[("_ic_arg_0", a)], [("_sol_hoist_0", .lit 0)], [], [("n", .arg 0), ("_ret0", .lit 0)]] } =
      some (.leaf (.normal (Sc a))) := rfl

theorem e_assignH (tbl : FunctionTable) (a : WExpr) (t : Nat) :
    eraseStmt (envT tbl) 10 (.assign (.var "_sol_hoist_0") (.var "_ret_sum_0")) (Sd a t) =
      some (.leaf (.normal (Se a t))) := rfl

theorem e_retAdd (tbl : FunctionTable) (t : Nat) :
    eraseStmt (envT tbl) 10 retAdd (Sf t) =
      some (.ite (.bin .lt (.bin .add (.arg 0) (.lit t)) (.arg 0)) (.leaf (.reverted (.panic 17)))
        (.leaf (.returned (Sf t) [.bin .add (.arg 0) (.lit t)] []))) := rfl

/-! ## The recursive call -/

/-- What a run of `sum`'s body from its entry with argument `v` gives, at fuel `F`: it returns
`tri v`, with the state as at its entry (no writes, no logs). -/
def SumRuns (tbl : FunctionTable) (ctx : Context) (F v : Nat) : Prop :=
  ∀ ρ rt, ρ.args = [v] → StmtRel ρ (envT tbl) ctx rt S0 →
    ∃ rt1, Stmt.eval F tbl ctx rt sumBody = .done (.ok (.returned rt1 [.word (tri v)])) ∧
      StmtRel ρ (envT tbl) ctx { rt1 with locals := [] } { S0 with scopes := [] }

theorem run_e {tbl : FunctionTable} {ctx : Context} {ρ : Val} {s : Stmt} {S : SymState} {b : Br}
    (h : eraseStmt (envT tbl) 10 s S = some b) {rt : Runtime} (hrel : StmtRel ρ (envT tbl) ctx rt S)
    {n : Nat} (hn : 10 ≤ n) :
    ∃ r, Stmt.eval n tbl ctx rt s = .done (.ok r) ∧ LeafRel ρ (envT tbl) ctx r (b.eval ρ) :=
  run_erased h hrel hn

/-- A state with no writes, no logs and the fixed caller, its locals dropped, under another
valuation of the same storage: the part of a callee's end its caller keeps. -/
theorem rel_clear {tbl : FunctionTable} {ctx : Context} {ρ ρ' : Val} {rt : Runtime} {S : SymState}
    (h : StmtRel ρ (envT tbl) ctx rt S) (hw : S.writes = []) (hl : S.logs = [])
    (hc : S.caller = .lit callerWord) (hs : ρ'.store = ρ.store) (hh : ρ'.hash = ρ.hash) :
    StmtRel ρ' (envT tbl) ctx { rt with locals := [] } { S0 with scopes := [] } where
  fields := h.fields
  events := h.events
  checked := h.checked
  sender := by rw [h.sender, hc]; rfl
  hash := hh.trans h.hash
  ok := by intro k; rw [hs]; exact h.ok k
  frames := rfl
  store := by
    intro k hk
    rw [h.store k hk, hw]
    simp [Writes.store, S0, hs]
  logs := by rw [h.logs, hl]; rfl
  facts := by simp [envT, argFacts, Facts.Hold]

theorem lit_word {ρ : Val} {t : Nat} (ht : t < Generic.wordSize) :
    ([WExpr.lit t].map fun e => Value.word (e.eval ρ)) = [.word t] := by
  simp [WExpr.eval, Nat.mod_eq_of_lt ht]

/-- **The recursive call, by the callee's run**: a call of `sum` on the word `_ic_arg_0` holds
(`v`), from a state with no writes or logs, ends normally with `_ret_sum_0` holding `tri v`,
when `sum`'s body returns `tri v` from every entry with argument `v` (`SumRuns`). -/
theorem call_runs {tbl : FunctionTable} (htbl : tbl.lookup? sumName = some sumFn) {ctx : Context}
    {ρ : Val} {rt : Runtime} {S : SymState} {a : WExpr} {v j : Nat}
    (hrel : StmtRel ρ (envT tbl) ctx rt S) (hw : S.writes = []) (hlg : S.logs = [])
    (hc : S.caller = .lit callerWord) (ha : Scopes.get? S.scopes "_ic_arg_0" = some a)
    (hv : a.eval ρ = v) {sc : Scopes}
    (hsc : Scopes.setMany S.scopes ["_ret_sum_0"] [.lit (tri v)] = some sc)
    (hbody : SumRuns tbl ctx j v) (ht : tri v < Generic.wordSize) (htg : S.tags = [] := by rfl) :
    ∃ rt', Stmt.eval (j + 2) tbl ctx rt
        (.captureReturn ["_ret_sum_0"] (.internalCall ["_ret_sum_0"] sumName [.var "_ic_arg_0"])) =
        .done (.ok (.normal rt')) ∧ StmtRel ρ (envT tbl) ctx rt' { S with scopes := sc } := by
  have hargs : eraseExprs (envT tbl).fields S [.var "_ic_arg_0"] = some ([], [a]) := by
    simp [eraseExprs, eraseExpr, SymState.word?, htg, ha]
  have hev := eval_refArgs ρ (envT tbl).fields ctx rt S hrel.expr hargs
  have hvW : v < Generic.wordSize := hv ▸ WExpr.eval_lt ρ a
  have hctx : ({ ctx with checked := true } : Context) = ctx := by
    rw [show true = ctx.checked from hrel.checked.symm]
  have hif : sumFn.initialFrame? [Value.word (a.eval ρ)] = some (frameOf ρ (callFrame sumFn [a])) :=
    initialFrame_words ρ sumFn [a] rfl rfl rfl
  have hrelc : StmtRel { ρ with args := [v] } (envT tbl) ctx
      { rt with locals := [frameOf ρ (callFrame sumFn [a])] } S0 :=
    { fields := hrel.fields, events := hrel.events, checked := hrel.checked
      sender := by rw [hrel.sender, hc]; rfl
      hash := hrel.hash, ok := hrel.ok
      frames := by
        simp [S0, callFrame, sumFn, nDecl, retDecl, frameOf, WExpr.eval, hv, Nat.mod_eq_of_lt hvW]
      store := by
        intro k hk
        rw [hrel.store k hk, hw]
        rfl
      logs := by rw [hrel.logs, hlg]; rfl
      facts := by simp [envT, argFacts, Facts.Hold] }
  obtain ⟨rt1, hb, hrel1⟩ := hbody _ _ rfl hrelc
  have hrel1' := rel_clear (ρ' := ρ) hrel1 rfl rfl rfl rfl rfl
  have hca : callAssign ["_ret_sum_0"] S { S0 with scopes := [] } [.lit (tri v)] =
      some (.leaf (.normal ⟨sc, [], [], S.caller, S.tags⟩)) := by
    simp [callAssign, SymState.setManyW, htg, hsc, S0]
  obtain ⟨r, hr, hl⟩ := callAssign_ok hrel hrel1' hca
  rw [lit_word ht] at hr
  obtain ⟨rt', rfl, hrel'⟩ := leaf_normal hl
  have hcall : Stmt.eval (j + 1) tbl ctx rt (.internalCall ["_ret_sum_0"] sumName [.var "_ic_arg_0"]) =
      .done (.ok (.normal rt')) := by
    rw [Stmt.eval]
    simp only [hev, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
      caught_done_ok, bind_done_ok, htbl, internalCallEnter?, hif, hctx]
    rw [show sumFn.body = sumBody from rfl, hb, bind_done_ok]
    simp only [internalCallFinish, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      coerceReturnBindingsRef]
    rw [show [Value.word (tri v)] = ([WExpr.lit (tri v)].map fun e => Value.word (e.eval ρ)) from
      (lit_word ht).symm, coerceRef_words ρ rt1 sumFn.returns [.lit (tri v)] rfl rfl, lit_word ht]
    exact hr
  refine ⟨rt', ?_, ?_⟩
  · rw [Stmt.eval]
    simp only [hcall, bind_done_ok]
    rfl
  · obtain ⟨sc0, w0, l0, c0, t0⟩ := S
    simp only at hw hlg htg
    subst hw hlg htg
    exact hrel'

/-! ## `sum`, by induction on its measure -/

theorem wordSize_gt : (1048576 : Nat) < Generic.wordSize := by unfold Generic.wordSize; decide

theorem sub_one_eval {ρ : Val} {m : Nat} (hρ : ρ.args = [m + 1]) (hm : m + 1 < Generic.wordSize) :
    nSub.eval ρ = m := by
  simp only [nSub, WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero, Nat.mod_eq_of_lt hm]
  have h1 : 1 % Generic.wordSize = 1 := Nat.mod_eq_of_lt (by have := wordSize_gt; omega)
  rw [h1, show m + 1 + (Generic.wordSize - 1) = m + Generic.wordSize by have := wordSize_gt; omega,
    Nat.add_mod_right, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 4000000 in
/-- **`sum`'s body returns `tri v`**, from every entry with argument `v ≤ 64`, at every fuel from
`16 * (v + 1)` on: by induction on the measure `v`, the recursive call at `v - 1` running by the
theorem at the lower measure (`call_runs`). -/
theorem sum_runs {tbl : FunctionTable} (htbl : tbl.lookup? sumName = some sumFn) (ctx : Context) :
    ∀ v, v ≤ 64 → ∀ F, 16 * (v + 1) ≤ F → SumRuns tbl ctx F v
  | 0, _, F, hF => by
    intro ρ rt hρ hrel
    obtain ⟨j, rfl⟩ : ∃ j, F = j + 5 := ⟨F - 5, by omega⟩
    obtain ⟨r1, h1, l1⟩ := run_e (e_assign tbl) hrel.pushScope (n := j + 4) (by omega)
    obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
    obtain ⟨r2, h2, l2⟩ := run_e (e_base tbl) hrel1.pushScope (n := j + 3) (by omega)
    have hc0 : (WExpr.bin .eq (.arg 0) (.lit 0)).eval ρ = 1 := by
      simp [WExpr.eval, BinOp.eval, hρ]
    simp only [Br.eval, hc0, one_ne_zero, ↓reduceIte] at l2
    obtain ⟨rt2, rfl, hrel2⟩ := leaf_returned l2
    have hl2 := evalList_cons_stop
      (rest := [.varDecl .uint256 "_sol_hoist_0" none, callBlock recArg, retAdd]) h2 (fun _ h => by cases h)
    have hb2 := eval_block_of hl2
    have hl1 := evalList_cons_stop (rest := []) hb2 (fun _ h => by cases h)
    have hs := eval_skip (j + 3) tbl ctx rt1
    have hall := eval_block_of ((evalList_cons_normal h1).trans ((evalList_cons_normal hs).trans hl1))
    refine ⟨rt2.popScope.popScope, hall.trans ?_, rel_clear hrel2.popScope.popScope rfl rfl rfl rfl rfl⟩
    simp [Result.mapRuntime, WExpr.eval, tri]
  | m + 1, hv, F, hF => by
    intro ρ rt hρ hrel
    obtain ⟨j, rfl⟩ : ∃ j, F = j + 5 := ⟨F - 5, by omega⟩
    have ih := sum_runs htbl ctx m (by omega) j (by omega)
    have hW := wordSize_gt
    have hm : m + 1 < Generic.wordSize := by omega
    have htm := tri_le m (by omega)
    have ht : tri m < Generic.wordSize := by omega
    -- n = n; skip
    obtain ⟨r1, h1, l1⟩ := run_e (e_assign tbl) hrel.pushScope (n := j + 4) (by omega)
    obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
    have hs := eval_skip (j + 3) tbl ctx rt1
    -- if (n == 0) return 0;  (n = m + 1, so it goes on)
    obtain ⟨r2, h2, l2⟩ := run_e (e_base tbl) hrel1.pushScope (n := j + 3) (by omega)
    have hc0 : (WExpr.bin .eq (.arg 0) (.lit 0)).eval ρ = 0 := by
      simp [WExpr.eval, BinOp.eval, hρ, Nat.mod_eq_of_lt hm]
    simp only [Br.eval, hc0, ↓reduceIte] at l2
    obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
    -- uint256 _sol_hoist_0;
    obtain ⟨r3, h3, l3⟩ := run_e (e_hoist tbl) hrel2 (n := j + 3) (by omega)
    obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
    -- the call's block: uint256 _ic_arg_0 = n - 1;  (n ≥ 1: no underflow)
    obtain ⟨r4, h4, l4⟩ := run_e (e_recArg tbl) hrel3.pushScope (n := j + 2) (by omega)
    have hc1 : (WExpr.bin .lt (.arg 0) (.lit 1)).eval ρ = 0 := by
      simp [WExpr.eval, BinOp.eval, hρ, Nat.mod_eq_of_lt hm]
    simp only [Br.eval, hc1, ↓reduceIte] at l4
    obtain ⟨rt4, rfl, hrel4⟩ := leaf_normal l4
    -- uint256 _ret_sum_0;
    obtain ⟨r5, h5, l5⟩ := run_e (e_ret tbl nSub) hrel4 (n := j + 2) (by omega)
    obtain ⟨rt5, rfl, hrel5⟩ := leaf_normal l5
    -- _ret_sum_0 = sum(n - 1): the theorem at the lower measure m
    obtain ⟨rt6, h6, hrel6⟩ := call_runs (sc := (Sd nSub (tri m)).scopes) htbl hrel5 rfl rfl rfl rfl
      (sub_one_eval hρ hm) rfl ih ht
    -- _sol_hoist_0 = _ret_sum_0;
    obtain ⟨r7, h7, l7⟩ := run_e (e_assignH tbl nSub (tri m)) hrel6 (n := j + 2) (by omega)
    obtain ⟨rt7, rfl, hrel7⟩ := leaf_normal l7
    have hcb := eval_block_of ((evalList_cons_normal h4).trans ((evalList_cons_normal h5).trans
      ((evalList_cons_normal h6).trans ((evalList_cons_normal h7).trans (evalList_nil _ _ _ _)))))
    have hcb' : Stmt.eval (j + 3) tbl ctx rt3 (callBlock recArg) = .done (.ok (.normal rt7.popScope)) := hcb
    -- return n + _sol_hoist_0;  (no overflow)
    obtain ⟨r8, h8, l8⟩ := run_e (e_retAdd tbl (tri m)) hrel7.popScope (n := j + 3) (by omega)
    have hadd : (WExpr.bin .add (.arg 0) (.lit (tri m))).eval ρ = tri (m + 1) := by
      simp only [WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero, Nat.mod_eq_of_lt hm,
        Nat.mod_eq_of_lt ht, Nat.mod_mod, tri_succ]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hc2 : (WExpr.bin .lt (.bin .add (.arg 0) (.lit (tri m))) (.arg 0)).eval ρ = 0 := by
      simp only [WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero, Nat.mod_eq_of_lt hm,
        Nat.mod_eq_of_lt ht, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (show m + 1 + tri m < Generic.wordSize by omega)]
      have : ¬ (m + 1 + tri m < m + 1) := by omega
      simp [this]
    simp only [Br.eval, hc2, ↓reduceIte] at l8
    obtain ⟨rt8, rfl, hrel8⟩ := leaf_returned l8
    have hl := (evalList_cons_normal h2).trans ((evalList_cons_normal h3).trans
      ((evalList_cons_normal hcb').trans (evalList_cons_stop (rest := []) h8 (fun _ h => by cases h))))
    have hb1 := eval_block_of hl
    have hall := eval_block_of ((evalList_cons_normal h1).trans ((evalList_cons_normal hs).trans
      (evalList_cons_stop (rest := []) hb1 (fun _ h => by cases h))))
    refine ⟨rt8.popScope.popScope, hall.trans ?_, rel_clear hrel8.popScope.popScope rfl rfl rfl rfl rfl⟩
    simp only [Result.mapRuntime, List.map_cons, List.map_nil, hadd]

/-- info: 'Verify.Phase3.RecSource.sum_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_runs

end Verify.Phase3.RecSource
