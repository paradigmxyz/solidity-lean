import Verify.LoopSource.Proof.LoopBinding
import Verify.LoopSource.LoopMap
import Verify.LoopSource.RC.Counter.Obligations
import Verify.LoopSource.RC.Counter.Map

/-!
# bump's loop, bound to solar-verify's obligations through the emitted loop-head map

`Verify.LoopSource.RC.Counter.Obligations` holds solar-verify's obligations for `bump` as Lean
obligations over its SSA names, with `obs_valid` (the script's verdict decided by the kernel, and
the check that the script gives them). `Verify.LoopSource.RC.Counter.Map` is the loop-head manifest
solar-verify emitted for the same source and compiler (`--emit-loop-heads`, checked current with
`--check-loop-heads` and against the obligations' pins by `gen_loopmap.py`), as places `M`. This module binds the two to the source loop bridge:

* `w_*`: the map's place for each name is the word the source loop's header state `headerS`
  holds there (by `decide`): a stale or mismatched map fails here;
* `envN`: solar-verify's assignment is `M.env headerS` at a header valuation for every name the
  manifest places; the binding supplies only the names it leaves out (`freeNames`: the limit and
  the call environment, `frN`);
* `consec_corr`: the evaluation correspondence (`LoopMap.Corr`, `holds_eq`) carries consecution's
  goal over the names to the words of the body's tree: the slot write `count + 1` (`SB`) and the
  scope update `i + 1` (`L'`);
* `init_vc`, `consec_vc`, `decr_vc`, `post_vc`: each obligation's facts hold at `envN`, so its
  goal does; `obl_vc` and `body_runs_vc` take initiation, consecution, the measure's fall and the
  exit from them (`ForObl`, `BodyRuns`).

Not from solar-verify: the overflow guards of `count++` and `i++` (`hc1`, `hi1`), proved here from
the invariant and the precondition, since solar-verify outside `--strict` treats an overflow as a
reverting path rather than an obligation.
-/

namespace Contracts.VerifyCounter.LoopVC
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source Contracts.VerifyCounter.LoopBinding
open SolidCore.Verify.VC SolidCore.Verify.LoopMap Verify.LoopSource.RC.Counter

/-! ## The map against the source loop's header -/

theorem w_count17 : M.word headerS "count@17" = some (.init 0) := by decide
theorem w_n21 : M.word headerS "n@21" = some (.arg 0) := by decide
theorem w_i28 : M.word headerS "i@28" = some (.arg 1) := by decide
theorem w_count27 : M.word headerS "count@27" = some (.arg 2) := by decide

/-! The names no loop-head variable places (`freeNames`): the limit, which the loop does not
mention, and the call environment. -/

theorem free_names : freeNames = ["limit@18", "msg.sender@2", "msg.value@3", "this@1"] := by decide
theorem f_limit18 : M.word headerS "limit@18" = none := by decide
theorem f_sender2 : M.word headerS "msg.sender@2" = none := by decide
theorem f_value3 : M.word headerS "msg.value@3" = none := by decide
theorem f_this1 : M.word headerS "this@1" = none := by decide

/-- The values the binding supplies for them: the call's limit, a nonzero contract and caller
(`callerWord`), and no value sent (`bump` is not payable). -/
def frN (lim : Nat) (x : String) : Int :=
  if x = "limit@18" then lim else if x = "this@1" then 1 else if x = "msg.sender@2" then 0x2000 else 0

/-- A header valuation from its words: `n`, `i` and the count as arguments 0 to 2 (`headerS`),
the count before the loop and the limit in slots 0 and 1. -/
def σN (c0 lim n i cnt : Nat) : Val :=
  ⟨[n, i, cnt], fun k => if k = 0 then c0 else if k = 1 then lim else 0, fun _ _ => 0, 0⟩

/-- solar-verify's assignment at that valuation, from the map. -/
def envN (c0 lim n i cnt : Nat) : Env := M.env headerS (frN lim) (σN c0 lim n i cnt)

theorem hval_eq (ρ : Val) (i cnt : Nat) (h0 : ρ.store 0 < Generic.wordSize)
    (h1 : ρ.store 1 < Generic.wordSize) (hi : i < Generic.wordSize) (hc : cnt < Generic.wordSize) :
    ∀ w ∈ [WExpr.init 0, .init 1, .arg 0, .arg 1, .arg 2],
      w.eval (hval ρ i cnt) = w.eval (σN (ρ.store 0) (ρ.store 1) (nOf ρ) i cnt) := by
  simp [WExpr.eval, hval, σN, nOf, Nat.mod_mod]

variable (c0 lim n i cnt : Nat) (hc0 : c0 < Generic.wordSize) (hlim : lim < Generic.wordSize)
  (hn : n < Generic.wordSize) (hi : i < Generic.wordSize) (hcnt : cnt < Generic.wordSize)
  (hpre : c0 + n ≤ lim)

include hc0 hlim hn hi hcnt in
/-- Each name's value at `envN`, read through the map. -/
theorem envN_vals :
    (envN c0 lim n i cnt).i "count@17" = c0 ∧ (envN c0 lim n i cnt).i "limit@18" = lim ∧
    (envN c0 lim n i cnt).i "n@21" = n ∧ (envN c0 lim n i cnt).i "i@28" = i ∧
    (envN c0 lim n i cnt).i "count@27" = cnt ∧ (envN c0 lim n i cnt).i "this@1" = 1 ∧
    (envN c0 lim n i cnt).i "msg.sender@2" = 0x2000 ∧ (envN c0 lim n i cnt).i "msg.value@3" = 0 := by
  simp only [envN, LoopMap.env_i w_count17, LoopMap.env_i w_n21, LoopMap.env_i w_i28,
    LoopMap.env_i w_count27, LoopMap.env_free f_limit18, LoopMap.env_free f_this1,
    LoopMap.env_free f_sender2, LoopMap.env_free f_value3]
  simp [WExpr.eval, σN, frN, Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hcnt]

/-- `2 ^ 256` as a numeral, for `omega`. -/
theorem hW : Generic.wordSize = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  decide

include hc0 hlim hn hpre in
/-- **Initiation**, from `init_0` and `init_1`: the invariant at `i = 0`, `count = old(count)`. -/
theorem init_vc : 0 ≤ n ∧ c0 + 0 = c0 + 0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    envN_vals c0 lim n 0 c0 hc0 hlim hn (by decide) hc0
  have hw := hW
  have h0 := obs_valid.get mem_init_0 (envN c0 lim n 0 c0) (by
    simp only [init_0, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  have h1 := obs_valid.get mem_init_1 (envN c0 lim n 0 c0) (by
    simp only [init_1, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  simp only [init_0, init_1] at h0 h1
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h0
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h1
  omega

include hc0 hlim hn hi hcnt hpre in
/-- **Consecution**, from `consec_2` and `consec_3`. -/
theorem consec_vc (hI : i ≤ n) (hC : cnt = c0 + i) (hlt : i < n) :
    i + 1 ≤ n ∧ cnt + 1 = c0 + (i + 1) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := envN_vals c0 lim n i cnt hc0 hlim hn hi hcnt
  have hw := hW
  have h2 := obs_valid.get mem_consec_2 (envN c0 lim n i cnt) (by
    simp only [consec_2, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  have h3 := obs_valid.get mem_consec_3 (envN c0 lim n i cnt) (by
    simp only [consec_3, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  simp only [consec_2, consec_3] at h2 h3
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h2
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h3
  omega

include hc0 hlim hn hi hcnt hpre in
/-- **Termination**, from `decr_4`: the measure `n - i` is a natural number and falls. -/
theorem decr_vc (hI : i ≤ n) (hC : cnt = c0 + i) (hlt : i < n) : n - (i + 1) < n - i := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := envN_vals c0 lim n i cnt hc0 hlim hn hi hcnt
  have hw := hW
  have h4 := obs_valid.get mem_decr_4 (envN c0 lim n i cnt) (by
    simp only [decr_4, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  simp only [decr_4] at h4
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h4
  omega

include hc0 hlim hn hi hcnt hpre in
/-- **Exit**, from `post_6`: at `i >= n` the invariant gives the postcondition. -/
theorem post_vc (hI : i ≤ n) (hC : cnt = c0 + i) (hge : ¬ i < n) : cnt = c0 + n := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := envN_vals c0 lim n i cnt hc0 hlim hn hi hcnt
  have hw := hW
  have h6 := obs_valid.get mem_post_6 (envN c0 lim n i cnt) (by
    simp only [post_6, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] <;> omega)
  simp only [post_6] at h6
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8] at h6
  omega

/-! ## The evaluation correspondence on consecution's goal -/

/-- consecution's goal `count@27 + 1 == count@17 + (i@28 + 1)` over the names. -/
def consecGoal : Tm :=
  .app "=" [.app "+" [.ivar "count@27", .num 1], .app "+" [.ivar "count@17", .app "+" [.ivar "i@28", .num 1]]]

/-- The goal's left side is the word `bump`'s body writes to slot 0 (`SB`), and the right side
`old(count)` plus the word `i++` leaves in scope (`L'`). -/
theorem consec_corr_lhs : Corr M headerS (.app "+" [.ivar "count@27", .num 1]) (.bin .add (.arg 2) (.lit 1)) :=
  .add (.var w_count27) (.num (by decide))

theorem consec_corr_rhs :
    Corr M headerS (.app "+" [.ivar "count@17", .app "+" [.ivar "i@28", .num 1]])
      (.bin .add (.init 0) (.bin .add (.arg 1) (.lit 1))) :=
  .add (.var w_count17) (.add (.var w_i28) (.num (by decide)))

theorem sb_write : SB.writes = [(.lit 0, .bin .add (.arg 2) (.lit 1))] := rfl
theorem l'_i : Scopes.get? L' "i" = some (.bin .add (.arg 1) (.lit 1)) := by decide

include hc0 hi hcnt in
/-- **Consecution, word for word**: where nothing wraps, solar-verify's consecution goal at the map's
assignment is the equation between the body's slot-0 write and `old(count)` plus the scope's new
`i`, evaluated at the header valuation. -/
theorem consec_corr (hw : cnt + 1 < Generic.wordSize) (hw' : c0 + (i + 1) < Generic.wordSize) :
    consecGoal.Holds (envN c0 lim n i cnt) ↔
      (WExpr.bin .add (.arg 2) (.lit 1)).eval (σN c0 lim n i cnt) =
        (WExpr.bin .add (.init 0) (.bin .add (.arg 1) (.lit 1))).eval (σN c0 lim n i cnt) := by
  have hi1 : i + 1 < Generic.wordSize := by omega
  have h1 : 1 % Generic.wordSize = 1 := by decide
  have hw := hW
  apply holds_eq consec_corr_lhs consec_corr_rhs
  · simp [NoWrap, WExpr.eval, BinOp.eval, σN, h1, Nat.mod_eq_of_lt hcnt] <;> omega
  · simp [NoWrap, WExpr.eval, BinOp.eval, σN, h1, Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hi1] <;> omega

/-! ## A satisfiable precondition: the obligations' facts are not vacuous -/

/-- **Nonvacuity witness**: with `n = 3`, `count = 5`, `limit = 8` (z3's model of the probe), the
precondition holds, the loop runs (`0 < n`), and every fact of consecution's obligation holds at
the map's assignment at the loop head with `i = 1`, `count = 6`. -/
theorem pre_witness :
    5 + 3 ≤ 8 ∧ 0 < 3 ∧ ∀ x ∈ consec_3.2.1, x.Holds (envN 5 8 3 1 6) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    envN_vals 5 8 3 1 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw := hW
  refine ⟨by decide, by decide, ?_⟩
  simp only [consec_3, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros <;> simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toInt, Value.toProp, Value.eq, e1, e2, e3, e4, e5, e6, e7, e8]

set_option maxHeartbeats 4000000 in
/-- **The loop's obligations hold**, consecution and termination from solar-verify's obligations. -/
theorem obl_vc (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (ctx : Context) (hok : ρ.Ok)
    (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    ForObl 3 (env ev tbl) ctx cond post body headerS (P ρ) m (Q ρ (env ev tbl) ctx) c bb where
  cond_erase := rfl
  body_runs := stmtRuns_block1 (stmtRuns_incField 1 true rfl)
  exit := by
    rintro σ rt ⟨i, cnt, hiw0, hcw0, rfl, hI⟩ hrel hc0
    have hi : i ≤ nOf ρ := by omega
    have hcnt : cnt = ρ.store 0 + i := by omega
    subst hcnt
    have hlim : ρ.store 1 < Generic.wordSize := hok.word 1
    have hn := nOf_lt ρ
    have hiw : i < Generic.wordSize := by omega
    have hcw : ρ.store 0 + i < Generic.wordSize := by omega
    obtain ⟨a0, a1, -⟩ := hval_args ρ i _ hiw hcw
    have hge : ¬ i < nOf ρ := by
      intro hlt
      rw [c_eval ρ i hiw, if_pos hlt] at hc0
      cases hc0
    -- the exit: solar-verify's obligation post_6
    have hpost := post_vc (ρ.store 0) (ρ.store 1) (nOf ρ) i (ρ.store 0 + i)
      (hok.word 0) hlim hn hiw hcw hpre hi rfl hge
    have hie : i = nOf ρ := by omega
    refine ⟨rt, rfl, StmtRel.congr hrel hrel.hash hok (Facts.hold_nil _) ?_ ?_ rfl⟩
    · simp [headerS, exitS, frameOf, WExpr.eval, hval, Nat.mod_eq_of_lt hiw, hie, nOf]
    · intro k _
      have h0 := hok.word 0
      have hie' : ρ.args.getD 0 0 % Generic.wordSize = i := hie.symm
      simp only [Writes.store, headerS, exitS, WExpr.eval, BinOp.eval, hval, List.getD_cons_succ,
        List.getD_cons_zero]
      by_cases hk0 : 0 % Generic.wordSize = k % Generic.wordSize <;> simp only [hk0, ↓reduceIte]
      rw [Nat.mod_eq_of_lt h0, hie', Nat.mod_mod]
  iter := by
    rintro σ ⟨i, cnt, hiw0, hcw0, rfl, hI⟩ hc
    have hi : i ≤ nOf ρ := by omega
    have hcnt : cnt = ρ.store 0 + i := by omega
    subst hcnt
    have hlim : ρ.store 1 < Generic.wordSize := hok.word 1
    have hn := nOf_lt ρ
    have hiw : i < Generic.wordSize := by omega
    have hcw : ρ.store 0 + i < Generic.wordSize := by omega
    obtain ⟨a0, a1, a2⟩ := hval_args ρ i (ρ.store 0 + i) hiw hcw
    have hin : i < nOf ρ := by
      by_contra hge
      exact hc (by rw [c_eval ρ i hiw, if_neg hge])
    have hc1 : ρ.store 0 + i + 1 < Generic.wordSize := by omega
    have hi1 : i + 1 < Generic.wordSize := by omega
    -- the body: count++, its overflow guard false
    have hbb : bb.eval (hval ρ i (ρ.store 0 + i)) = .normal SB := by
      have hbr : incFieldBr 0 0 32 headerS.push =
          guards [.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)]
            (.leaf (.normal { headerS.push with writes := [(.lit 0, .bin .add (.arg 2) (.lit 1))] })) := rfl
      have hg : ([WExpr.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)].any
          (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0)) = false := by
        simp [WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hcw, Nat.mod_eq_of_lt hc1]
      rw [bb, Br.eval_mapS, hbr, guards_eval, hg]
      rfl
    rw [hbb]
    -- the update: i++, its overflow guard false
    refine ⟨incVarBr (.arg 1) L' SB, stmtRuns_incVar 2 true rfl rfl, ?_⟩
    have hg2 : (overflow .add (.arg 1) (.lit 1)).toList.any
        (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0) = false := by
      simp [overflow, WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
    simp only [incVarBr, guards_eval, hg2, Bool.false_eq_true, ↓reduceIte, Br.eval]
    -- back at the header with i + 1, the measure one lower
    have hc1' : ρ.store 0 + (i + 1) < Generic.wordSize := by omega
    obtain ⟨b0, b1, b2⟩ := hval_args ρ (i + 1) _ hi1 hc1'
    -- consecution and the measure's fall: solar-verify's obligations consec_2, consec_3, decr_4
    obtain ⟨hn1, hcnt1⟩ := consec_vc (ρ.store 0) (ρ.store 1) (nOf ρ) i (ρ.store 0 + i)
      (hok.word 0) hlim hn hiw hcw hpre hi rfl hin
    refine ⟨hval ρ (i + 1) (ρ.store 0 + (i + 1)),
      ⟨i + 1, ρ.store 0 + (i + 1), hi1, hc1', rfl, hn1, rfl⟩, ?_, ?_⟩
    · simp only [m, a0, a1, a2, b0, b1, b2]
      exact decr_vc (ρ.store 0) (ρ.store 1) (nOf ρ) i (ρ.store 0 + i)
        (hok.word 0) hlim hn hiw hcw hpre hi rfl hin
    · intro rp hl2
      refine StmtRel.congr hl2 hl2.hash hok (Facts.hold_nil _) ?_ ?_ rfl
      · simp [SB, L', headerS, SymState.pop, SymState.push, frameOf, WExpr.eval, BinOp.eval, hval,
          Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
      · intro k _
        simp only [Writes.store, SB, SymState.pop, SymState.push, headerS, WExpr.eval, BinOp.eval,
          hval, List.getD_cons_succ, List.getD_cons_zero]
        split_ifs
        · rw [Nat.mod_eq_of_lt hcw, show 1 % Generic.wordSize = 1 by decide, Nat.mod_mod, ← Nat.add_assoc]
        · rfl


set_option maxHeartbeats 4000000 in
/-- **bump's body runs to `bumpBr`**, initiation from solar-verify's obligations,, the loop by the generic bridge, at every fuel from
`2 ^ 256 + 8` on. -/
theorem body_runs_vc (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef)
    (hbody : fn.body = bumpBody) (hinit : initState fn = S0) (fuel : Nat)
    (hfuel : 2 ^ 256 + 8 ≤ fuel) : BodyRuns (env ev tbl) fuel fn bumpBr := by
  intro ρ ctx rt hrel
  rw [hinit] at hrel
  rw [hbody]
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  have hok : ρ.Ok := hrel.ok
  set E := env ev tbl with hE
  -- n = n
  obtain ⟨r1, h1, l1⟩ := eval_stmt ρ E ctx 10 s1 S0.push _ (e1 ev tbl) rt.pushScope hrel.pushScope
  obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
  have h1' := eval_mono (by omega : 10 ≤ f + 3) h1
  -- require(count + n <= limit, "over")
  obtain ⟨r2, h2, l2⟩ := eval_stmt ρ E ctx 10 s2 S0.push.push _ (e2 ev tbl) rt1.pushScope
    hrel1.pushScope
  have h2' := eval_mono (by omega : 10 ≤ f + 2) h2
  unfold bumpBr
  rw [guards_eval] at l2 ⊢
  by_cases hg : [ovf].any (fun g => g.eval ρ != 0) = true
  · rw [if_pos hg] at l2 ⊢
    cases r2 <;> simp only [LeafRel] at l2
    have hl2 := evalList_cons_stop (rest := [.block [s3, loop]]) h2' (fun _ h => by cases h)
    have hb2 := eval_block_of hl2
    have hl1 := evalList_cons_stop (rest := []) hb2 (fun _ h => by cases h)
    exact ⟨_, eval_block_of ((evalList_cons_normal h1').trans hl1), l2⟩
  rw [if_neg hg] at l2 ⊢
  simp only [Br.eval] at l2 ⊢
  by_cases hv : le.eval ρ = 0
  · rw [if_pos hv] at l2 ⊢
    cases r2 <;> simp only [LeafRel] at l2
    have hl2 := evalList_cons_stop (rest := [.block [s3, loop]]) h2' (fun _ h => by cases h)
    have hb2 := eval_block_of hl2
    have hl1 := evalList_cons_stop (rest := []) hb2 (fun _ h => by cases h)
    exact ⟨_, eval_block_of ((evalList_cons_normal h1').trans hl1), l2⟩
  rw [if_neg hv] at l2 ⊢
  obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
  have h0 := hok.word 0
  have hn := nOf_lt ρ
  have hpre := require_passed ρ hok hg hv
  have hlim0 : ρ.store 1 < Generic.wordSize := hok.word 1
  -- uint256 i = 0
  obtain ⟨r3, h3, l3⟩ := eval_stmt ρ E ctx 10 s3 S0.push.push.push _ (e3 ev tbl) rt2.pushScope
    hrel2.pushScope
  obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
  have h3' := eval_mono (by omega : 10 ≤ f + 1) h3
  -- initiation: the header at i = 0
  have hrelh : StmtRel (hval ρ 0 (ρ.store 0 + 0)) E ctx rt3.pushScope headerS := by
    refine StmtRel.congr hrel3.pushScope hrel3.hash hok (Facts.hold_nil _) ?_ ?_ rfl
    · simp [SymState.push, S0, headerS, frameOf, WExpr.eval, hval]
    · intro k hk
      simp only [Writes.store, SymState.push, S0, headerS]
      split_ifs with hk0
      · simp only [WExpr.eval, hval, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero] at hk0 ⊢
        rw [Nat.mod_eq_of_lt hk] at hk0
        rw [← hk0, Nat.mod_eq_of_lt h0, Nat.zero_mod]
      · rfl
  have hskip : Stmt.eval 1 E.tbl ctx rt3.pushScope .skip = .done (.ok (.normal rt3.pushScope)) := by
    rw [Stmt.eval]; rfl
  have hm0 : m (hval ρ 0 (ρ.store 0 + 0)) < 2 ^ 256 := by
    obtain ⟨z0, z1, z2⟩ := hval_args ρ 0 (ρ.store 0 + 0) (by decide) (by omega)
    simp only [m, z0, z1, z2]
    omega
  -- the loop, by the generic bridge
  obtain ⟨r, hr, hq⟩ := forLoop_of_erased (obl_vc ev tbl ρ ctx hok hpre) hskip
    ⟨0, ρ.store 0 + 0, by decide, by omega, rfl, init_vc (ρ.store 0) (ρ.store 1) (nOf ρ) (hok.word 0) hlim0 hn hpre⟩ hrelh (f + 1) (by omega) (by omega)
  obtain ⟨rtx, rfl, hrelx⟩ := hq
  have hr' : Stmt.eval (f + 1) E.tbl ctx rt3 loop = .done (.ok (.normal rtx.popScope)) := hr
  have hl3 : Stmt.evalList (f + 1) E.tbl ctx rt2.pushScope [s3, loop] =
      .done (.ok (.normal rtx.popScope)) := by
    rw [evalList_cons_normal h3', evalList_cons_normal hr', evalList_nil]
  have hb3 : Stmt.eval (f + 2) E.tbl ctx rt2 (.block [s3, loop]) = _ := eval_block_of hl3
  have hl2 : Stmt.evalList (f + 2) E.tbl ctx rt1.pushScope [s2, .block [s3, loop]] =
      .done (.ok (.normal rtx.popScope.popScope)) := by
    rw [evalList_cons_normal h2', evalList_cons_normal hb3, evalList_nil]
  have hb2 : Stmt.eval (f + 3) E.tbl ctx rt1 (.block [s2, .block [s3, loop]]) = _ :=
    eval_block_of hl2
  have hl1 : Stmt.evalList (f + 3) E.tbl ctx rt.pushScope [s1, .block [s2, .block [s3, loop]]] =
      .done (.ok (.normal rtx.popScope.popScope.popScope)) := by
    rw [evalList_cons_normal h1', evalList_cons_normal hb2, evalList_nil]
  exact ⟨_, eval_block_of hl1, hrelx.popScope.popScope.popScope.popScope⟩

/-- info: 'Contracts.VerifyCounter.LoopVC.body_runs_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_runs_vc

end Contracts.VerifyCounter.LoopVC
