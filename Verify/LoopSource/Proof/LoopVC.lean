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

include hc0 hlim hn hpre in
/-- **The loop's arithmetic, from solar-verify's obligations**: initiation, the exit, consecution
and the measure's fall are `init_vc`, `post_vc`, `consec_vc` and `decr_vc`. -/
theorem arith_vc : Arith c0 n :=
  ⟨init_vc c0 lim n hc0 hlim hn hpre,
    fun i cnt hi hcnt hI hC hge => post_vc c0 lim n i cnt hc0 hlim hn hi hcnt hpre hI hC hge,
    fun i cnt hi hcnt hI hC hlt => consec_vc c0 lim n i cnt hc0 hlim hn hi hcnt hpre hI hC hlt,
    fun i cnt hi hcnt hI hC hlt => decr_vc c0 lim n i cnt hc0 hlim hn hi hcnt hpre hI hC hlt⟩

/-- **The loop's obligations hold**, from solar-verify's obligations (`arith_vc`). -/
theorem obl_vc (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (ctx : Context) (hok : ρ.Ok)
    (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    ForObl 3 (env ev tbl) ctx cond post body headerS (P ρ) m (Q ρ (env ev tbl) ctx) c bb :=
  obl_of ev tbl ρ ctx hok hpre (arith_vc _ _ _ (hok.word 0) (hok.word 1) (nOf_lt ρ) hpre)

/-- **bump's body runs to `bumpBr`**, the loop's arithmetic from solar-verify's obligations
(`arith_vc`), the loop by the generic bridge, at every fuel from `2 ^ 256 + 8` on. -/
theorem body_runs_vc (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef)
    (hbody : fn.body = bumpBody) (hinit : initState fn = S0) (fuel : Nat)
    (hfuel : 2 ^ 256 + 8 ≤ fuel) : BodyRuns (env ev tbl) fuel fn bumpBr :=
  body_runs_of ev tbl fn hbody hinit fuel hfuel fun ρ hok hpre =>
    arith_vc _ _ _ (hok.word 0) (hok.word 1) (nOf_lt ρ) hpre

/-- info: 'Contracts.VerifyCounter.LoopVC.body_runs_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_runs_vc

end Contracts.VerifyCounter.LoopVC
