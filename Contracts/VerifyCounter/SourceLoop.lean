import SolidCore.Refinement.Generic.LoopStmt
import SolidCore.Refinement.Generic.LoopSeq

/-!
# bump's loop in SolidCore: a ranking certificate

`bump(n)` of solar-verify's `Counter` (crates/verify/examples/Counter.sol),

    require(count + n <= limit, "over");
    for (uint256 i = 0; i < n; i++) { count++; }

as SolidCore's type checker leaves it (`bumpBody`, from `Contracts/VerifyCounter/SourceAst.lean`).
The loop's certificate (`cert`) is solar-verify's inferred invariant and measure for this loop,
`i <= n`, `count == old(count) + i` and `n - i`, stated of SolidCore's runtime at the header
(`Inv`, `rank`): the runtime is related (`StmtRel`) to the header state `headerS` whose words for
`n`, `i` and `count` are fresh (arguments 0, 1 and 2 of `hval ρ i (count0 + i)`). Each iteration is
run by SolidCore's interpreter (`eval_incField`, `eval_incVar`): the overflow guards of `count++`
and `i++` are false under the invariant and the `require`, the invariant comes back with `i + 1`,
and the rank falls by one; on exit `i = n` and `count` is `old(count) + n` (`exitS`).
-/

namespace Contracts.VerifyCounter.Source
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- The loop's condition, `i < n`. -/
def cond : Expr := .binary .lt (.castOp .uintCleanup 256 (.var "i")) (.castOp .uintCleanup 256 (.var "n"))

/-- The loop's update, `i++`. -/
def post : Stmt := .exprStmt (.incDec .add true (some (.uint 256)) (.var "i"))

/-- The loop's body, `count++`. -/
def body : Stmt :=
  .block [.exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" []))]

/-- The header state: `n` is argument 0, `i` argument 1 and `count` (slot 0) argument 2. -/
def headerS : SymState :=
  { scopes := [[], [("i", .arg 1)], [], [], [("n", .arg 0)]], writes := [(.lit 0, .arg 2)], logs := [] }

/-- The state at the loop's exit, over the call's words: `i = n`, `count = old(count) + n`. -/
def exitS : SymState :=
  { scopes := [[], [("i", .arg 0)], [], [], [("n", .arg 0)]],
    writes := [(.lit 0, .bin .add (.init 0) (.arg 0))], logs := [] }

/-- The words of the header: the call's `n`, and `i` and `count`. -/
def hval (ρ : Val) (i c : Nat) : Val := ⟨[ρ.args.getD 0 0, i, c], ρ.store, ρ.hash⟩

/-- The call's `n`. -/
def nOf (ρ : Val) : Nat := (WExpr.arg 0).eval ρ

/-- **The invariant** (inferred: `i <= n`, `count == old(count) + i`). -/
def Inv (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) : Prop :=
  ∃ i, i ≤ nOf ρ ∧ StmtRel (hval ρ i (ρ.store 0 + i)) E ctx rt headerS

/-- **The rank** (inferred: `n - i`), read off the runtime's `i`. -/
def rank (ρ : Val) (rt : Runtime) : Nat :=
  match rt.lookupLocal? "i" with
  | some (.word v) => nOf ρ - v
  | _ => 0

/-- What the loop ends in: normally, in the exit state. -/
def Q (ρ : Val) (E : EraseEnv) (ctx : Context) (r : Result) : Prop :=
  ∃ rt, r = .normal rt ∧ StmtRel ρ E ctx rt exitS

/-- The storage fields of `Counter`, as the type checker leaves them. -/
def countOk (E : EraseEnv) : Prop := fieldOf? E.fields "count" = some (0, 0, 32)

theorem nOf_lt (ρ : Val) : nOf ρ < wordSize := WExpr.eval_lt ρ _

theorem rank_of {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {i c : Nat}
    (h : StmtRel (hval ρ i c) E ctx rt headerS) (hi : i < wordSize) : rank ρ rt = nOf ρ - i := by
  have := h.expr.locals "i" (.arg 1) rfl
  simp only [rank, this, WExpr.eval, hval, List.getD_cons_succ, List.getD_cons_zero,
    Nat.mod_eq_of_lt hi]

set_option maxHeartbeats 4000000 in
/-- **bump's loop with any measure R that falls on every iteration is certified**: everything
but the rank's fall is checked here, against SolidCore's interpreter. -/
theorem certWith (ρ : Val) (E : EraseEnv) (ctx : Context) (hcount : countOk E)
    (hfacts : E.facts = []) (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) (R : Runtime → Nat)
    (hR : ∀ i rt rt', i < nOf ρ → StmtRel (hval ρ i (ρ.store 0 + i)) E ctx rt headerS →
      StmtRel (hval ρ (i + 1) (ρ.store 0 + (i + 1))) E ctx rt' headerS → R rt' < R rt) :
    ForCert 3 E.tbl ctx cond post body (Inv ρ E ctx) R (Q ρ E ctx) := by
  constructor
  rintro rt ⟨i, hi, hrel⟩
  have hok : ρ.Ok := hrel.ok
  have hlim : ρ.store 1 < wordSize := hok.word 1
  have hn := nOf_lt ρ
  have hiw : i < wordSize := by omega
  have hcw : ρ.store 0 + i < wordSize := by omega
  have hcond : eraseExpr E.fields headerS cond = some ([], .bin .lt (.arg 1) (.arg 0)) := rfl
  have hev := eval_eq _ E.fields ctx rt headerS hrel.expr hcond
  have hlt : (WExpr.bin .lt (.arg 1) (.arg 0)).eval (hval ρ i (ρ.store 0 + i)) =
      if i < nOf ρ then 1 else 0 := by
    simp only [WExpr.eval, BinOp.eval, hval, List.getD_cons_succ, List.getD_cons_zero,
      Nat.mod_eq_of_lt hiw, nOf]
    by_cases h : i < ρ.args.getD 0 0 % wordSize <;> simp only [h, ↓reduceIte] <;> decide
  refine ⟨.ok (.word (if i < nOf ρ then 1 else 0), rt), ?_, ?_⟩
  · rw [hev, caught_exprResult]
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, hlt]
  dsimp only [Value.expectWord]
  by_cases hin : i < nOf ρ
  · rw [if_pos hin, if_pos (by decide)]
    -- the body: count++ under the header state
    have hk : fieldOf? E.fields "count" = some (0, 0, 32) := hcount
    obtain ⟨r1, h1, hl1⟩ := eval_incField _ E ctx rt.pushScope headerS.push hrel.pushScope 1 true hk
    have hbr : incFieldBr 0 0 32 headerS.push =
        guards [.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)]
          (.leaf (.normal { headerS.push with writes := [(.lit 0, .bin .add (.arg 2) (.lit 1))] })) := rfl
    rw [hbr, guards_eval] at hl1
    have hg : ([WExpr.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)].any
        (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0)) = false := by
      have h1' : ρ.store 0 + i + 1 < wordSize := by omega
      simp [WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hcw, Nat.mod_eq_of_lt h1']
    rw [hg] at hl1
    simp only [Bool.false_eq_true, ↓reduceIte, Br.eval] at hl1
    rcases r1 with rb | ⟨_, _⟩ | _ | ⟨_, _⟩ | _ | _ <;> simp only [LeafRel] at hl1
    have hlist : Stmt.evalList (1 + 1) E.tbl ctx rt.pushScope
        [.exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" []))] =
        .done (.ok (.normal rb)) := by
      rw [evalList_cons_normal h1, evalList_nil]
    have hb := eval_block_of hlist
    refine ⟨_, hb, ?_⟩
    -- the update: i++
    have hrelb := hl1.popScope
    obtain ⟨r2, h2, hl2⟩ := eval_incVar _ E ctx rb.popScope _ hrelb 2 true (x := "i")
      (old := .arg 1) (L' := [[], [("i", .bin .add (.arg 1) (.lit 1))], [], [], [("n", .arg 0)]])
      rfl rfl
    simp only [ForRest, Result.mapRuntime]
    refine ⟨r2, h2, ?_⟩
    have hi1 : i + 1 < wordSize := by omega
    have hg2 : (overflow .add (.arg 1) (.lit 1)).toList.any
        (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0) = false := by
      simp [overflow, WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
    simp only [incVarBr, guards_eval, hg2, Bool.false_eq_true, ↓reduceIte, Br.eval] at hl2
    rcases r2 with rp | ⟨_, _⟩ | _ | ⟨_, _⟩ | _ | _ <;> simp only [LeafRel] at hl2
    have hc1 : ρ.store 0 + (i + 1) < wordSize := by omega
    have hrelp : StmtRel (hval ρ (i + 1) (ρ.store 0 + (i + 1))) E ctx rp headerS := by
      refine StmtRel.congr hl2 hrel.hash hok (by rw [hfacts]; exact Facts.hold_nil _) ?_ ?_ rfl
      · simp [headerS, SymState.pop, SymState.push, frameOf, WExpr.eval, BinOp.eval, hval,
          Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
      · intro k _
        simp only [Writes.store, SymState.pop, SymState.push, headerS, WExpr.eval, BinOp.eval, hval,
          List.getD_cons_succ, List.getD_cons_zero]
        split_ifs
        · rw [Nat.mod_eq_of_lt hcw, show 1 % wordSize = 1 by decide, Nat.mod_mod, ← Nat.add_assoc]
        · rfl
    exact ⟨⟨i + 1, by omega, hrelp⟩, hR i rt rp hin hrel hrelp⟩
  · rw [if_neg hin, if_neg (by decide)]
    have hie : i = nOf ρ := by omega
    refine ⟨rt, rfl, StmtRel.congr hrel hrel.hash hok (by rw [hfacts]; exact Facts.hold_nil _) ?_ ?_ rfl⟩
    · simp [headerS, exitS, frameOf, WExpr.eval, hval, Nat.mod_eq_of_lt hiw, hie, nOf]
    · intro k _
      have h0 := hok.word 0
      have hie' : ρ.args.getD 0 0 % wordSize = i := hie.symm
      simp only [Writes.store, headerS, exitS, WExpr.eval, BinOp.eval, hval, List.getD_cons_succ,
        List.getD_cons_zero]
      by_cases hk0 : 0 % wordSize = k % wordSize <;> simp only [hk0, ↓reduceIte]
      rw [Nat.mod_eq_of_lt h0, hie', Nat.mod_mod]

/-- **bump's loop has a ranking certificate**: the inferred measure `n - i` falls by one on every
iteration. -/
theorem cert (ρ : Val) (E : EraseEnv) (ctx : Context) (hcount : countOk E)
    (hfacts : E.facts = []) (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    ForCert 3 E.tbl ctx cond post body (Inv ρ E ctx) (rank ρ) (Q ρ E ctx) :=
  certWith ρ E ctx hcount hfacts hpre (rank ρ) fun i _ _ hin h h' => by
    have hn := nOf_lt ρ
    rw [rank_of h' (by omega), rank_of h (by omega)]
    omega

/-- info: 'Contracts.VerifyCounter.Source.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cert

end Contracts.VerifyCounter.Source
