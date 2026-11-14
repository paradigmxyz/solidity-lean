import Contracts.VerifyCounter.SourceLoop
import SolidCore.Refinement.Generic.LoopRun

/-!
# bump's body in SolidCore runs to its tree, the loop by its ranking certificate

`bumpBody` is `bump(n)`'s body as SolidCore's type checker leaves it (see `SourceAst.lean` and
`Source.lean`, where the kernel checks that the checked contract's `bump` has this body):

    { n = n; { require(count + n <= limit, "over"); { uint256 i = 0; for (; i < n; i++) { count++; } } } }

`body_runs` is `BodyRuns` of it, for the tree `bumpBr`: `Panic(0x11)` when `count + n` wraps,
`Error("over")` when it exceeds `limit`, and otherwise success with slot 0 holding `count + n` and
nothing else written. The statements around the loop run as their erasure (`eval_stmt`); the loop
runs by its ranking certificate (`SourceLoop.cert`, `forLoop_of_cert`) at every fuel from
`2 ^ 256 + 8` on: the rank `n - i` is below `2 ^ 256`, and each iteration spends one unit.
-/

namespace Contracts.VerifyCounter.Source
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- A `uint256` storage field filling its slot, as the type checker leaves `count` and `limit`. -/
def wordField (name : String) (slot : Nat) : StorageField :=
  { name := name, slot := slot, ty? := some Ty.uint256, layout? := some (StorageLayout.scalar Ty.uint256),
    transient := false, packedOffset := 0, packedBytes := 32, packedSigned := false }

/-- `Counter`'s storage fields. -/
def vcFields : List StorageField := [wordField "count" 0, wordField "limit" 1]

def s1 : Stmt := .assign (.var "n") (.castOp .uintCleanup 256 (.var "n"))

def s2 : Stmt :=
  .requireStmt
    (.binary .le
      (.castOp .uintCleanup 256 (.castOp .uintCleanup 256
        (.binary .add (.castOp .uintCleanup 256 (.storageRead .ref "count" []))
          (.castOp .uintCleanup 256 (.var "n")))))
      (.castOp .uintCleanup 256 (.storageRead .ref "limit" [])))
    (some "over")

def s3 : Stmt := .varDecl .uint256 "i" (some (.word 0))

def loop : Stmt := .forLoop .skip cond post body

/-- **bump's body.** -/
def bumpBody : Stmt := .block [s1, .block [s2, .block [s3, loop]]]

/-- The first symbolic state of a call of `bump`: `n` is argument 0. -/
def S0 : SymState := { scopes := [[("n", .arg 0)]], writes := [], logs := [] }

/-- `count + n` wraps. -/
def ovf : WExpr := .bin .lt (.bin .add (.init 0) (.arg 0)) (.init 0)

/-- `count + n <= limit`. -/
def le : WExpr := .un .iszero (.bin .gt (.bin .add (.init 0) (.arg 0)) (.init 1))

/-- The state at the end of the body: slot 0 holds `count + n`. -/
def SF : SymState :=
  { scopes := [[("n", .arg 0)]], writes := [(.lit 0, .bin .add (.init 0) (.arg 0))], logs := [] }

/-- **bump's tree of leaves.** -/
def bumpBr : Br := guards [ovf] (.ite le (.leaf (.normal SF)) (.leaf (.reverted (.error "over"))))

/-- The erasure environment of bump's body. -/
def env (ev : List EventDecl) (tbl : FunctionTable) : EraseEnv :=
  { fields := vcFields, events := ev, tbl := tbl, facts := [] }

theorem e1 (ev : List EventDecl) (tbl : FunctionTable) :
    eraseStmt (env ev tbl) 10 s1 S0.push = some (.leaf (.normal S0.push)) := rfl

theorem e2 (ev : List EventDecl) (tbl : FunctionTable) :
    eraseStmt (env ev tbl) 10 s2 S0.push.push =
      some (guards [ovf] (.ite le (.leaf (.normal S0.push.push)) (.leaf (.reverted (.error "over"))))) :=
  rfl

theorem e3 (ev : List EventDecl) (tbl : FunctionTable) :
    eraseStmt (env ev tbl) 10 s3 S0.push.push.push =
      some (.leaf (.normal { S0.push.push.push with scopes := [[("i", .lit 0)], [], [], [("n", .arg 0)]] })) :=
  rfl

theorem leaf_normal {ρ : Val} {E : EraseEnv} {ctx : Context} {r : Result} {S : SymState}
    (h : LeafRel ρ E ctx r (.normal S)) : ∃ rt, r = .normal rt ∧ StmtRel ρ E ctx rt S := by
  cases r <;> simp only [LeafRel] at h
  exact ⟨_, rfl, h⟩

/-- What the `require` passing says: `count + n` does not wrap and is at most `limit`. -/
theorem require_passed (ρ : Val) (hok : ρ.Ok) (hg : ¬([ovf].any (fun g => g.eval ρ != 0) = true))
    (hv : ¬le.eval ρ = 0) : ρ.store 0 + nOf ρ ≤ ρ.store 1 := by
  have h0 := hok.word 0
  have h1w := hok.word 1
  have hn := nOf_lt ρ
  have hg' : ovf.eval ρ = 0 := by
    simpa [bne_iff_ne] using hg
  have eovf : ovf.eval ρ = if (ρ.store 0 + nOf ρ) % Generic.wordSize < ρ.store 0 then 1 else 0 := by
    simp only [ovf, nOf, WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt h0, Nat.mod_mod]
    by_cases h : (ρ.store 0 + ρ.args.getD 0 0 % Generic.wordSize) % Generic.wordSize < ρ.store 0 <;>
      simp only [h, ↓reduceIte] <;> decide
  have ele : le.eval ρ = if ρ.store 1 < (ρ.store 0 + nOf ρ) % Generic.wordSize then 0 else 1 := by
    simp only [le, nOf, WExpr.eval, BinOp.eval, UnOp.eval, Nat.mod_eq_of_lt h0,
      Nat.mod_eq_of_lt h1w, Nat.mod_mod]
    by_cases h : ρ.store 1 < (ρ.store 0 + ρ.args.getD 0 0 % Generic.wordSize) % Generic.wordSize <;>
      simp only [h, ↓reduceIte] <;> decide
  have hw : ρ.store 0 + nOf ρ < Generic.wordSize := by
    by_contra hc
    have : (ρ.store 0 + nOf ρ) % Generic.wordSize < ρ.store 0 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [eovf, if_pos this] at hg'; cases hg'
  rw [ele, Nat.mod_eq_of_lt hw] at hv
  split at hv
  · exact absurd rfl hv
  · omega

set_option maxHeartbeats 4000000 in
/-- **bump's body runs to `bumpBr`**, at every fuel from `2 ^ 256 + 8` on. -/
theorem body_runs (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef)
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
  · -- count + n wraps: Panic(0x11)
    rw [if_pos hg] at l2 ⊢
    cases r2 <;> simp only [LeafRel] at l2
    rename_i rt2 e
    have hl2 := evalList_cons_stop (rest := [.block [s3, loop]]) h2' (fun _ h => by cases h)
    have hb2 := eval_block_of hl2
    have hl1 := evalList_cons_stop (rest := []) hb2 (fun _ h => by cases h)
    exact ⟨_, eval_block_of ((evalList_cons_normal h1').trans hl1), l2⟩
  rw [if_neg hg] at l2 ⊢
  simp only [Br.eval] at l2 ⊢
  by_cases hv : le.eval ρ = 0
  · -- count + n > limit: Error("over")
    rw [if_pos hv] at l2 ⊢
    cases r2 <;> simp only [LeafRel] at l2
    have hl2 := evalList_cons_stop (rest := [.block [s3, loop]]) h2' (fun _ h => by cases h)
    have hb2 := eval_block_of hl2
    have hl1 := evalList_cons_stop (rest := []) hb2 (fun _ h => by cases h)
    exact ⟨_, eval_block_of ((evalList_cons_normal h1').trans hl1), l2⟩
  rw [if_neg hv] at l2 ⊢
  obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
  -- the require passed: count + n does not wrap and is at most limit
  have h0 := hok.word 0
  have h1w := hok.word 1
  have hn := nOf_lt ρ
  have hpre := require_passed ρ hok hg hv
  -- uint256 i = 0
  obtain ⟨r3, h3, l3⟩ := eval_stmt ρ E ctx 10 s3 S0.push.push.push _ (e3 ev tbl) rt2.pushScope
    hrel2.pushScope
  obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
  have h3' := eval_mono (by omega : 10 ≤ f + 1) h3
  -- the loop, by its ranking certificate
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
  have hinv : Inv ρ E ctx rt3.pushScope := ⟨0, Nat.zero_le _, hrelh⟩
  obtain ⟨r, hr, hq⟩ := forLoop_of_cert (cert ρ E ctx rfl rfl hpre) hskip hinv (f + 1)
    (by have hn2 : nOf ρ < 2 ^ 256 := hn; rw [rank_of hrelh (by decide)]; omega) (by omega)
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

/-- info: 'Contracts.VerifyCounter.Source.body_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_runs

end Contracts.VerifyCounter.Source
