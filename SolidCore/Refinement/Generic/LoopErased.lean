import SolidCore.Refinement.Generic.LoopStmt
import SolidCore.Refinement.Generic.LoopSeq

/-!
# Ranking certificates of loops from obligations over erased words

`ForCert` and `WhileCert` (`Loop.lean`) are statements about SolidCore's interpreter: from every
runtime of an invariant the condition evaluates, the body and the update run, and the loop either ends
in `Q` or comes back to the invariant with a smaller rank. This file proves them, for any loop whose
condition, body and update the generic source stage erases (`eraseExpr`, `eraseStmt`, loop-free),
from obligations that mention no runtime and no interpreter: facts about the erased words at a
**header valuation** `σ`.

The header is a symbolic state `H` (`SymState`) whose words for what the loop changes are fresh:
`σ` assigns them. A loop is given by `H`, an invariant `P` of header valuations and a measure
`m` of them, and its obligations (`ForObl` / `WhileObl`) are:

* the condition erases at `H` to a word `c` with no overflow guard, and the body runs as a tree of
  leaves at `H` (and, for `for`, the update at every normal end of the body): `StmtRuns`, which
  the generic stage's erasure gives (`stmtRuns_of_erase`), as do the loop fragment's increments
  `x++` on a local or a storage word (`stmtRuns_incVar`, `stmtRuns_incField`, which the erasure
  has no arm for) and a block of one such statement (`stmtRuns_block1`);
* **exit**: at `σ` of `P` where `c` is 0, every runtime `H` shows at `σ` ends the loop in `Q`;
* **iteration**: at `σ` of `P` where `c` is not 0, the leaf the body (and update) take at `σ`
  either ends the loop (a return or a revert: every result it shows meets `Q`) or comes back to the
  header: some `σ'` of `P` with `m σ' < m σ` such that every runtime the leaf's state shows at
  `σ` is one `H` shows at `σ'` (**preservation** and the **rank's fall**).

`forCert_of_erased` / `whileCert_of_erased` turn them into the certificates, with the invariant
`HeadInv` (some `σ` of `P` relates the runtime to `H`) and the rank `headRank` (the least `m σ`
over those `σ`, so that no choice of `σ` can raise it). The interpreter's runs of the condition,
body and update are the generic stage's own theorems (`eval_eq`, `eval_stmt`); nothing about the
loop is assumed. `forLoop_of_erased` adds the entry (**initiation**: the state before the loop
shows some `σ0` of `P` at `H`) and ends the `for` statement in `Q` from fuel `m σ0 + k + 2`.

What a loop needs that is not here: a body or update with a nested loop, an internal call the
stage does not erase, or a `break`/`continue` (no leaf says either) has no `StmtRuns`, so it has no
obligations of this form. The obligations are facts about words; tying them to
solar-verify's SMT obligations (`Verify.Obligation`) is a separate binding.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-- Some `n` of `p` is least. -/
theorem exists_least {p : Nat → Prop} (h : ∃ n, p n) : ∃ n, p n ∧ ∀ k, p k → n ≤ k := by
  obtain ⟨n, hn⟩ := h
  refine Nat.strongRecOn (motive := fun n => p n → ∃ n, p n ∧ ∀ k, p k → n ≤ k) n ?_ hn
  intro n ih hn
  by_cases hm : ∃ k, k < n ∧ p k
  · obtain ⟨k, hk, hpk⟩ := hm
    exact ih k hk hpk
  · exact ⟨n, hn, fun k hk => Nat.le_of_not_lt fun hlt => hm ⟨k, hlt, hk⟩⟩

/-- **The loop's invariant at its header**: some header valuation of `P` relates the runtime to
`H`. -/
def HeadInv (E : EraseEnv) (ctx : Context) (H : SymState) (P : Val → Prop) (rt : Runtime) : Prop :=
  ∃ σ, P σ ∧ StmtRel σ E ctx rt H

/-- `n` is the measure of a header valuation of `P` that relates the runtime to `H`. -/
def RankAt (E : EraseEnv) (ctx : Context) (H : SymState) (P : Val → Prop) (m : Val → Nat)
    (rt : Runtime) (n : Nat) : Prop :=
  ∃ σ, P σ ∧ StmtRel σ E ctx rt H ∧ m σ = n

open Classical in
/-- **The loop's rank at its header**: the least measure over the valuations `HeadInv` names. -/
noncomputable def headRank (E : EraseEnv) (ctx : Context) (H : SymState) (P : Val → Prop)
    (m : Val → Nat) (rt : Runtime) : Nat :=
  if h : ∃ n, RankAt E ctx H P m rt n then Classical.choose (exists_least h) else 0

theorem headRank_spec {E : EraseEnv} {ctx : Context} {H : SymState} {P : Val → Prop}
    {m : Val → Nat} {rt : Runtime} (h : HeadInv E ctx H P rt) :
    ∃ σ, P σ ∧ StmtRel σ E ctx rt H ∧ m σ = headRank E ctx H P m rt := by
  obtain ⟨σ, hp, hr⟩ := h
  have he : ∃ n, RankAt E ctx H P m rt n := ⟨m σ, σ, hp, hr, rfl⟩
  unfold headRank
  rw [dif_pos he]
  exact (Classical.choose_spec (exists_least he)).1

theorem headRank_le {E : EraseEnv} {ctx : Context} {H : SymState} {P : Val → Prop}
    {m : Val → Nat} {rt : Runtime} {σ : Val} (hp : P σ) (hr : StmtRel σ E ctx rt H) :
    headRank E ctx H P m rt ≤ m σ := by
  have he : ∃ n, RankAt E ctx H P m rt n := ⟨m σ, σ, hp, hr, rfl⟩
  unfold headRank
  rw [dif_pos he]
  exact (Classical.choose_spec (exists_least he)).2 _ ⟨σ, hp, hr, rfl⟩

/-- **`s` runs as the tree `b` from `S`** with fuel `n`: from every runtime `S` shows at a valuation,
the interpreter ends `s` in a result the leaf `b` takes there shows. -/
def StmtRuns (E : EraseEnv) (n : Nat) (ctx : Context) (s : Stmt) (S : SymState) (b : Br) : Prop :=
  ∀ σ rt, StmtRel σ E ctx rt S →
    ∃ r, Stmt.eval n E.tbl ctx rt s = .done (.ok r) ∧ LeafRel σ E ctx r (b.eval σ)

/-- An erased statement runs as its erasure. -/
theorem stmtRuns_of_erase {E : EraseEnv} {n : Nat} {ctx : Context} {s : Stmt} {S : SymState}
    {b : Br} (h : eraseStmt E n s S = some b) : StmtRuns E n ctx s S b :=
  fun σ rt hrel => eval_stmt σ E ctx n s S b h rt hrel

/-- `x++` on a local word runs as `incVarBr`. -/
theorem stmtRuns_incVar {E : EraseEnv} {ctx : Context} {S : SymState} (n : Nat) (pst : Bool)
    {x : String} {old : WExpr} {L' : Scopes} (hold : Scopes.get? S.scopes x = some old)
    (hL : Scopes.set S.scopes x (.bin .add old (.lit 1)) = some L') :
    StmtRuns E (n + 1) ctx (.exprStmt (.incDec .add pst (some (.uint 256)) (.var x))) S
      (incVarBr old L' S) :=
  fun σ rt hrel => eval_incVar σ E ctx rt S hrel n pst hold hL

/-- `x++` on a word storage field runs as `incFieldBr`. -/
theorem stmtRuns_incField {E : EraseEnv} {ctx : Context} {S : SymState} (n : Nat) (pst : Bool)
    {x : String} {k off bytes : Nat} (hk : fieldOf? E.fields x = some (k, off, bytes)) :
    StmtRuns E (n + 1) ctx (.exprStmt (.incDec .add pst (some (.uint 256)) (.storageRead .header x [])))
      S (incFieldBr k off bytes S) :=
  fun σ rt hrel => eval_incField σ E ctx rt S hrel n pst hk

/-- A block of one statement runs as the statement's tree in a new scope, popped. -/
theorem stmtRuns_block1 {E : EraseEnv} {n : Nat} {ctx : Context} {s : Stmt} {S : SymState} {b : Br}
    (h : StmtRuns E n ctx s S.push b) :
    StmtRuns E (n + 1) ctx (.block [s]) S (b.mapS SymState.pop) := by
  intro σ rt hrel
  obtain ⟨r, hr, hl⟩ := h σ rt.pushScope hrel.pushScope
  have hlist : Stmt.evalList n E.tbl ctx rt.pushScope [s] = .done (.ok r) := by
    cases r with
    | normal rb => rw [evalList_cons_normal hr, evalList_nil]
    | _ => exact evalList_cons_stop hr (fun _ h => by cases h)
  refine ⟨_, eval_block_of hlist, ?_⟩
  rw [Br.eval_mapS]
  exact hl.popScope

/-- A leaf that ends the loop: every result it shows at `σ` meets `Q`. -/
def Ends (σ : Val) (E : EraseEnv) (ctx : Context) (Q : Result → Prop) (l : Leaf) : Prop :=
  ∀ r, LeafRel σ E ctx r l → Q r

/-- Back at the header: `S` at `σ` is `H` at some `σ'` of `P` of smaller measure. -/
def Back (E : EraseEnv) (ctx : Context) (H : SymState) (P : Val → Prop) (m : Val → Nat)
    (σ : Val) (S : SymState) : Prop :=
  ∃ σ', P σ' ∧ m σ' < m σ ∧ ∀ rt, StmtRel σ E ctx rt S → StmtRel σ' E ctx rt H

/-- What the last leaf of an iteration owes: back at the header when normal, else `Q`. -/
def IterEnd (E : EraseEnv) (ctx : Context) (H : SymState) (P : Val → Prop) (m : Val → Nat)
    (Q : Result → Prop) (σ : Val) : Leaf → Prop
  | .normal S => Back E ctx H P m σ S
  | .returned S vs => Ends σ E ctx Q (.returned S vs)
  | .reverted f => Ends σ E ctx Q (.reverted f)

/-- What the body's leaf of a `for` iteration owes: when normal, the update runs as a tree there and its
leaf owes `IterEnd`; else `Q`. -/
def ForBody (k : Nat) (E : EraseEnv) (ctx : Context) (post : Stmt) (H : SymState)
    (P : Val → Prop) (m : Val → Nat) (Q : Result → Prop) (σ : Val) : Leaf → Prop
  | .normal S => ∃ pb, StmtRuns E k ctx post S pb ∧ IterEnd E ctx H P m Q σ (pb.eval σ)
  | .returned S vs => Ends σ E ctx Q (.returned S vs)
  | .reverted f => Ends σ E ctx Q (.reverted f)

/-- **The obligations of `for (…; cnd; post) body`** at the header `H`, with the invariant `P` and the
measure `m` of header valuations, the erased condition `c` and the body's tree `bb`. -/
structure ForObl (k : Nat) (E : EraseEnv) (ctx : Context) (cnd : Expr) (post body : Stmt)
    (H : SymState) (P : Val → Prop) (m : Val → Nat) (Q : Result → Prop) (c : WExpr) (bb : Br) :
    Prop where
  cond_erase : eraseExpr E.fields H cnd = some ([], c)
  body_runs : StmtRuns E k ctx body H bb
  exit : ∀ σ rt, P σ → StmtRel σ E ctx rt H → c.eval σ = 0 → Q (.normal rt)
  iter : ∀ σ, P σ → c.eval σ ≠ 0 → ForBody k E ctx post H P m Q σ (bb.eval σ)

/-- **The obligations of `while (cnd) body`**. -/
structure WhileObl (k : Nat) (E : EraseEnv) (ctx : Context) (cnd : Expr) (body : Stmt)
    (H : SymState) (P : Val → Prop) (m : Val → Nat) (Q : Result → Prop) (c : WExpr) (bb : Br) :
    Prop where
  cond_erase : eraseExpr E.fields H cnd = some ([], c)
  body_runs : StmtRuns E k ctx body H bb
  exit : ∀ σ rt, P σ → StmtRel σ E ctx rt H → c.eval σ = 0 → Q (.normal rt)
  iter : ∀ σ, P σ → c.eval σ ≠ 0 → IterEnd E ctx H P m Q σ (bb.eval σ)

theorem wordTruthy_of_lt {w : Nat} (h : w < wordSize) : wordTruthy w = !(w == 0) := by
  have h' : w % SolidCore.Solidity.Shared.wordModulus = w := Nat.mod_eq_of_lt h
  simp only [wordTruthy, SolidCore.Solidity.Shared.norm, h']

/-- The condition of a loop at a header runtime: it evaluates to the erased word, with no revert. -/
theorem condStep_of_erased {E : EraseEnv} {ctx : Context} {H : SymState} {cnd : Expr} {c : WExpr}
    {σ : Val} {rt : Runtime} (hc : eraseExpr E.fields H cnd = some ([], c))
    (hrel : StmtRel σ E ctx rt H) {Q : Result → Prop} {Go : Runtime → Prop}
    (hgo : c.eval σ ≠ 0 → Go rt) (hq : c.eval σ = 0 → Q (.normal rt)) :
    CondStep ctx cnd rt Q Go := by
  have hev := eval_eq σ E.fields ctx rt H hrel.expr hc
  refine ⟨.ok (.word (c.eval σ), rt), ?_, ?_⟩
  · rw [hev, caught_exprResult]
    simp
  dsimp only [Value.expectWord]
  rw [wordTruthy_norm, wordTruthy_of_lt (WExpr.eval_lt σ c)]
  by_cases hz : c.eval σ = 0
  · simp only [hz, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hq hz
  · have : (c.eval σ == 0) = false := by simpa using hz
    simp only [this, Bool.not_false, ↓reduceIte]
    exact hgo hz

/-- **A `for` loop whose obligations hold has a ranking certificate.** -/
theorem forCert_of_erased {k : Nat} {E : EraseEnv} {ctx : Context} {cnd : Expr} {post body : Stmt}
    {H : SymState} {P : Val → Prop} {m : Val → Nat} {Q : Result → Prop} {c : WExpr} {bb : Br}
    (h : ForObl k E ctx cnd post body H P m Q c bb) :
    ForCert k E.tbl ctx cnd post body (HeadInv E ctx H P) (headRank E ctx H P m) Q := by
  constructor
  intro rt hinv
  obtain ⟨σ, hp, hrel, hm⟩ := headRank_spec (m := m) hinv
  refine condStep_of_erased h.cond_erase hrel ?_ (h.exit σ rt hp hrel)
  intro hz
  obtain ⟨r1, h1, hl1⟩ := h.body_runs σ rt hrel
  refine ⟨r1, h1, ?_⟩
  have hit := h.iter σ hp hz
  generalize bb.eval σ = l at hl1 hit
  cases l with
  | normal S1 =>
    cases r1 <;> simp only [LeafRel] at hl1
    rename_i rb
    obtain ⟨pb, hpb, hend⟩ := hit
    obtain ⟨r2, h2, hl2⟩ := hpb σ rb hl1
    refine ⟨r2, h2, ?_⟩
    generalize pb.eval σ = l2 at hl2 hend
    cases l2 with
    | normal S2 =>
      cases r2 <;> simp only [LeafRel] at hl2
      rename_i rp
      obtain ⟨σ', hp', hlt, htr⟩ := hend
      have hrp := htr rp hl2
      exact ⟨⟨σ', hp', hrp⟩, by have := headRank_le (m := m) hp' hrp; omega⟩
    | returned S2 vs =>
      cases r2 <;> simp only [LeafRel] at hl2
      exact hend _ hl2
    | reverted f =>
      cases r2 <;> simp only [LeafRel] at hl2
      exact hend _ hl2
  | returned S1 vs =>
    cases r1 <;> simp only [LeafRel] at hl1
    exact hit _ hl1
  | reverted f =>
    cases r1 <;> simp only [LeafRel] at hl1
    exact hit _ hl1

/-- **A `while` loop whose obligations hold has a ranking certificate.** -/
theorem whileCert_of_erased {k : Nat} {E : EraseEnv} {ctx : Context} {cnd : Expr} {body : Stmt}
    {H : SymState} {P : Val → Prop} {m : Val → Nat} {Q : Result → Prop} {c : WExpr} {bb : Br}
    (h : WhileObl k E ctx cnd body H P m Q c bb) :
    WhileCert k E.tbl ctx cnd body (HeadInv E ctx H P) (headRank E ctx H P m) Q := by
  constructor
  intro rt hinv
  obtain ⟨σ, hp, hrel, hm⟩ := headRank_spec (m := m) hinv
  refine condStep_of_erased h.cond_erase hrel ?_ (h.exit σ rt hp hrel)
  intro hz
  obtain ⟨r1, h1, hl1⟩ := h.body_runs σ rt hrel
  refine ⟨r1, h1, ?_⟩
  have hend := h.iter σ hp hz
  generalize bb.eval σ = l at hl1 hend
  cases l with
  | normal S1 =>
    cases r1 <;> simp only [LeafRel] at hl1
    rename_i rp
    obtain ⟨σ', hp', hlt, htr⟩ := hend
    have hrp := htr rp hl1
    exact ⟨⟨σ', hp', hrp⟩, by have := headRank_le (m := m) hp' hrp; omega⟩
  | returned S1 vs =>
    cases r1 <;> simp only [LeafRel] at hl1
    exact hend _ hl1
  | reverted f =>
    cases r1 <;> simp only [LeafRel] at hl1
    exact hend _ hl1

/-- **A `for` statement whose obligations hold ends in `Q`**, from a runtime `rt` whose `init`
(fuel `k0`) ends normally in a runtime the header shows at some `σ0` of `P` (initiation), at every
fuel from `m σ0 + k + 2` and `k0 + 1` on. -/
theorem forLoop_of_erased {k k0 : Nat} {E : EraseEnv} {ctx : Context} {init : Stmt} {cnd : Expr}
    {post body : Stmt} {H : SymState} {P : Val → Prop} {m : Val → Nat} {Q : Result → Prop}
    {c : WExpr} {bb : Br} (h : ForObl k E ctx cnd post body H P m Q c bb) {rt rt1 : Runtime}
    (hinit : Stmt.eval k0 E.tbl ctx rt.pushScope init = .done (.ok (.normal rt1)))
    {σ0 : Val} (hp0 : P σ0) (hrel0 : StmtRel σ0 E ctx rt1 H) (fuel : Nat)
    (hf : m σ0 + k + 2 ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel E.tbl ctx rt (.forLoop init cnd post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) ∧ Q r :=
  forLoop_of_cert (forCert_of_erased h) hinit ⟨σ0, hp0, hrel0⟩ fuel
    (by have := headRank_le (m := m) hp0 hrel0; omega) hk0

/-- **A `while` statement whose obligations hold ends in `Q`**, from a runtime the header shows
at some `σ0` of `P` (initiation), at every fuel from `m σ0 + k + 2` on. -/
theorem whileLoop_of_erased {k : Nat} {E : EraseEnv} {ctx : Context} {cnd : Expr} {body : Stmt}
    {H : SymState} {P : Val → Prop} {m : Val → Nat} {Q : Result → Prop} {c : WExpr} {bb : Br}
    (h : WhileObl k E ctx cnd body H P m Q c bb) {rt : Runtime} {σ0 : Val} (hp0 : P σ0)
    (hrel0 : StmtRel σ0 E ctx rt H) (fuel : Nat) (hf : m σ0 + k + 2 ≤ fuel) :
    ∃ r, Stmt.eval fuel E.tbl ctx rt (.whileLoop cnd body) = .done (.ok r) ∧ Q r :=
  whileLoop_of_cert (whileCert_of_erased h) ⟨σ0, hp0, hrel0⟩ fuel
    (by have := headRank_le (m := m) hp0 hrel0; omega)

/-- info: 'SolidCore.Refinement.Generic.Loop.forCert_of_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forCert_of_erased

/-- info: 'SolidCore.Refinement.Generic.Loop.whileCert_of_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whileCert_of_erased

/-- info: 'SolidCore.Refinement.Generic.Loop.forLoop_of_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forLoop_of_erased

/-- info: 'SolidCore.Refinement.Generic.Loop.whileLoop_of_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whileLoop_of_erased

end SolidCore.Refinement.Generic.Loop
