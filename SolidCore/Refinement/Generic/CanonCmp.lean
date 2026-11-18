import SolidCore.Refinement.Generic.Simp

/-!
# Comparisons in one spelling

`Tree.canon` (Simp.lean) compares canonical forms with equality, so two trees that agree on every
call but spell a comparison differently are reported as differing. This module adds one more
pass over the canonical form, `Tree.cmpCanon`, which spells every comparison one way:

* `gt a b` is `lt b a`, when neither operand is a constant.
* A strict comparison against a constant is `gt x c`: `lt x k` is `iszero (gt x (k - 1))` (`0` when
  `k = 0`), `lt c x` and `gt x c` are `gt x c` (`0` when `c` is the largest word), and `gt c x` is
  `iszero (gt x (c - 1))` (`0` when `c = 0`). That is the spelling `Facts.bound` reads, so a later
  `Tree.canon` bounds the word on the branch, and a dominated overflow test such as the checked
  add's `lt (x + 1) x` under `lt x max` folds to `0` (`sLt`).
* `eq x max` (either side), for the largest word `max`, is `gt x (max - 1)`.

A branch on `iszero c` then takes the swapped sides (`Tree.canon`'s `splitNeg`), so
`ite (gt x 5) r s` and `ite (lt x 6) s r` meet, and so do the require `lt x max` with its overflow
test and one `eq x max`. Each rewrite keeps a word's value (`WExpr.eval_cmp`), so
`Tree.eval_cmpCanon` and `Tree.eval_of_agree` keep the comparison semantic.

`Tree.agree` is the check a stage would use: the old comparison, or the new one when the old one
fails, so everything the old comparison accepts it accepts.

This is a leaf: nothing imports it at its commit, so it changes no other module's closure. Using it
in a stage changes `Stage.lean` and `StageFrom.lean` (their `t1.canon.beq t2.canon`), and with them every
module that imports them.
-/

namespace SolidCore.Refinement.Generic

/-- A comparison or equality on rewritten operands, in the one spelling. -/
def cmpBin : BinOp → WExpr → WExpr → WExpr
  | .gt, a, .lit c =>
    if c % wordSize = maxWord then .lit 0 else .bin .gt a (.lit (c % wordSize))
  | .gt, .lit c, b =>
    if c % wordSize = 0 then .lit 0 else .un .iszero (.bin .gt b (.lit (c % wordSize - 1)))
  | .gt, a, b => .bin .lt b a
  | .lt, a, .lit k =>
    if k % wordSize = 0 then .lit 0 else .un .iszero (.bin .gt a (.lit (k % wordSize - 1)))
  | .lt, .lit c, b =>
    if c % wordSize = maxWord then .lit 0 else .bin .gt b (.lit (c % wordSize))
  | .eq, a, .lit m =>
    if m % wordSize = maxWord then .bin .gt a (.lit (maxWord - 1)) else .bin .eq a (.lit m)
  | .eq, .lit m, a =>
    if m % wordSize = maxWord then .bin .gt a (.lit (maxWord - 1)) else .bin .eq (.lit m) a
  | op, a, b => .bin op a b

theorem ite01_mod (p : Prop) [Decidable p] {n : Nat} (hn : 1 < n) :
    (if p then 1 else 0 : Nat) % n = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, Nat.mod_eq_of_lt hn]

theorem cmpBin_eval (ρ : Val) (op : BinOp) (a b : WExpr) :
    (cmpBin op a b).eval ρ = (WExpr.bin op a b).eval ρ := by
  have ha := a.eval_lt ρ
  have hb := b.eval_lt ρ
  have hW : (1 : Nat) < wordSize := by decide
  unfold cmpBin
  split <;> (try split) <;>
    simp only [WExpr.eval] at * <;>
    simp only [BinOp.eval, UnOp.eval] at * <;>
    simp only [maxWord, wordSize] at * <;>
    (repeat' split) <;> omega

/-- Every comparison of a word in the one spelling, bottom up. -/
def WExpr.cmp : WExpr → WExpr
  | .lit n => .lit n
  | .arg i => .arg i
  | .init k => .init k
  | .un op a => .un op a.cmp
  | .bin op a b => cmpBin op a.cmp b.cmp
  | .sinit k => .sinit k.cmp
  | .sel c a b => .sel c.cmp a.cmp b.cmp
  | .hash a b => .hash a.cmp b.cmp
  | .caller => .caller

theorem WExpr.eval_cmp (ρ : Val) : ∀ e : WExpr, e.cmp.eval ρ = e.eval ρ
  | .lit _ => rfl
  | .arg _ => rfl
  | .init _ => rfl
  | .un op a => by simp only [WExpr.cmp, WExpr.eval, WExpr.eval_cmp ρ a]
  | .bin op a b => by
    rw [WExpr.cmp, cmpBin_eval]; simp only [WExpr.eval, WExpr.eval_cmp ρ a, WExpr.eval_cmp ρ b]
  | .sinit k => by simp only [WExpr.cmp, WExpr.eval, WExpr.eval_cmp ρ k]
  | .sel c a b => by
    simp only [WExpr.cmp, WExpr.eval, WExpr.eval_cmp ρ c, WExpr.eval_cmp ρ a, WExpr.eval_cmp ρ b]
  | .hash a b => by simp only [WExpr.cmp, WExpr.eval, WExpr.eval_cmp ρ a, WExpr.eval_cmp ρ b]
  | .caller => rfl

/-- A byte of output, its word's comparisons in the one spelling. -/
def OByte.cmp : OByte → OByte
  | .lit b => .lit b
  | .byteOf e i => .byteOf e.cmp i

theorem OByte.eval_cmp (ρ : Val) (b : OByte) : b.cmp.eval ρ = b.eval ρ := by
  cases b <;> simp [OByte.cmp, OByte.eval, WExpr.eval_cmp]

/-- Every word of a tree, its comparisons in the one spelling. -/
def Tree.cmp : Tree → Tree
  | .halt ok out ws ls =>
    .halt ok (out.map OByte.cmp) (ws.mapW WExpr.cmp) (ls.map (Log.mapL WExpr.cmp OByte.cmp))
  | .ite c t e => .ite c.cmp t.cmp e.cmp

theorem Tree.eval_cmp (ρ : Val) : ∀ T : Tree, T.cmp.eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [Tree.cmp, Tree.eval, List.map_map, Writes.store_mapW ρ _ (WExpr.eval_cmp ρ)]
    congr 2
    · funext b
      exact OByte.eval_cmp ρ b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_cmp ρ) (OByte.eval_cmp ρ) l
  | .ite c t e => by simp only [Tree.cmp, Tree.eval, WExpr.eval_cmp, Tree.eval_cmp ρ t, Tree.eval_cmp ρ e]

/-- A canonical form with its comparisons in the one spelling, canonical again: twice, so the
bounds and negations the first respelling exposes are used and respelled. -/
def Tree.cmpCanon (U : Tree) : Tree := ((U.cmp.canon).cmp).canon

/-- **The canonical form with comparisons in one spelling.** -/
def Tree.canonCmp (T : Tree) : Tree := T.canon.cmpCanon

theorem Tree.eval_cmpCanon (ρ : Val) (U : Tree) : U.cmpCanon.eval ρ = U.eval ρ := by
  rw [Tree.cmpCanon, Tree.eval_canon, Tree.eval_cmp, Tree.eval_canon, Tree.eval_cmp]

theorem Tree.eval_canonCmp (ρ : Val) (T : Tree) : T.canonCmp.eval ρ = T.eval ρ := by
  rw [Tree.canonCmp, Tree.eval_cmpCanon, Tree.eval_canon]

/-- Two trees agree: their canonical forms are equal, or, failing that, the forms with their
comparisons in one spelling are. -/
def Tree.agree (t1 t2 : Tree) : Bool := t1.canon.beq t2.canon || t1.canonCmp.beq t2.canonCmp

/-- **Agreeing trees are equal on every call.** -/
theorem Tree.eval_of_agree {t1 t2 : Tree} (h : Tree.agree t1 t2 = true) (ρ : Val) :
    t1.eval ρ = t2.eval ρ := by
  unfold Tree.agree at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [← Tree.eval_canon ρ t1, Tree.eq_of_beq h, Tree.eval_canon]
  · rw [← Tree.eval_canonCmp ρ t1, Tree.eq_of_beq h, Tree.eval_canonCmp]

/-- What the old comparison accepts, `agree` accepts. -/
theorem Tree.agree_of_beq {t1 t2 : Tree} (h : t1.canon.beq t2.canon = true) :
    Tree.agree t1 t2 = true := by
  simp [Tree.agree, h]

end SolidCore.Refinement.Generic
