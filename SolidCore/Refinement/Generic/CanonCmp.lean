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

/-! ## Checked arithmetic in one spelling, and a select as a branch

Three more spellings of one word, SolidCore's check against solar's (`arithBin`, bottom up in
`WExpr.arith`):

* `lt (add x 1) x`, the overflow check of a checked `x + 1`, is `iszero (add x 1)`: `x + 1`
  wraps exactly when it is zero, which is solar's test.
* `eq (div (mul a c) c) a`, what is left of `uint256`'s mul overflow check by a nonzero constant
  `c` once `iszero c` folds, is `iszero (gt a (maxWord / c))`: `a * c` does not wrap exactly
  when `a ≤ maxWord / c`, solar's range check.
* `add a a` is `mul a 2`.

`Tree.unsel` splits a halt whose output holds `mul x (iszero c)` (solar's branch-free
`c ? 0 : x`) into a branch on `c`: the output with the word `0` where `c` holds and `x` where
it does not, as the source's `if` spells it. `Tree.canonArith` applies both to the comparison
form and brings it to canonical form again. Each rewrite keeps every word's value and every
call's result (`WExpr.eval_arith`, `Tree.eval_unsel`). -/

/-- `lt (add x 1) x` as `iszero (add x 1)`. -/
def arithLt (a b : WExpr) : Option WExpr :=
  match a with
  | .bin .add x (.lit c) => if x = b ∧ c % wordSize = 1 then some (.un .iszero a) else none
  | _ => none

/-- `eq (div (mul a c) c) a`, `c` a nonzero constant, as `iszero (gt a (maxWord / c))`. -/
def arithEq (a b : WExpr) : Option WExpr :=
  match a with
  | .bin .div (.bin .mul x (.lit c)) (.lit c') =>
    if x = b ∧ c' % wordSize = c % wordSize ∧ 0 < c % wordSize then
      some (.un .iszero (.bin .gt x (.lit (maxWord / (c % wordSize)))))
    else none
  | _ => none

/-- One of the three arithmetic spellings, when it applies. -/
def arithBin : BinOp → WExpr → WExpr → Option WExpr
  | .lt, a, b => arithLt a b
  | .eq, a, b => arithEq a b
  | .add, a, b => if a = b then some (.bin .mul a (.lit 2)) else none
  | _, _, _ => none

/-- `a * k` does not wrap exactly when the wrapped product divided by `k` is `a`. -/
theorem mul_div_eq_iff {a k : Nat} (hk : 0 < k) :
    a * k % wordSize / k = a ↔ a ≤ maxWord / k := by
  rw [Nat.le_div_iff_mul_le hk]
  constructor
  · intro h
    rcases Nat.lt_or_ge (a * k) wordSize with hlt | hge
    · exact Nat.le_sub_one_of_lt hlt
    · exfalso
      have h1 : a * k % wordSize < wordSize := Nat.mod_lt _ (by decide)
      have h2 : a * k % wordSize / k * k ≤ a * k % wordSize := Nat.div_mul_le_self _ _
      rw [h] at h2
      omega
  · intro h
    have hlt : a * k < wordSize := Nat.lt_of_le_of_lt h (Nat.sub_one_lt (by decide))
    rw [Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ hk]

theorem arithLt_eval (ρ : Val) {a b e : WExpr} (h : arithLt a b = some e) :
    e.eval ρ = (WExpr.bin .lt a b).eval ρ := by
  have hW : (1 : Nat) < wordSize := by decide
  cases a with
  | bin op x y =>
    cases y with
    | lit c =>
      cases op
      case add =>
        simp only [arithLt] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, hc1⟩ := hc
          simp only [Option.some.injEq] at h
          subst h
          have hx := x.eval_lt ρ
          simp only [WExpr.eval, BinOp.eval, UnOp.eval, hc1, Nat.mod_mod]
          generalize x.eval ρ = v at hx ⊢
          by_cases hs : v + 1 < wordSize
          · rw [Nat.mod_eq_of_lt hs]
            have h1 : ¬ v + 1 = 0 := by omega
            have h2 : ¬ v + 1 < v := by omega
            simp [h1, h2]
          · have he : v + 1 = wordSize := by omega
            have h2 : 0 < v := by omega
            rw [he, Nat.mod_self]
            simp [h2]
        · simp at h
      all_goals simp [arithLt] at h
    | _ => cases op <;> simp [arithLt] at h
  | _ => simp [arithLt] at h

theorem arithEq_eval (ρ : Val) {a b e : WExpr} (h : arithEq a b = some e) :
    e.eval ρ = (WExpr.bin .eq a b).eval ρ := by
  cases a with
  | bin op m y =>
    cases y with
    | lit c' =>
      cases m with
      | bin op' x z =>
        cases z with
        | lit c =>
          cases op <;> cases op' <;> simp only [arithEq, reduceCtorEq] at h <;>
            try (simp at h; done)
          split at h
          · rename_i hc
            obtain ⟨rfl, hcc, hpos⟩ := hc
            simp only [Option.some.injEq] at h
            subst h
            have hW1 : (1 : Nat) % wordSize = 1 := Nat.mod_eq_of_lt (by decide)
            have hq : maxWord / (c % wordSize) < wordSize :=
              Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_one_lt (by decide))
            have key := mul_div_eq_iff (a := x.eval ρ) hpos
            have hprod : x.eval ρ * (c % wordSize) % wordSize < wordSize := Nat.mod_lt _ (by decide)
            have hdiv : x.eval ρ * (c % wordSize) % wordSize / (c % wordSize) < wordSize :=
              Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod
            have hL : (WExpr.un .iszero (.bin .gt x (.lit (maxWord / (c % wordSize))))).eval ρ =
                if x.eval ρ ≤ maxWord / (c % wordSize) then 1 else 0 := by
              show (if (if (maxWord / (c % wordSize)) % wordSize < x.eval ρ then 1 else 0) % wordSize = 0
                then 1 else 0) % wordSize = _
              rw [Nat.mod_eq_of_lt hq]
              by_cases h1 : x.eval ρ ≤ maxWord / (c % wordSize)
              · rw [if_neg (Nat.not_lt.mpr h1), Nat.zero_mod, if_pos rfl, if_pos h1, hW1]
              · rw [if_pos (Nat.lt_of_not_le h1), hW1, if_neg (by decide), if_neg h1, Nat.zero_mod]
            have hR : (WExpr.bin .eq (.bin .div (.bin .mul x (.lit c)) (.lit c')) x).eval ρ =
                if x.eval ρ * (c % wordSize) % wordSize / (c % wordSize) = x.eval ρ then 1 else 0 := by
              show (if (if c' % wordSize = 0 then 0
                  else x.eval ρ * (c % wordSize) % wordSize % wordSize / (c' % wordSize)) % wordSize =
                  x.eval ρ then 1 else 0) % wordSize = _
              rw [hcc, if_neg (Nat.pos_iff_ne_zero.mp hpos), Nat.mod_mod, Nat.mod_eq_of_lt hdiv]
              split <;> simp [hW1]
            rw [hL, hR]
            by_cases h1 : x.eval ρ ≤ maxWord / (c % wordSize)
            · rw [if_pos h1, if_pos (key.mpr h1)]
            · rw [if_neg h1, if_neg (fun h => h1 (key.mp h))]
          · simp at h
        | _ => cases op <;> cases op' <;> simp [arithEq] at h
      | _ => cases op <;> simp [arithEq] at h
    | _ => cases op <;> cases m <;> simp [arithEq] at h
  | _ => simp [arithEq] at h

theorem arithBin_eval (ρ : Val) {op : BinOp} {a b e : WExpr} (h : arithBin op a b = some e) :
    e.eval ρ = (WExpr.bin op a b).eval ρ := by
  cases op
  case lt => exact arithLt_eval ρ h
  case eq => exact arithEq_eval ρ h
  case add =>
    simp only [arithBin] at h
    split at h
    · rename_i hab
      subst hab
      simp only [Option.some.injEq] at h
      subst h
      simp only [WExpr.eval, BinOp.eval, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (show 2 < wordSize by decide)]
      congr 1
      omega
    · simp at h
  all_goals simp [arithBin] at h

/-- Every word with its arithmetic in the one spelling, bottom up. -/
def WExpr.arith : WExpr → WExpr
  | .lit n => .lit n
  | .arg i => .arg i
  | .init k => .init k
  | .un op a => .un op a.arith
  | .bin op a b => (arithBin op a.arith b.arith).getD (.bin op a.arith b.arith)
  | .sinit k => .sinit k.arith
  | .sel c a b => .sel c.arith a.arith b.arith
  | .hash a b => .hash a.arith b.arith
  | .caller => .caller

theorem WExpr.eval_arith (ρ : Val) : ∀ e : WExpr, e.arith.eval ρ = e.eval ρ
  | .lit _ => rfl
  | .arg _ => rfl
  | .init _ => rfl
  | .un op a => by simp only [WExpr.arith, WExpr.eval, WExpr.eval_arith ρ a]
  | .bin op a b => by
    simp only [WExpr.arith]
    cases h : arithBin op a.arith b.arith with
    | none => simp only [Option.getD_none, WExpr.eval, WExpr.eval_arith ρ a, WExpr.eval_arith ρ b]
    | some e =>
      simp only [Option.getD_some, arithBin_eval ρ h]
      simp only [WExpr.eval, WExpr.eval_arith ρ a, WExpr.eval_arith ρ b]
  | .sinit k => by simp only [WExpr.arith, WExpr.eval, WExpr.eval_arith ρ k]
  | .sel c a b => by
    simp only [WExpr.arith, WExpr.eval, WExpr.eval_arith ρ c, WExpr.eval_arith ρ a,
      WExpr.eval_arith ρ b]
  | .hash a b => by simp only [WExpr.arith, WExpr.eval, WExpr.eval_arith ρ a, WExpr.eval_arith ρ b]
  | .caller => rfl

/-- A byte of output, its word's arithmetic in the one spelling. -/
def OByte.arith : OByte → OByte
  | .lit b => .lit b
  | .byteOf e i => .byteOf e.arith i

theorem OByte.eval_arith (ρ : Val) (b : OByte) : b.arith.eval ρ = b.eval ρ := by
  cases b <;> simp [OByte.arith, OByte.eval, WExpr.eval_arith]

/-- Every word of a tree, its arithmetic in the one spelling. -/
def Tree.arith : Tree → Tree
  | .halt ok out ws ls =>
    .halt ok (out.map OByte.arith) (ws.mapW WExpr.arith) (ls.map (Log.mapL WExpr.arith OByte.arith))
  | .ite c t e => .ite c.arith t.arith e.arith

theorem Tree.eval_arith (ρ : Val) : ∀ T : Tree, T.arith.eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [Tree.arith, Tree.eval, List.map_map, Writes.store_mapW ρ _ (WExpr.eval_arith ρ)]
    congr 2
    · funext b
      exact OByte.eval_arith ρ b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_arith ρ) (OByte.eval_arith ρ) l
  | .ite c t e => by
    simp only [Tree.arith, Tree.eval, WExpr.eval_arith, Tree.eval_arith ρ t, Tree.eval_arith ρ e]

/-- The select `c ? 0 : x` a byte of output reads, spelled `mul x (iszero c)`: `(c, x)`. -/
def OByte.sel? : OByte → Option (WExpr × WExpr × WExpr)
  | .byteOf (.bin .mul x (.un .iszero c)) _ => some (.bin .mul x (.un .iszero c), c, x)
  | _ => none

/-- A byte of output with the word `w` read as `r`. -/
def OByte.subst (w r : WExpr) : OByte → OByte
  | .byteOf e i => if e = w then .byteOf r i else .byteOf e i
  | b => b

theorem OByte.eval_subst (ρ : Val) {w r : WExpr} (h : r.eval ρ = w.eval ρ) (b : OByte) :
    (b.subst w r).eval ρ = b.eval ρ := by
  cases b with
  | lit b => rfl
  | byteOf e i =>
    simp only [OByte.subst]
    split
    · rename_i he
      subst he
      simp only [OByte.eval, h]
    · rfl

/-- A halt whose output holds a select `c ? 0 : x` as a branch on `c`; any other tree as it is. -/
def Tree.unsel : Tree → Tree
  | .halt ok out ws ls =>
    match out.findSome? OByte.sel? with
    | some (w, c, x) =>
      .ite c (.halt ok (out.map (OByte.subst w (.lit 0))) ws ls)
        (.halt ok (out.map (OByte.subst w x)) ws ls)
    | none => .halt ok out ws ls
  | .ite c t e => .ite c t.unsel e.unsel

theorem OByte.sel?_spec {b : OByte} {w c x : WExpr} (h : b.sel? = some (w, c, x)) :
    w = .bin .mul x (.un .iszero c) := by
  unfold OByte.sel? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp at h

theorem Tree.eval_unsel (ρ : Val) : ∀ T : Tree, T.unsel.eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [Tree.unsel]
    split
    · rename_i w c x hf
      obtain ⟨b, -, hb⟩ := List.exists_of_findSome?_eq_some hf
      have hw := OByte.sel?_spec hb
      subst hw
      have hx := x.eval_lt ρ
      simp only [Tree.eval]
      split
      · rename_i hc
        have hr : x.eval ρ = (WExpr.bin .mul x (.un .iszero c)).eval ρ := by
          simp only [WExpr.eval, BinOp.eval, UnOp.eval, hc, ↓reduceIte, Nat.mod_mod]
          rw [Nat.mod_eq_of_lt (show 1 < wordSize by decide), Nat.mul_one, Nat.mod_eq_of_lt hx]
        simp only [List.map_map]
        congr 2
        funext b
        exact OByte.eval_subst ρ hr b
      · rename_i hc
        have hr : (WExpr.lit 0).eval ρ = (WExpr.bin .mul x (.un .iszero c)).eval ρ := by
          simp only [WExpr.eval, BinOp.eval, UnOp.eval, hc, ↓reduceIte]
          simp
        simp only [List.map_map]
        congr 2
        funext b
        exact OByte.eval_subst ρ hr b
    · rfl
  | .ite c t e => by simp only [Tree.unsel, Tree.eval, Tree.eval_unsel ρ t, Tree.eval_unsel ρ e]

/-- **The comparison form with its arithmetic in the one spelling and its selects as branches**,
canonical again. -/
def Tree.canonArith (T : Tree) : Tree := T.canonCmp.arith.unsel.canon

theorem Tree.eval_canonArith (ρ : Val) (T : Tree) : T.canonArith.eval ρ = T.eval ρ := by
  rw [Tree.canonArith, Tree.eval_canon, Tree.eval_unsel, Tree.eval_arith, Tree.eval_canonCmp]

/-- Two trees agree: their canonical forms are equal, or, failing that, the forms with their
comparisons in one spelling are, or, failing that, the forms with their arithmetic in one spelling
and their selects as branches are. -/
def Tree.agree (t1 t2 : Tree) : Bool :=
  t1.canon.beq t2.canon || t1.canonCmp.beq t2.canonCmp || t1.canonArith.beq t2.canonArith

/-- **Agreeing trees are equal on every call.** -/
theorem Tree.eval_of_agree {t1 t2 : Tree} (h : Tree.agree t1 t2 = true) (ρ : Val) :
    t1.eval ρ = t2.eval ρ := by
  unfold Tree.agree at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [← Tree.eval_canon ρ t1, Tree.eq_of_beq h, Tree.eval_canon]
    · rw [← Tree.eval_canonCmp ρ t1, Tree.eq_of_beq h, Tree.eval_canonCmp]
  · rw [← Tree.eval_canonArith ρ t1, Tree.eq_of_beq h, Tree.eval_canonArith]

/-- What the old comparison accepts, `agree` accepts. -/
theorem Tree.agree_of_beq {t1 t2 : Tree} (h : t1.canon.beq t2.canon = true) :
    Tree.agree t1 t2 = true := by
  simp [Tree.agree, h]

end SolidCore.Refinement.Generic
