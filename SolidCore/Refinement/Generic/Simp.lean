import SolidCore.Refinement.Generic.Tree

/-!
# Canonical forms of trees: split disjunctions and negations, path facts and bounds

The two sides of the generic source stage spell the same call differently where a narrow type
meets a word: SolidCore checks a `uint8` sum with `uint256`'s overflow check and then its
cleanup, solar with one range check; SolidCore cleans a word that solar knows is clean; solar
reads a packed byte with `byte`, the source with a shift and a mask; solar joins its argument
checks with `or`. `canon` brings both trees to one form, which the kernel then compares by `=`:

* `Tree.split` turns a branch on `or a b` into a branch on `a`, then on `b` (`splitCond`);
* `Tree.simp K` simplifies every word bottom up (`WExpr.simp`): constants fold, `or` with zero
  and shifts by zero drop, `byte i v` becomes `and (shr (8 * (31 - i)) v) 255`, a mask
  `and a (2 ^ k - 1)` drops when `a` is at most the mask, and a comparison that cannot hold
  (`gt a c` with `a ≤ c`, `uint256`'s add and mul overflow checks on operands too small to
  overflow) becomes zero. Upper bounds (`bound`) come from the words' shapes and from the facts
  `K` of the path: each branch taken records its word and side, so a word known to be at most
  `c` (`gt a c` taken as zero) bounds `a`, a branch on a word already decided takes its side,
  and `sub a b` with `lt a b` taken as zero is at most `a`;
* `Tree.splitNeg` then turns a branch on a negation (`iszero a`, `eq a 0`) into a branch on
  `a` with its sides swapped, and splits the disjunctions the simplification left, such as
  `uint256`'s mul overflow check `iszero (or (iszero r) …)` against solar's branch on
  `or (eq r 0) …`; a second `Tree.simp` simplifies along the new paths;
* `Tree.post` then normalizes what solar decides or spells otherwise: identities, the order of a
  sum's operands, comparisons the bounds of the path decide, checks solar joins with `and`,
  branch-free selects, and branches whose sides give the same result; and `Tree.canonWith`
  folds the hash of two constants, as solar folds a constant mapping key to its slot.

`Tree.eval_canon`: a tree and its canonical form give every call the same result. Every rule is
proved on the words' values (`WExpr.eval_simp`, `bound_sound`), so the check stays sound
whatever the trees are; a rule that does not apply leaves the word as it is.
-/

namespace SolidCore.Refinement.Generic

/-- The largest word. -/
abbrev maxWord : Nat := wordSize - 1

theorem WExpr.eval_le (ρ : Val) (e : WExpr) : e.eval ρ ≤ maxWord := by
  have := e.eval_lt ρ
  simp only [maxWord]
  omega

/-! ## Splitting disjunctions -/

/-- A branch on `c`, with a disjunction `or a b` split into a branch on `a`, then on `b`. -/
def splitCond : WExpr → Tree → Tree → Tree
  | .bin .or a b, t, e => splitCond a t (splitCond b t e)
  | c, t, e => .ite c t e

/-- Every branch of a tree, its disjunctions split. -/
def Tree.split : Tree → Tree
  | .halt ok out ws ls => .halt ok out ws ls
  | .ite c t e => splitCond c t.split e.split

theorem or_eval_eq_zero (ρ : Val) (a b : WExpr) :
    (WExpr.bin .or a b).eval ρ = 0 ↔ a.eval ρ = 0 ∧ b.eval ρ = 0 := by
  have ha := a.eval_lt ρ
  have hb := b.eval_lt ρ
  simp only [WExpr.eval, BinOp.eval]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]
  exact Nat.or_eq_zero_iff

theorem splitCond_eval (ρ : Val) (c : WExpr) : ∀ t e : Tree,
    (splitCond c t e).eval ρ = if c.eval ρ = 0 then e.eval ρ else t.eval ρ := by
  induction c with
  | bin op a b iha ihb =>
    cases op
    case or =>
      intro t e
      simp only [splitCond, iha, ihb, or_eval_eq_zero]
      by_cases ha : a.eval ρ = 0 <;> by_cases hb : b.eval ρ = 0 <;> simp [ha, hb]
    all_goals intro t e; rfl
  | _ => intro t e; rfl

theorem Tree.eval_split (ρ : Val) : ∀ T : Tree, T.split.eval ρ = T.eval ρ
  | .halt _ _ _ _ => rfl
  | .ite c t e => by
    rw [Tree.split, splitCond_eval, Tree.eval_split ρ t, Tree.eval_split ρ e]
    rfl

/-! ## Facts of a path -/

/-- The branches a path took: each word, and whether it was not zero. -/
abbrev Facts := List (WExpr × Bool)

/-- The call's words agree with the facts. -/
def Facts.Hold (ρ : Val) (K : Facts) : Prop := ∀ p ∈ K, (p.1.eval ρ = 0 ↔ p.2 = false)

/-- The side the facts give a word, if they record it. -/
def Facts.lookup : Facts → WExpr → Option Bool
  | [], _ => none
  | (c', b) :: K, c => if c' = c then some b else Facts.lookup K c

theorem Facts.lookup_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) {c : WExpr} {b : Bool}
    (hl : K.lookup c = some b) : (c.eval ρ = 0 ↔ b = false) := by
  induction K with
  | nil => simp [Facts.lookup] at hl
  | cons p K ih =>
    obtain ⟨c', b'⟩ := p
    simp only [Facts.lookup] at hl
    split at hl
    · rename_i he
      subst he
      simp only [Option.some.injEq] at hl
      subst hl
      exact h _ List.mem_cons_self
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hl

theorem Facts.Hold.cons {ρ : Val} {K : Facts} (h : K.Hold ρ) {c : WExpr} {b : Bool}
    (hc : c.eval ρ = 0 ↔ b = false) : Facts.Hold ρ ((c, b) :: K) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hc
  · exact h p hp

/-- The facts with one more: a word and its side, a disjunction taken as zero recorded as both
of its operands taken as zero. -/
def Facts.add : Facts → WExpr → Bool → Facts
  | K, .bin .or a b, false => Facts.add (Facts.add K a false) b false
  | K, c, s => (c, s) :: K

theorem Facts.Hold.add {ρ : Val} {K : Facts} (c : WExpr) (s : Bool) (h : K.Hold ρ)
    (hc : c.eval ρ = 0 ↔ s = false) : (K.add c s).Hold ρ := by
  induction K, c, s using Facts.add.induct with
  | case1 K a b iha ihb =>
    have h0 := (or_eval_eq_zero ρ a b).mp (hc.mpr rfl)
    simp only [Facts.add]
    exact ihb (iha h (by simp [h0.1])) (by simp [h0.2])
  | case2 K c s hne =>
    rw [Facts.add]
    · exact h.cons hc
    · exact hne

/-! ## Upper bounds -/

/-- The bound one fact gives a word: `gt e c` taken as zero bounds `e` by `c`. -/
def factBound1 (p : WExpr × Bool) (e : WExpr) : Nat :=
  match p with
  | (.bin .gt e' (.lit c), false) => if e' = e then c % wordSize else maxWord
  | _ => maxWord

/-- The bound the facts give a word. -/
def Facts.bound : Facts → WExpr → Nat
  | [], _ => maxWord
  | p :: K, e => min (factBound1 p e) (Facts.bound K e)

theorem factBound1_sound {ρ : Val} {p : WExpr × Bool} (hp : p.1.eval ρ = 0 ↔ p.2 = false)
    (e : WExpr) : e.eval ρ ≤ factBound1 p e := by
  unfold factBound1
  split
  · rename_i e' c
    split
    · rename_i he
      subst he
      have h0 := hp.mpr rfl
      simp only [WExpr.eval, BinOp.eval] at h0
      by_cases hc : c % wordSize < e'.eval ρ
      · simp [hc] at h0
      · omega
    · exact e.eval_le ρ
  · exact e.eval_le ρ

theorem Facts.bound_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (e : WExpr) :
    e.eval ρ ≤ K.bound e := by
  induction K with
  | nil => exact e.eval_le ρ
  | cons p K ih =>
    exact Nat.le_min.mpr ⟨factBound1_sound (h p List.mem_cons_self) e,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

/-- The least `k` from `k` on with `n < 2 ^ k`, within `f` steps. -/
def bitLenGo (n : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if n < 2 ^ k then k else bitLenGo n f (k + 1)

/-- The number of bits of `n`, for a word. -/
def bitLen (n : Nat) : Nat := bitLenGo n 257 0

/-- A bound of `a ||| b` and `a ^^^ b` for `a ≤ x` and `b ≤ y`. -/
def orBound (x y : Nat) : Nat :=
  if max x y < 2 ^ bitLen (max x y) then 2 ^ bitLen (max x y) - 1 else maxWord

/-- The bound of a binary operation from bounds `x` and `y` of its operands. -/
def binBound (K : Facts) (op : BinOp) (a b : WExpr) (x y : Nat) : Nat :=
  match op with
  | .and => min x y
  | .or => orBound x y
  | .xor => orBound x y
  | .add => if x + y < wordSize then x + y else maxWord
  | .mul => if x * y < wordSize then x * y else maxWord
  | .sub => if K.lookup (.bin .lt a b) = some false then x else maxWord
  | .div => x
  | .shr =>
    match a with
    | .lit s => if s % wordSize < 256 then y / 2 ^ (s % wordSize) else 0
    | _ => maxWord
  | .byte => 255
  | .lt => 1
  | .gt => 1
  | .eq => 1
  | .shl => maxWord

/-- An upper bound of a word on the paths the facts hold on. -/
def bound (K : Facts) : WExpr → Nat
  | .lit n => n % wordSize
  | .arg i => K.bound (.arg i)
  | .init k => K.bound (.init k)
  | .un .iszero _ => 1
  | .un .not a => K.bound (.un .not a)
  | .bin op a b => min (K.bound (.bin op a b)) (binBound K op a b (bound K a) (bound K b))
  | .sinit k => K.bound (.sinit k)
  | .sel _ a b => max (bound K a) (bound K b)
  | .hash a b => K.bound (.hash a b)

theorem orBound_sound {a b x y : Nat} (ha : a ≤ x) (hb : b ≤ y) {f : Nat → Nat → Nat}
    (hf : ∀ n, a < 2 ^ n → b < 2 ^ n → f a b < 2 ^ n) (v : Nat) (hv : v < wordSize)
    (hvf : v ≤ f a b) : v ≤ orBound x y := by
  unfold orBound
  split
  · rename_i hk
    have h1 : a < 2 ^ bitLen (max x y) := by omega
    have h2 : b < 2 ^ bitLen (max x y) := by omega
    have := hf _ h1 h2
    omega
  · simp only [maxWord]; omega

theorem mod_word_le {v n : Nat} (h : v ≤ n) : v % wordSize ≤ n :=
  Nat.le_trans (Nat.mod_le _ _) h

theorem binBound_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (op : BinOp) (a b : WExpr) (x y : Nat)
    (hx : a.eval ρ ≤ x) (hy : b.eval ρ ≤ y) :
    (WExpr.bin op a b).eval ρ ≤ binBound K op a b x y := by
  have ha := a.eval_lt ρ
  have hb := b.eval_lt ρ
  have hle := (WExpr.bin op a b).eval_le ρ
  have hlt := (WExpr.bin op a b).eval_lt ρ
  cases op
  case shr =>
    simp only [binBound]
    split
    · rename_i s
      rw [show (WExpr.bin .shr (.lit s) b).eval ρ =
        (if s % wordSize < 256 then b.eval ρ / 2 ^ (s % wordSize) else 0) % wordSize by
          rfl]
      split
      · exact mod_word_le (Nat.div_le_div_right hy)
      · simp
    · exact hle
  case sub =>
    simp only [binBound]
    split
    · rename_i hl
      have h0 := (Facts.lookup_sound h hl).mpr rfl
      simp only [WExpr.eval, BinOp.eval] at h0 hx ⊢
      by_cases hc : a.eval ρ < b.eval ρ
      · simp [hc] at h0
      · rw [Nat.mod_mod, show a.eval ρ + (wordSize - b.eval ρ) = (a.eval ρ - b.eval ρ) + wordSize by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    · exact hle
  all_goals
    simp only [WExpr.eval] at hle hlt ⊢
    generalize a.eval ρ = u at *
    generalize b.eval ρ = w at *
    simp only [binBound, BinOp.eval] at hle hlt ⊢
  case add =>
    split
    · rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]; omega
    · exact hle
  case mul =>
    split
    · rename_i hxy
      have : u * w < wordSize := Nat.lt_of_le_of_lt (Nat.mul_le_mul hx hy) hxy
      rw [Nat.mod_mod, Nat.mod_eq_of_lt this]
      exact Nat.mul_le_mul hx hy
    · exact hle
  case div =>
    split
    · simp
    · exact mod_word_le (Nat.le_trans (Nat.div_le_self _ _) hx)
  case lt => split <;> simp
  case gt => split <;> simp
  case eq => split <;> simp
  case and =>
    exact Nat.le_min.mpr ⟨mod_word_le (Nat.le_trans Nat.and_le_left hx),
      mod_word_le (Nat.le_trans Nat.and_le_right hy)⟩
  case or => exact orBound_sound hx hy (fun n h1 h2 => Nat.or_lt_two_pow h1 h2) _ hlt (Nat.mod_le _ _)
  case xor => exact orBound_sound hx hy (fun n h1 h2 => Nat.xor_lt_two_pow h1 h2) _ hlt (Nat.mod_le _ _)
  case shl => exact hle
  case byte =>
    split
    · have := Nat.mod_lt (w / 256 ^ (31 - u)) (show 0 < 256 by decide)
      exact mod_word_le (by omega)
    · simp

theorem bound_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) : ∀ e : WExpr, e.eval ρ ≤ bound K e
  | .lit n => by simp [bound, WExpr.eval]
  | .arg i => Facts.bound_sound h _
  | .init k => Facts.bound_sound h _
  | .un .iszero a => by
    simp only [bound, WExpr.eval, UnOp.eval]
    split <;> simp
  | .un .not a => Facts.bound_sound h _
  | .bin op a b => Nat.le_min.mpr ⟨Facts.bound_sound h _,
      binBound_sound h op a b _ _ (bound_sound h a) (bound_sound h b)⟩
  | .sinit k => Facts.bound_sound h _
  | .hash a b => Facts.bound_sound h _
  | .sel c a b => by
    simp only [bound, WExpr.eval]
    have := bound_sound h a
    have := bound_sound h b
    split <;> omega

/-! ## Simplifying words -/

/-- `and a (lit m)`, without the mask when `m` is `2 ^ k - 1` and `a ≤ m`. -/
def sAndLit (K : Facts) (a : WExpr) (m : Nat) : WExpr :=
  if m = 2 ^ bitLen m - 1 ∧ bound K a ≤ m then a else .bin .and a (.lit m)

/-- `or a b` without a zero operand. -/
def sOr (a b : WExpr) : WExpr := if a = .lit 0 then b else if b = .lit 0 then a else .bin .or a b

/-- `and a b`, a constant mask through `sAndLit`. -/
def sAnd (K : Facts) (a b : WExpr) : WExpr :=
  match b with
  | .lit m => sAndLit K a (m % wordSize)
  | _ => .bin .and a b

/-- `gt a c`, zero when `a ≤ c`. -/
def sGt (K : Facts) (a b : WExpr) : WExpr :=
  match b with
  | .lit c => if bound K a ≤ c % wordSize then .lit 0 else .bin .gt a b
  | _ => .bin .gt a b

/-- `lt (add x y) x`, `uint256`'s add overflow check, zero when `x + y` cannot overflow. -/
def sLt (K : Facts) (a b : WExpr) : WExpr :=
  match a with
  | .bin .add x y => if x = b ∧ bound K x + bound K y < wordSize then .lit 0 else .bin .lt a b
  | _ => .bin .lt a b

/-- A shift by zero is its value. -/
def sShift (op : BinOp) (a b : WExpr) : WExpr := if a = .lit 0 then b else .bin op a b

/-- `byte i v` as `and (shr (8 * (31 - i)) v) 255`. -/
def sByte (K : Facts) (a b : WExpr) : WExpr :=
  match a with
  | .lit i =>
    if i % wordSize < 32 then
      sAndLit K (if i % wordSize = 31 then b else .bin .shr (.lit (8 * (31 - i % wordSize))) b) 255
    else .bin .byte a b
  | _ => .bin .byte a b

/-- A binary operation on simplified operands. -/
def sBin (K : Facts) (op : BinOp) (a b : WExpr) : WExpr :=
  match a, b with
  | .lit x, .lit y => .lit (op.eval (x % wordSize) (y % wordSize) % wordSize)
  | _, _ =>
    match op with
    | .or => sOr a b
    | .and => sAnd K a b
    | .gt => sGt K a b
    | .lt => sLt K a b
    | .shl => sShift .shl a b
    | .shr => sShift .shr a b
    | .byte => sByte K a b
    | .eq => if a = b then .lit 1 else .bin .eq a b
    | _ => .bin op a b

/-- A unary operation on a simplified operand: `uint256`'s multiplication overflow check
`iszero (or (iszero r) (eq (div (mul l r) r) l))` is zero when `l * r` cannot overflow. -/
def sUn (K : Facts) (op : UnOp) (a : WExpr) : WExpr :=
  match a with
  | .lit x => .lit (op.eval (x % wordSize) % wordSize)
  | .bin .or (.un .iszero r) (.bin .eq (.bin .div (.bin .mul l r') r'') l') =>
    if op = .iszero ∧ r = r' ∧ r = r'' ∧ l = l' ∧ bound K l * bound K r < wordSize then .lit 0
    else .un op a
  | _ => .un op a

/-- A word simplified on the paths the facts hold on. -/
def WExpr.simp (K : Facts) : WExpr → WExpr
  | .lit n => .lit (n % wordSize)
  | .arg i => .arg i
  | .init k => .init k
  | .un op a => sUn K op (a.simp K)
  | .bin op a b => sBin K op (a.simp K) (b.simp K)
  | .sinit k => .sinit (k.simp K)
  | .sel c a b =>
    match (c.simp K).lit? with
    | some n => if n % wordSize = 0 then b.simp K else a.simp K
    | none =>
      match K.lookup (c.simp K) with
      | some true => a.simp K
      | some false => b.simp K
      | none => .sel (c.simp K) (a.simp K) (b.simp K)
  | .hash a b => .hash (a.simp K) (b.simp K)

theorem eval_sAndLit {ρ : Val} {K : Facts} (h : K.Hold ρ) (a : WExpr) {m : Nat}
    (hm : m < wordSize) : (sAndLit K a m).eval ρ = (WExpr.bin .and a (.lit m)).eval ρ := by
  unfold sAndLit
  split
  · rename_i hc
    obtain ⟨hk, hb⟩ := hc
    have hle := Nat.le_trans (bound_sound h a) hb
    rw [eval_bin, eval_lit, Nat.mod_eq_of_lt hm]
    generalize bitLen m = k at hk
    subst hk
    have hP := Nat.two_pow_pos k
    simp only [BinOp.eval]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show a.eval ρ < 2 ^ k by omega),
      Nat.mod_eq_of_lt (a.eval_lt ρ)]
  · rfl

theorem eval_sOr (ρ : Val) (a b : WExpr) : (sOr a b).eval ρ = (WExpr.bin .or a b).eval ρ := by
  unfold sOr
  split
  · rename_i he; subst he
    rw [eval_bin, eval_lit]
    simp [BinOp.eval, Nat.mod_eq_of_lt (b.eval_lt ρ)]
  · split
    · rename_i _ he; subst he
      rw [eval_bin, eval_lit]
      simp [BinOp.eval, Nat.mod_eq_of_lt (a.eval_lt ρ)]
    · rfl

theorem eval_sAnd {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sAnd K a b).eval ρ = (WExpr.bin .and a b).eval ρ := by
  unfold sAnd
  split
  · next m =>
    rw [eval_sAndLit h a (Nat.mod_lt _ (by decide)), eval_bin, eval_bin, eval_lit, eval_lit,
      Nat.mod_mod]
  · rfl

theorem eval_sGt {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sGt K a b).eval ρ = (WExpr.bin .gt a b).eval ρ := by
  unfold sGt
  split
  · next c =>
    split
    · rename_i hc
      have := bound_sound h a
      rw [eval_bin, eval_lit, eval_lit]
      simp only [BinOp.eval]
      split
      · omega
      · rfl
    · rfl
  · rfl

theorem eval_sLt {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sLt K a b).eval ρ = (WExpr.bin .lt a b).eval ρ := by
  unfold sLt
  split
  · next x y =>
    split
    · rename_i hc
      obtain ⟨rfl, hc⟩ := hc
      have hx := bound_sound h x
      have hy := bound_sound h y
      rw [eval_bin, eval_bin, eval_lit]
      simp only [BinOp.eval, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (show x.eval ρ + y.eval ρ < wordSize by omega)]
      split
      · omega
      · rfl
    · rfl
  · rfl

theorem eval_sShift (ρ : Val) (op : BinOp) (hop : op = .shl ∨ op = .shr) (a b : WExpr) :
    (sShift op a b).eval ρ = (WExpr.bin op a b).eval ρ := by
  unfold sShift
  split
  · rename_i he; subst he
    rw [eval_bin, eval_lit]
    rcases hop with rfl | rfl <;> simp [BinOp.eval, Nat.mod_eq_of_lt (b.eval_lt ρ)]
  · rfl

theorem eval_sByte {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sByte K a b).eval ρ = (WExpr.bin .byte a b).eval ρ := by
  have hb := b.eval_lt ρ
  unfold sByte
  split
  · next i =>
    split
    · rename_i hi
      rw [eval_sAndLit h _ (by decide)]
      have hpow : (256 : Nat) ^ (31 - i % wordSize) = 2 ^ (8 * (31 - i % wordSize)) := by
        rw [Nat.pow_mul]
      have hlt8 : 8 * (31 - i % wordSize) < 256 := by omega
      have h255 : (255 : Nat) % wordSize = 2 ^ 8 - 1 := by decide
      have hbyte : ∀ v : Nat, v % 2 ^ 8 % wordSize = v % 2 ^ 8 := fun v =>
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
      rw [eval_bin, eval_bin, eval_lit, eval_lit, h255]
      simp only [BinOp.eval, Nat.and_two_pow_sub_one_eq_mod]
      rw [if_pos hi]
      split
      · rename_i h31
        rw [h31, Nat.sub_self, Nat.pow_zero, Nat.div_one]
      · rw [eval_bin, eval_lit,
          Nat.mod_eq_of_lt (show 8 * (31 - i % wordSize) < wordSize from Nat.lt_of_lt_of_le hlt8 (by decide))]
        simp only [BinOp.eval]
        rw [if_pos hlt8, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb), hpow,
          show (256 : Nat) = 2 ^ 8 by decide, hbyte]
    · rfl
  · rfl

theorem eval_sBin {ρ : Val} {K : Facts} (h : K.Hold ρ) (op : BinOp) (a b : WExpr) :
    (sBin K op a b).eval ρ = (WExpr.bin op a b).eval ρ := by
  unfold sBin
  split
  · simp [WExpr.eval, Nat.mod_mod]
  · cases op
    case or => exact eval_sOr ρ a b
    case and => exact eval_sAnd h a b
    case gt => exact eval_sGt h a b
    case lt => exact eval_sLt h a b
    case shl => exact eval_sShift ρ .shl (.inl rfl) a b
    case shr => exact eval_sShift ρ .shr (.inr rfl) a b
    case byte => exact eval_sByte h a b
    case eq =>
      show (if a = b then WExpr.lit 1 else .bin .eq a b).eval ρ = _
      by_cases hab : a = b
      · subst hab; simp [WExpr.eval, BinOp.eval]
      · rw [if_neg hab]
    all_goals rfl

theorem eval_sUn {ρ : Val} {K : Facts} (h : K.Hold ρ) (op : UnOp) (a : WExpr) :
    (sUn K op a).eval ρ = (WExpr.un op a).eval ρ := by
  unfold sUn
  split
  · simp [WExpr.eval, Nat.mod_mod]
  · next r l r' r'' l' =>
    split
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, hb⟩ := hc
      have hl := bound_sound h l
      have hr := bound_sound h r
      have hlr : l.eval ρ * r.eval ρ < wordSize :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul hl hr) hb
      have hlt := l.eval_lt ρ
      have hor : (WExpr.bin .or (.un .iszero r) (.bin .eq (.bin .div (.bin .mul l r) r) l)).eval ρ
          ≠ 0 := by
        rw [Ne, or_eval_eq_zero]
        intro ⟨h1, h2⟩
        by_cases hw : r.eval ρ = 0
        · simp [WExpr.eval, UnOp.eval, hw] at h1
        · have : (WExpr.bin .eq (.bin .div (.bin .mul l r) r) l).eval ρ = 1 := by
            simp only [WExpr.eval, BinOp.eval, Nat.mod_mod, hw, ↓reduceIte, Nat.mod_eq_of_lt hlr,
              Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hw), Nat.mod_eq_of_lt hlt]
            rfl
          omega
      rw [show (WExpr.un .iszero (.bin .or (.un .iszero r)
          (.bin .eq (.bin .div (.bin .mul l r) r) l))).eval ρ =
          (if (WExpr.bin .or (.un .iszero r) (.bin .eq (.bin .div (.bin .mul l r) r) l)).eval ρ = 0
            then 1 else 0) % wordSize from rfl, if_neg hor]
      rfl
    · rfl
  · rfl

theorem WExpr.eval_simp {ρ : Val} {K : Facts} (h : K.Hold ρ) : ∀ e : WExpr, (e.simp K).eval ρ = e.eval ρ
  | .lit n => by simp [WExpr.simp, WExpr.eval, Nat.mod_mod]
  | .arg i => rfl
  | .init k => rfl
  | .un op a => by
    rw [WExpr.simp, eval_sUn h]
    simp only [WExpr.eval, WExpr.eval_simp h a]
  | .bin op a b => by
    rw [WExpr.simp, eval_sBin h]
    simp only [WExpr.eval, WExpr.eval_simp h a, WExpr.eval_simp h b]
  | .sinit k => by simp only [WExpr.simp, WExpr.eval, WExpr.eval_simp h k]
  | .hash a b => by simp only [WExpr.simp, WExpr.eval, WExpr.eval_simp h a, WExpr.eval_simp h b]
  | .sel c a b => by
    have hc := WExpr.eval_simp h c
    simp only [WExpr.simp]
    split
    · rename_i n hn
      rw [WExpr.eq_of_lit? hn] at hc
      simp only [WExpr.eval] at hc
      simp only [WExpr.eval, ← hc]
      split
      · exact WExpr.eval_simp h b
      · exact WExpr.eval_simp h a
    · split
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [WExpr.eval, ← hc]
        rw [if_neg (by simpa using this)]
        exact WExpr.eval_simp h a
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [WExpr.eval, ← hc]
        rw [if_pos (by simpa using this)]
        exact WExpr.eval_simp h b
      · simp only [WExpr.eval, hc, WExpr.eval_simp h a, WExpr.eval_simp h b]

/-! ## Simplifying trees -/

/-- A byte of output, its word simplified. -/
def OByte.simp (K : Facts) : OByte → OByte
  | .lit b => .lit (b % 256)
  | .byteOf e i =>
    match e.simp K with
    | .lit n => .lit (n % wordSize / 256 ^ (31 - i) % 256)
    | e' => .byteOf e' i

theorem OByte.eval_simp {ρ : Val} {K : Facts} (h : K.Hold ρ) (b : OByte) :
    (b.simp K).eval ρ = b.eval ρ := by
  cases b with
  | lit b => simp [OByte.simp, OByte.eval, Nat.mod_mod]
  | byteOf e i =>
    have he := WExpr.eval_simp h e
    simp only [OByte.simp]
    split
    · rename_i n hn
      rw [hn] at he
      simp only [OByte.eval, ← he, WExpr.eval, Nat.mod_mod]
    · simp only [OByte.eval, he]

/-- A tree simplified on the paths the facts hold on: every word simplified, a branch on a
constant or on a word the facts decide takes its side, and each side of any other branch is
simplified with its word's side as one more fact. -/
def Tree.simp (K : Facts) : Tree → Tree
  | .halt ok out ws ls =>
    .halt ok (out.map (OByte.simp K)) (ws.mapW (WExpr.simp K))
      (ls.map (Log.mapL (WExpr.simp K) (OByte.simp K)))
  | .ite c t e =>
    match (c.simp K).lit? with
    | some n => if n % wordSize = 0 then e.simp K else t.simp K
    | none =>
      match K.lookup (c.simp K) with
      | some true => t.simp K
      | some false => e.simp K
      | none => .ite (c.simp K) (t.simp ((c.simp K, true) :: K)) (e.simp ((c.simp K, false) :: K))

theorem Tree.eval_simp {ρ : Val} : ∀ {K : Facts}, K.Hold ρ → ∀ T : Tree, (T.simp K).eval ρ = T.eval ρ
  | K, h, .halt ok out ws ls => by
    simp only [Tree.simp, Tree.eval, List.map_map, Writes.store_mapW ρ _ (WExpr.eval_simp h)]
    congr 2
    · funext b
      exact OByte.eval_simp h b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_simp h) (OByte.eval_simp h) l
  | K, h, .ite c t e => by
    have hc := WExpr.eval_simp h c
    simp only [Tree.simp]
    split
    · rename_i n hn
      rw [WExpr.eq_of_lit? hn] at hc
      simp only [WExpr.eval] at hc
      simp only [Tree.eval, ← hc]
      split
      · exact Tree.eval_simp h e
      · exact Tree.eval_simp h t
    · split
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [Tree.eval, ← hc]
        rw [if_neg (by simpa using this)]
        exact Tree.eval_simp h t
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [Tree.eval, ← hc]
        rw [if_pos (by simpa using this)]
        exact Tree.eval_simp h e
      · simp only [Tree.eval, hc]
        split
        · rename_i h0
          exact Tree.eval_simp (h.cons (by simp [hc, h0])) e
        · rename_i h0
          exact Tree.eval_simp (h.cons (by simp [hc, h0])) t

/-! ## Negations -/

/-- A branch on `c`, a negation `iszero a`, `eq a 0` or `eq 0 a` turned into a branch on `a`
with its sides swapped, and a disjunction split as `splitCond` does. -/
def splitNeg : WExpr → Tree → Tree → Tree
  | .un .iszero a, t, e => splitNeg a e t
  | .bin .eq a (.lit 0), t, e => splitNeg a e t
  | .bin .eq (.lit 0) a, t, e => splitNeg a e t
  | .bin .or a b, t, e => splitNeg a t (splitNeg b t e)
  | c, t, e => .ite c t e

/-- Every branch of a tree, its negations and disjunctions split. -/
def Tree.splitNeg : Tree → Tree
  | .halt ok out ws ls => .halt ok out ws ls
  | .ite c t e => Generic.splitNeg c t.splitNeg e.splitNeg

theorem splitNeg_eval (ρ : Val) (c : WExpr) (t e : Tree) :
    (splitNeg c t e).eval ρ = if c.eval ρ = 0 then e.eval ρ else t.eval ρ := by
  fun_induction splitNeg c t e with
  | case1 a t e ih =>
    rw [ih]
    have ha := a.eval_lt ρ
    by_cases h : a.eval ρ = 0 <;> simp [WExpr.eval, UnOp.eval, h]
  | case2 a t e ih =>
    rw [ih]
    by_cases h : a.eval ρ = 0 <;> simp [WExpr.eval, BinOp.eval, h]
  | case3 a t e _ ih =>
    rw [ih]
    have : (0 : Nat) = a.eval ρ ↔ a.eval ρ = 0 := eq_comm
    by_cases h : a.eval ρ = 0 <;> simp [WExpr.eval, BinOp.eval, h, this]
  | case4 a b t e ihb iha =>
    rw [iha, ihb]
    simp only [or_eval_eq_zero]
    by_cases ha : a.eval ρ = 0 <;> by_cases hb : b.eval ρ = 0 <;> simp [ha, hb]
  | case5 => rfl

theorem Tree.eval_splitNeg (ρ : Val) : ∀ T : Tree, T.splitNeg.eval ρ = T.eval ρ
  | .halt _ _ _ _ => rfl
  | .ite c t e => by
    rw [Tree.splitNeg, splitNeg_eval, Tree.eval_splitNeg ρ t, Tree.eval_splitNeg ρ e]
    rfl

/-! ## Normalizations after the canonical form

`Tree.canon` ends with `Tree.post`, which normalizes further the tree `canon`'s simplification
leaves. It runs after every other step, so two trees whose canonical forms were equal without it
still are (it is a function of that form):

* `WExpr.simpX` simplifies words as `WExpr.simp` does, with more rules (`sBinX`): `x + 0`,
  `x - 0`, `x * 0`, `x * 1` and `x / 1` fold; a sum's operands take one order (`WExpr.cmp`,
  constants last), and in `uint256`'s add overflow check `lt (add x y) y` the compared operand
  comes first; a comparison of a word with itself folds, and so does one the bounds of its
  operands decide: upper bounds as `bound` gives them and from more facts of the path
  (`upper`: `lt a c` taken, `eq a c` taken, `eq a (2 ^ 256 - 1)` not taken, ...), lower bounds
  from the facts (`lower`: a word taken as not zero, `gt a c` taken, `lt a c` not taken, ...);
  a mask drops by these bounds too;
* `Tree.splitAnd` turns a branch on `and a b`, both at most one, into a branch on `a`, then on
  `b`: solar joins the overflow checks of several products into one branch;
* `Tree.lift` turns a halt whose words compute with a comparison (solar's branch-free selects,
  such as `add (mul (gt x 10) 50) 50`) into a branch on the comparison, each side with its
  value;
* `Tree.merge` propagates `x = k` into the side of a branch on `eq x k` that takes it, and drops a
  branch whose two sides, both halts, give the same result on the side it decides (solar's
  `x + 1` for `x == max ? 0 : x + 1`), comparing them with the branch's value substituted and
  a subtraction of a constant spelled as an addition.

`Tree.canonWith h` then folds the hash of two constants by `h`, as solar folds `keccak256` of
constant words to a literal slot: sound on calls whose hash is `h` (`Tree.eval_canonWith`), as
SolidCore's slot hash `solHash` is on both sides of the generic stage.
-/

/-! ### Maps over the words of a tree -/

/-- A word with every occurrence of the word `x` replaced by the constant `v`. -/
def WExpr.subst (x : WExpr) (v : Nat) (e : WExpr) : WExpr :=
  if e = x then .lit v else
  match e with
  | .un op a => .un op ((WExpr.subst x v a))
  | .bin op a b => .bin op ((WExpr.subst x v a)) ((WExpr.subst x v b))
  | .sinit k => .sinit ((WExpr.subst x v k))
  | .sel c a b => .sel ((WExpr.subst x v c)) ((WExpr.subst x v a)) ((WExpr.subst x v b))
  | .hash a b => .hash ((WExpr.subst x v a)) ((WExpr.subst x v b))
  | .lit n => .lit n
  | .arg i => .arg i
  | .init k => .init k

theorem WExpr.eval_subst {ρ : Val} {x : WExpr} {v : Nat} (hx : x.eval ρ = v % wordSize) :
    ∀ e : WExpr, (WExpr.subst x v e).eval ρ = e.eval ρ := by
  intro e
  induction e with
  | lit n =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · rfl
  | arg i =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · rfl
  | init k =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · rfl
  | un op a iha =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · simp only [WExpr.eval, iha]
  | bin op a b iha ihb =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · simp only [WExpr.eval, iha, ihb]
  | sinit k ih =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · simp only [WExpr.eval, ih]
  | sel c a b ihc iha ihb =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · simp only [WExpr.eval, ihc, iha, ihb]
  | hash a b iha ihb =>
    unfold WExpr.subst
    split
    · rename_i he; subst he; exact (eval_lit ρ v).trans hx.symm
    · simp only [WExpr.eval, iha, ihb]

/-- A byte of output with its word mapped. -/
def OByte.mapW (f : WExpr → WExpr) : OByte → OByte
  | .lit b => .lit b
  | .byteOf e i => .byteOf (f e) i

theorem OByte.eval_mapW {ρ : Val} {f : WExpr → WExpr} (hf : ∀ e, (f e).eval ρ = e.eval ρ) :
    ∀ b : OByte, (b.mapW f).eval ρ = b.eval ρ
  | .lit _ => rfl
  | .byteOf e i => by simp only [OByte.mapW, OByte.eval, hf]

/-- A halt with every word mapped. -/
def haltMap (f : WExpr → WExpr) (ok : Bool) (out : List OByte) (ws : Writes) (ls : List Log) :
    Tree :=
  .halt ok (out.map (OByte.mapW f)) (ws.mapW f) (ls.map (Log.mapL f (OByte.mapW f)))

theorem eval_haltMap {ρ : Val} {f : WExpr → WExpr} (hf : ∀ e, (f e).eval ρ = e.eval ρ)
    (ok : Bool) (out : List OByte) (ws : Writes) (ls : List Log) :
    (haltMap f ok out ws ls).eval ρ = (Tree.halt ok out ws ls).eval ρ := by
  simp only [haltMap, Tree.eval, List.map_map, Writes.store_mapW ρ _ hf]
  congr 2
  · funext b
    exact OByte.eval_mapW hf b
  · congr 1
    funext l
    exact Log.eval_mapL ρ _ _ hf (OByte.eval_mapW hf) l

/-- Every word of a tree mapped, its conditions too. -/
def Tree.mapW (f : WExpr → WExpr) : Tree → Tree
  | .halt ok out ws ls => haltMap f ok out ws ls
  | .ite c t e => .ite (f c) (t.mapW f) (e.mapW f)

theorem Tree.eval_mapW {ρ : Val} {f : WExpr → WExpr} (hf : ∀ e, (f e).eval ρ = e.eval ρ) :
    ∀ T : Tree, (T.mapW f).eval ρ = T.eval ρ
  | .halt ok out ws ls => eval_haltMap hf ok out ws ls
  | .ite c t e => by
    simp only [Tree.mapW, Tree.eval, hf, Tree.eval_mapW hf t, Tree.eval_mapW hf e]

/-! ### Lower bounds, and more upper bounds from the facts -/

/-- The lower bound one fact gives a word. -/
def factLower1 (p : WExpr × Bool) (e : WExpr) : Nat :=
  if p.1 = e ∧ p.2 = true then 1 else
  match p with
  | (.bin .gt e' (.lit c), true) => if e' = e then c % wordSize + 1 else 0
  | (.bin .lt (.lit c) e', true) => if e' = e then c % wordSize + 1 else 0
  | (.bin .lt e' (.lit c), false) => if e' = e then c % wordSize else 0
  | (.bin .gt (.lit c) e', false) => if e' = e then c % wordSize else 0
  | (.bin .eq e' (.lit c), true) => if e' = e then c % wordSize else 0
  | _ => 0

theorem factLower1_sound {ρ : Val} {p : WExpr × Bool} (hp : p.1.eval ρ = 0 ↔ p.2 = false)
    (e : WExpr) : factLower1 p e ≤ e.eval ρ := by
  unfold factLower1
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h
    subst h1
    have : p.1.eval ρ ≠ 0 := fun h0 => by simp [hp.mp h0] at h2
    omega
  · split
    next e' c _ =>
      split
      · rename_i he; subst he
        simp only [WExpr.eval, BinOp.eval] at hp
        by_cases hc : c % wordSize < e'.eval ρ
        · omega
        · simp [hc] at hp
      · omega
    next c e' _ =>
      split
      · rename_i he; subst he
        simp only [WExpr.eval, BinOp.eval] at hp
        by_cases hc : c % wordSize < e'.eval ρ
        · omega
        · simp [hc] at hp
      · omega
    next e' c _ =>
      split
      · rename_i he; subst he
        simp only [WExpr.eval, BinOp.eval] at hp
        by_cases hc : e'.eval ρ < c % wordSize
        · simp [hc] at hp
        · omega
      · omega
    next c e' _ =>
      split
      · rename_i he; subst he
        simp only [WExpr.eval, BinOp.eval] at hp
        by_cases hc : e'.eval ρ < c % wordSize
        · simp [hc] at hp
        · omega
      · omega
    next e' c _ =>
      split
      · rename_i he; subst he
        simp only [WExpr.eval, BinOp.eval] at hp
        by_cases hc : e'.eval ρ = c % wordSize
        · omega
        · simp [hc] at hp
      · omega
    · omega

/-- The lower bound the facts give a word. -/
def Facts.lower : Facts → WExpr → Nat
  | [], _ => 0
  | p :: K, e => max (factLower1 p e) (Facts.lower K e)

theorem Facts.lower_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (e : WExpr) :
    K.lower e ≤ e.eval ρ := by
  induction K with
  | nil => exact Nat.zero_le _
  | cons p K ih =>
    exact Nat.max_le.mpr ⟨factLower1_sound (h p List.mem_cons_self) e,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

/-- A lower bound of a word on the paths the facts hold on. -/
def lower (K : Facts) (e : WExpr) : Nat :=
  match e with
  | .lit n => n % wordSize
  | e => K.lower e

theorem lower_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (e : WExpr) : lower K e ≤ e.eval ρ := by
  unfold lower
  split
  · simp [WExpr.eval]
  · exact Facts.lower_sound h e

/-- The upper bound one fact gives a word, beyond `factBound1`'s. -/
def factUpper1 (p : WExpr × Bool) (e : WExpr) : Nat :=
  match p with
  | (.bin .lt e' (.lit c), true) => if e' = e then c % wordSize - 1 else maxWord
  | (.bin .gt (.lit c) e', true) => if e' = e then c % wordSize - 1 else maxWord
  | (.bin .lt (.lit c) e', false) => if e' = e then c % wordSize else maxWord
  | (.bin .eq e' (.lit c), true) => if e' = e then c % wordSize else maxWord
  | (.bin .eq e' (.lit c), false) =>
    if e' = e ∧ c % wordSize = maxWord then maxWord - 1 else maxWord
  | _ => maxWord

theorem factUpper1_sound {ρ : Val} {p : WExpr × Bool} (hp : p.1.eval ρ = 0 ↔ p.2 = false)
    (e : WExpr) : e.eval ρ ≤ factUpper1 p e := by
  have hle := e.eval_le ρ
  unfold factUpper1
  split
  next e' c =>
    split
    · rename_i he; subst he
      simp only [WExpr.eval, BinOp.eval] at hp
      by_cases hc : e'.eval ρ < c % wordSize
      · omega
      · simp [hc] at hp
    · exact hle
  next c e' =>
    split
    · rename_i he; subst he
      simp only [WExpr.eval, BinOp.eval] at hp
      by_cases hc : e'.eval ρ < c % wordSize
      · omega
      · simp [hc] at hp
    · exact hle
  next c e' =>
    split
    · rename_i he; subst he
      simp only [WExpr.eval, BinOp.eval] at hp
      by_cases hc : c % wordSize < e'.eval ρ
      · simp [hc] at hp
      · omega
    · exact hle
  next e' c =>
    split
    · rename_i he; subst he
      simp only [WExpr.eval, BinOp.eval] at hp
      by_cases hc : e'.eval ρ = c % wordSize
      · omega
      · simp [hc] at hp
    · exact hle
  next e' c =>
    split
    · rename_i he
      obtain ⟨he, hm⟩ := he
      subst he
      simp only [WExpr.eval, BinOp.eval] at hp
      by_cases hc : e'.eval ρ = c % wordSize
      · simp [hc] at hp
      · simp only [maxWord] at hm hle ⊢
        omega
    · exact hle
  · exact hle

/-- The upper bound the facts give a word, beyond `Facts.bound`'s. -/
def Facts.upper : Facts → WExpr → Nat
  | [], _ => maxWord
  | p :: K, e => min (factUpper1 p e) (Facts.upper K e)

theorem Facts.upper_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (e : WExpr) :
    e.eval ρ ≤ K.upper e := by
  induction K with
  | nil => exact e.eval_le ρ
  | cons p K ih =>
    exact Nat.le_min.mpr ⟨factUpper1_sound (h p List.mem_cons_self) e,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

/-- An upper bound of a word: `bound`'s, and the other facts'. -/
def upper (K : Facts) (e : WExpr) : Nat := min (bound K e) (K.upper e)

theorem upper_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) (e : WExpr) : e.eval ρ ≤ upper K e :=
  Nat.le_min.mpr ⟨bound_sound h e, Facts.upper_sound h e⟩

/-! ### More rules for words -/

/-- A rank of a word's constructor for `WExpr.cmp`, constants last. -/
def WExpr.tag : WExpr → Nat
  | .arg _ => 0
  | .init _ => 1
  | .sinit _ => 2
  | .hash _ _ => 3
  | .un _ _ => 4
  | .bin _ _ _ => 5
  | .sel _ _ _ => 6
  | .lit _ => 7

/-- A rank of a binary operation for `WExpr.cmp`. -/
def BinOp.tag : BinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .lt => 4 | .gt => 5 | .eq => 6 | .and => 7
  | .or => 8 | .xor => 9 | .shl => 10 | .shr => 11 | .byte => 12

/-- A rank of a unary operation for `WExpr.cmp`. -/
def UnOp.tag : UnOp → Nat
  | .iszero => 0 | .not => 1

/-- An order of words, by their constructors and then their parts. -/
def WExpr.cmp : WExpr → WExpr → Ordering
  | .lit m, .lit n => compare m n
  | .arg i, .arg j => compare i j
  | .init i, .init j => compare i j
  | .sinit a, .sinit b => a.cmp b
  | .hash a b, .hash c d => (a.cmp c).then (b.cmp d)
  | .un o a, .un p b => (compare o.tag p.tag).then (a.cmp b)
  | .bin o a b, .bin p c d => ((compare o.tag p.tag).then (a.cmp c)).then (b.cmp d)
  | .sel a b c, .sel d e f => ((a.cmp d).then (b.cmp e)).then (c.cmp f)
  | a, b => compare a.tag b.tag

/-- What the bounds decide of `lt a b`: one when every value of `a` is below every value of
`b`, zero when none is or when `a` is `b`. -/
def decLt (K : Facts) (a b : WExpr) : Option Nat :=
  if a = b then some 0
  else if upper K a < lower K b then some 1
  else if upper K b ≤ lower K a then some 0
  else none

theorem decLt_sound {ρ : Val} {K : Facts} (h : K.Hold ρ) {a b : WExpr} {n : Nat}
    (hd : decLt K a b = some n) : (WExpr.bin .lt a b).eval ρ = n % wordSize := by
  have ua := upper_sound h a
  have ub := upper_sound h b
  have la := lower_sound h a
  have lb := lower_sound h b
  unfold decLt at hd
  simp only [eval_bin, BinOp.eval]
  split at hd
  · rename_i he; subst he; simp at hd; subst hd; simp
  · split at hd
    · simp at hd; subst hd; rw [if_pos (by omega)]
    · split at hd
      · simp at hd; subst hd; rw [if_neg (by omega)]
      · simp at hd

/-- A sum, with a zero operand dropped and the operands in order (`WExpr.cmp`). -/
def sAddX (K : Facts) (a b : WExpr) : WExpr :=
  if a = .lit 0 then b else if b = .lit 0 then a else
  if b.cmp a = .lt then sBin K .add b a else sBin K .add a b

/-- A product, with a zero or one operand folded. -/
def sMulX (K : Facts) (a b : WExpr) : WExpr :=
  if a = .lit 0 ∨ b = .lit 0 then .lit 0 else
  if a = .lit 1 then b else if b = .lit 1 then a else sBin K .mul a b

/-- `lt a b`, folded when the bounds decide it, and `uint256`'s add overflow check
`lt (add x y) x` when `upper` bounds `x + y` below `2 ^ 256`; in `lt (add x b) b` the compared
operand comes first. -/
def sLtX (K : Facts) (a b : WExpr) : WExpr :=
  match decLt K a b with
  | some n => .lit n
  | none =>
    match a with
    | .bin .add x y =>
      if x = b ∧ upper K x + upper K y < wordSize then .lit 0
      else if y = b ∧ x ≠ b then sBin K .lt (.bin .add y x) b else sBin K .lt a b
    | _ => sBin K .lt a b

/-- `gt a b`, folded when the bounds decide it. -/
def sGtX (K : Facts) (a b : WExpr) : WExpr :=
  match decLt K b a with
  | some n => .lit n
  | none => sBin K .gt a b

/-- `and a (lit m)`, without the mask when `m` is `2 ^ k - 1` and `a ≤ m` by `upper`. -/
def sAndX (K : Facts) (a b : WExpr) : WExpr :=
  match b with
  | .lit m =>
    if m % wordSize = 2 ^ bitLen (m % wordSize) - 1 ∧ upper K a ≤ m % wordSize then a
    else sBin K .and a b
  | _ => sBin K .and a b

/-- A binary operation on simplified operands, with `Tree.post`'s rules. -/
def sBinX (K : Facts) (op : BinOp) (a b : WExpr) : WExpr :=
  match op with
  | .add => sAddX K a b
  | .mul => sMulX K a b
  | .sub => if b = .lit 0 then a else if a = b then .lit 0 else sBin K .sub a b
  | .div => if b = .lit 1 then a else sBin K .div a b
  | .lt => sLtX K a b
  | .gt => sGtX K a b
  | .and => sAndX K a b
  | op => sBin K op a b

theorem eval_sAddX {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sAddX K a b).eval ρ = (WExpr.bin .add a b).eval ρ := by
  have ha := a.eval_lt ρ
  have hb := b.eval_lt ρ
  unfold sAddX
  split
  · rename_i he; subst he
    simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt hb]
  · split
    · rename_i _ he; subst he
      simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt ha]
    · split
      · rw [eval_sBin h]
        simp only [eval_bin, BinOp.eval, Nat.add_comm]
      · exact eval_sBin h _ _ _

theorem eval_sMulX {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sMulX K a b).eval ρ = (WExpr.bin .mul a b).eval ρ := by
  have ha := a.eval_lt ρ
  have hb := b.eval_lt ρ
  unfold sMulX
  split
  · rename_i he
    rcases he with he | he <;> subst he <;> simp [WExpr.eval, BinOp.eval]
  · split
    · rename_i _ he; subst he
      simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt hb]
    · split
      · rename_i _ _ he; subst he
        simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt ha]
      · exact eval_sBin h _ _ _

theorem eval_add_comm (ρ : Val) (x y : WExpr) :
    (WExpr.bin .add y x).eval ρ = (WExpr.bin .add x y).eval ρ := by
  simp only [eval_bin, BinOp.eval, Nat.add_comm]

theorem eval_sLtX {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sLtX K a b).eval ρ = (WExpr.bin .lt a b).eval ρ := by
  unfold sLtX
  split
  · rename_i n hd
    rw [decLt_sound h hd, eval_lit]
  · split
    next x y _ =>
      split
      · rename_i hc
        obtain ⟨rfl, hc⟩ := hc
        have hx := upper_sound h x
        have hy := upper_sound h y
        rw [eval_bin, eval_bin, eval_lit]
        simp only [BinOp.eval, Nat.mod_mod]
        rw [Nat.mod_eq_of_lt (show x.eval ρ + y.eval ρ < wordSize by omega)]
        split
        · omega
        · rfl
      · split
        · rw [eval_sBin h]
          exact congrArg (fun v => BinOp.eval .lt v (b.eval ρ) % wordSize) (eval_add_comm ρ x y)
        · exact eval_sBin h _ _ _
    · exact eval_sBin h _ _ _

theorem eval_sGtX {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sGtX K a b).eval ρ = (WExpr.bin .gt a b).eval ρ := by
  unfold sGtX
  split
  · rename_i n hd
    rw [eval_lit, ← decLt_sound h hd]
    simp only [eval_bin, BinOp.eval]
  · exact eval_sBin h _ _ _

theorem eval_sAndX {ρ : Val} {K : Facts} (h : K.Hold ρ) (a b : WExpr) :
    (sAndX K a b).eval ρ = (WExpr.bin .and a b).eval ρ := by
  unfold sAndX
  split
  · next m =>
    split
    · rename_i hc
      obtain ⟨hk, hb⟩ := hc
      have hle := Nat.le_trans (upper_sound h a) hb
      rw [eval_bin, eval_lit]
      generalize bitLen (m % wordSize) = k at hk
      have hP := Nat.two_pow_pos k
      simp only [BinOp.eval]
      rw [hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show a.eval ρ < 2 ^ k by omega),
        Nat.mod_eq_of_lt (a.eval_lt ρ)]
    · exact eval_sBin h _ _ _
  · exact eval_sBin h _ _ _

theorem eval_sBinX {ρ : Val} {K : Facts} (h : K.Hold ρ) (op : BinOp) (a b : WExpr) :
    (sBinX K op a b).eval ρ = (WExpr.bin op a b).eval ρ := by
  have ha := a.eval_lt ρ
  unfold sBinX
  split
  · exact eval_sAddX h a b
  · exact eval_sMulX h a b
  · split
    · rename_i he; subst he
      simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt ha]
    · split
      · rename_i _ he; subst he
        simp only [eval_bin, eval_lit, BinOp.eval]
        rw [Nat.add_sub_of_le (Nat.le_of_lt ha), Nat.mod_self, Nat.zero_mod]
      · exact eval_sBin h _ _ _
  · split
    · rename_i he; subst he
      simp [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt ha]
    · exact eval_sBin h _ _ _
  · exact eval_sLtX h a b
  · exact eval_sGtX h a b
  · exact eval_sAndX h a b
  · exact eval_sBin h _ _ _

/-- A word simplified as `WExpr.simp` does, with `sBinX`'s rules. -/
def WExpr.simpX (K : Facts) : WExpr → WExpr
  | .lit n => .lit (n % wordSize)
  | .arg i => .arg i
  | .init k => .init k
  | .un op a => sUn K op (a.simpX K)
  | .bin op a b => sBinX K op (a.simpX K) (b.simpX K)
  | .sinit k => .sinit (k.simpX K)
  | .sel c a b =>
    match (c.simpX K).lit? with
    | some n => if n % wordSize = 0 then b.simpX K else a.simpX K
    | none =>
      match K.lookup (c.simpX K) with
      | some true => a.simpX K
      | some false => b.simpX K
      | none => .sel (c.simpX K) (a.simpX K) (b.simpX K)
  | .hash a b => .hash (a.simpX K) (b.simpX K)

theorem WExpr.eval_simpX {ρ : Val} {K : Facts} (h : K.Hold ρ) :
    ∀ e : WExpr, (e.simpX K).eval ρ = e.eval ρ
  | .lit n => by simp [WExpr.simpX, WExpr.eval, Nat.mod_mod]
  | .arg i => rfl
  | .init k => rfl
  | .un op a => by
    rw [WExpr.simpX, eval_sUn h]
    simp only [WExpr.eval, WExpr.eval_simpX h a]
  | .bin op a b => by
    rw [WExpr.simpX, eval_sBinX h]
    simp only [WExpr.eval, WExpr.eval_simpX h a, WExpr.eval_simpX h b]
  | .sinit k => by simp only [WExpr.simpX, WExpr.eval, WExpr.eval_simpX h k]
  | .hash a b => by
    simp only [WExpr.simpX, WExpr.eval, WExpr.eval_simpX h a, WExpr.eval_simpX h b]
  | .sel c a b => by
    have hc := WExpr.eval_simpX h c
    simp only [WExpr.simpX]
    split
    · rename_i n hn
      rw [WExpr.eq_of_lit? hn] at hc
      simp only [WExpr.eval] at hc
      simp only [WExpr.eval, ← hc]
      split
      · exact WExpr.eval_simpX h b
      · exact WExpr.eval_simpX h a
    · split
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [WExpr.eval, ← hc]
        rw [if_neg (by simpa using this)]
        exact WExpr.eval_simpX h a
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [WExpr.eval, ← hc]
        rw [if_pos (by simpa using this)]
        exact WExpr.eval_simpX h b
      · simp only [WExpr.eval, hc, WExpr.eval_simpX h a, WExpr.eval_simpX h b]

/-- A byte of output, its word simplified by `WExpr.simpX`. -/
def OByte.simpX (K : Facts) : OByte → OByte
  | .lit b => .lit (b % 256)
  | .byteOf e i =>
    match e.simpX K with
    | .lit n => .lit (n % wordSize / 256 ^ (31 - i) % 256)
    | e' => .byteOf e' i

theorem OByte.eval_simpX {ρ : Val} {K : Facts} (h : K.Hold ρ) (b : OByte) :
    (b.simpX K).eval ρ = b.eval ρ := by
  cases b with
  | lit b => simp [OByte.simpX, OByte.eval, Nat.mod_mod]
  | byteOf e i =>
    have he := WExpr.eval_simpX h e
    simp only [OByte.simpX]
    split
    · rename_i n hn
      rw [hn] at he
      simp only [OByte.eval, ← he, WExpr.eval, Nat.mod_mod]
    · simp only [OByte.eval, he]

/-- A tree simplified as `Tree.simp` does, its words by `WExpr.simpX`. -/
def Tree.simpX (K : Facts) : Tree → Tree
  | .halt ok out ws ls =>
    .halt ok (out.map (OByte.simpX K)) (ws.mapW (WExpr.simpX K))
      (ls.map (Log.mapL (WExpr.simpX K) (OByte.simpX K)))
  | .ite c t e =>
    match (c.simpX K).lit? with
    | some n => if n % wordSize = 0 then e.simpX K else t.simpX K
    | none =>
      match K.lookup (c.simpX K) with
      | some true => t.simpX K
      | some false => e.simpX K
      | none =>
        .ite (c.simpX K) (t.simpX ((c.simpX K, true) :: K)) (e.simpX ((c.simpX K, false) :: K))

theorem Tree.eval_simpX {ρ : Val} :
    ∀ {K : Facts}, K.Hold ρ → ∀ T : Tree, (T.simpX K).eval ρ = T.eval ρ
  | K, h, .halt ok out ws ls => by
    simp only [Tree.simpX, Tree.eval, List.map_map, Writes.store_mapW ρ _ (WExpr.eval_simpX h)]
    congr 2
    · funext b
      exact OByte.eval_simpX h b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_simpX h) (OByte.eval_simpX h) l
  | K, h, .ite c t e => by
    have hc := WExpr.eval_simpX h c
    simp only [Tree.simpX]
    split
    · rename_i n hn
      rw [WExpr.eq_of_lit? hn] at hc
      simp only [WExpr.eval] at hc
      simp only [Tree.eval, ← hc]
      split
      · exact Tree.eval_simpX h e
      · exact Tree.eval_simpX h t
    · split
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [Tree.eval, ← hc]
        rw [if_neg (by simpa using this)]
        exact Tree.eval_simpX h t
      · rename_i hl
        have := Facts.lookup_sound h hl
        simp only [Tree.eval, ← hc]
        rw [if_pos (by simpa using this)]
        exact Tree.eval_simpX h e
      · simp only [Tree.eval, hc]
        split
        · rename_i h0
          exact Tree.eval_simpX (h.cons (by simp [hc, h0])) e
        · rename_i h0
          exact Tree.eval_simpX (h.cons (by simp [hc, h0])) t

/-! ### Joined checks -/

/-- A branch on `c`, a conjunction `and a b` of two words at most one split into a branch on
`a`, then on `b`. -/
def splitAndCond : WExpr → Tree → Tree → Tree
  | .bin .and a b, t, e =>
    if bound [] a ≤ 1 ∧ bound [] b ≤ 1 then splitAndCond a (splitAndCond b t e) e
    else .ite (.bin .and a b) t e
  | c, t, e => .ite c t e

theorem and_eval_eq_zero {ρ : Val} {a b : WExpr} (ha : a.eval ρ ≤ 1) (hb : b.eval ρ ≤ 1) :
    (WExpr.bin .and a b).eval ρ = 0 ↔ a.eval ρ = 0 ∨ b.eval ρ = 0 := by
  simp only [eval_bin, BinOp.eval]
  generalize a.eval ρ = x at *
  generalize b.eval ρ = y at *
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
    rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

theorem Facts.hold_nil (ρ : Val) : Facts.Hold ρ [] := fun _ h => absurd h List.not_mem_nil

theorem splitAndCond_eval (ρ : Val) (c : WExpr) : ∀ t e : Tree,
    (splitAndCond c t e).eval ρ = if c.eval ρ = 0 then e.eval ρ else t.eval ρ := by
  induction c with
  | bin op a b iha ihb =>
    cases op
    case and =>
      intro t e
      simp only [splitAndCond]
      split
      · rename_i hab
        have ha := Nat.le_trans (bound_sound (Facts.hold_nil ρ) a) hab.1
        have hb := Nat.le_trans (bound_sound (Facts.hold_nil ρ) b) hab.2
        rw [iha, ihb]
        have hab := and_eval_eq_zero ha hb
        by_cases h1 : a.eval ρ = 0 <;> by_cases h2 : b.eval ρ = 0 <;> simp [h1, h2, hab]
      · rfl
    all_goals intro t e; rfl
  | _ => intro t e; rfl

/-- Every branch of a tree, its conjunctions of words at most one split. -/
def Tree.splitAnd : Tree → Tree
  | .halt ok out ws ls => .halt ok out ws ls
  | .ite c t e => splitAndCond c t.splitAnd e.splitAnd

theorem Tree.eval_splitAnd (ρ : Val) : ∀ T : Tree, T.splitAnd.eval ρ = T.eval ρ
  | .halt _ _ _ _ => rfl
  | .ite c t e => by
    rw [Tree.splitAnd, splitAndCond_eval, Tree.eval_splitAnd ρ t, Tree.eval_splitAnd ρ e]
    rfl

/-! ### Comparisons computed with -/

/-- Whether a word is a comparison: one or zero. -/
def WExpr.isCmp : WExpr → Bool
  | .bin .lt _ _ | .bin .gt _ _ | .bin .eq _ _ | .un .iszero _ => true
  | _ => false

theorem WExpr.eval_isCmp (ρ : Val) {c : WExpr} (h : c.isCmp = true) :
    c.eval ρ = 0 ∨ c.eval ρ = 1 := by
  match c, h with
  | .bin .lt a b, _ | .bin .gt a b, _ | .bin .eq a b, _ | .un .iszero a, _ =>
    simp only [WExpr.eval, BinOp.eval, UnOp.eval]
    split <;> simp

/-- A comparison a word computes with: an operand of an operation that is not a comparison. -/
def WExpr.inner : WExpr → Option WExpr
  | .un .iszero a => a.inner
  | .un .not a => if a.isCmp then some a else a.inner
  | .bin op a b =>
    if (WExpr.bin op a b).isCmp then a.inner.orElse fun _ => b.inner
    else if a.isCmp then some a else if b.isCmp then some b
    else a.inner.orElse fun _ => b.inner
  | .sel c a b => (a.inner.orElse fun _ => b.inner).orElse fun _ => c.inner
  | .hash a b => a.inner.orElse fun _ => b.inner
  | .sinit k => k.inner
  | _ => none

/-- The words of a halt. -/
def haltWords (out : List OByte) (ws : Writes) (ls : List Log) : List WExpr :=
  let ob : OByte → Option WExpr := fun b => match b with | .byteOf e _ => some e | .lit _ => none
  out.filterMap ob ++ ws.flatMap (fun p => [p.1, p.2]) ++
    ls.flatMap fun l => l.topics ++ l.data.filterMap ob

/-- A halt whose words compute with a comparison, as a branch on it, each side with the
comparison's value, at most `fuel` deep. -/
def liftHalt : Nat → Bool → List OByte → Writes → List Log → Tree
  | 0, ok, out, ws, ls => .halt ok out ws ls
  | f + 1, ok, out, ws, ls =>
    match (haltWords out ws ls).firstM WExpr.inner with
    | some c =>
      if c.isCmp then
        .ite c
          (liftHalt f ok (out.map (OByte.mapW (WExpr.subst c 1))) (ws.mapW (WExpr.subst c 1))
            (ls.map (Log.mapL (WExpr.subst c 1) (OByte.mapW (WExpr.subst c 1)))))
          (liftHalt f ok (out.map (OByte.mapW (WExpr.subst c 0))) (ws.mapW (WExpr.subst c 0))
            (ls.map (Log.mapL (WExpr.subst c 0) (OByte.mapW (WExpr.subst c 0)))))
      else .halt ok out ws ls
    | none => .halt ok out ws ls

theorem liftHalt_eval (ρ : Val) : ∀ (f : Nat) (ok : Bool) (out : List OByte) (ws : Writes)
    (ls : List Log), (liftHalt f ok out ws ls).eval ρ = (Tree.halt ok out ws ls).eval ρ
  | 0, _, _, _, _ => rfl
  | f + 1, ok, out, ws, ls => by
    simp only [liftHalt]
    split
    · rename_i c _
      split
      · rename_i hc
        have hside : ∀ v, c.eval ρ = v % wordSize →
            (liftHalt f ok (out.map (OByte.mapW (WExpr.subst c v))) (ws.mapW (WExpr.subst c v))
              (ls.map (Log.mapL (WExpr.subst c v) (OByte.mapW (WExpr.subst c v))))).eval ρ =
            (Tree.halt ok out ws ls).eval ρ := by
          intro v hv
          rw [liftHalt_eval ρ f]
          exact eval_haltMap (WExpr.eval_subst hv) ok out ws ls
        simp only [Tree.eval]
        split
        · rename_i h0; exact hside 0 (by simp [h0])
        · rename_i h0
          rcases WExpr.eval_isCmp ρ hc with h1 | h1
          · exact absurd h1 h0
          · exact hside 1 (by simp [h1])
      · rfl
    · rfl

/-- Every halt of a tree whose words compute with comparisons, as branches on them. -/
def Tree.lift : Tree → Tree
  | .halt ok out ws ls => liftHalt 6 ok out ws ls
  | .ite c t e => .ite c t.lift e.lift

theorem Tree.eval_lift (ρ : Val) : ∀ T : Tree, T.lift.eval ρ = T.eval ρ
  | .halt ok out ws ls => liftHalt_eval ρ 6 ok out ws ls
  | .ite c t e => by simp only [Tree.lift, Tree.eval, Tree.eval_lift ρ t, Tree.eval_lift ρ e]

/-! ### Branches that do not matter -/

/-- A word with a subtraction of a constant spelled as the addition of its negation. -/
def WExpr.subAdd : WExpr → WExpr
  | .bin op a b =>
    match op, b.subAdd with
    | .sub, .lit c => .bin .add a.subAdd (.lit ((wordSize - c % wordSize) % wordSize))
    | op, b' => .bin op a.subAdd b'
  | .un op a => .un op a.subAdd
  | .sinit k => .sinit k.subAdd
  | .sel c a b => .sel c.subAdd a.subAdd b.subAdd
  | .hash a b => .hash a.subAdd b.subAdd
  | .lit n => .lit n
  | .arg i => .arg i
  | .init k => .init k

theorem WExpr.eval_subAdd (ρ : Val) : ∀ e : WExpr, e.subAdd.eval ρ = e.eval ρ
  | .bin op a b => by
    have ihb := WExpr.eval_subAdd ρ b
    have iha := WExpr.eval_subAdd ρ a
    simp only [WExpr.subAdd]
    split
    · rename_i c hb
      rw [hb] at ihb
      simp only [eval_bin, eval_lit, iha, ← ihb, BinOp.eval, Nat.mod_mod]
      have hc := Nat.mod_lt c (show 0 < wordSize by decide)
      have ha := a.eval_lt ρ
      by_cases h0 : c % wordSize = 0
      · simp [h0]
      · rw [Nat.mod_eq_of_lt (show wordSize - c % wordSize < wordSize by omega)]
    · simp only [eval_bin, iha, ihb]
  | .un op a => by simp only [WExpr.subAdd, WExpr.eval, WExpr.eval_subAdd ρ a]
  | .sinit k => by simp only [WExpr.subAdd, WExpr.eval, WExpr.eval_subAdd ρ k]
  | .sel c a b => by
    simp only [WExpr.subAdd, WExpr.eval, WExpr.eval_subAdd ρ c, WExpr.eval_subAdd ρ a,
      WExpr.eval_subAdd ρ b]
  | .hash a b => by
    simp only [WExpr.subAdd, WExpr.eval, WExpr.eval_subAdd ρ a, WExpr.eval_subAdd ρ b]
  | .lit _ => rfl
  | .arg _ => rfl
  | .init _ => rfl

/-- What a tree gives where the word `x` is `v`, to compare with another's: its words with `x`
as `v`, simplified, and a subtraction of a constant as an addition. -/
def Tree.key (x : WExpr) (v : Nat) (T : Tree) : Tree :=
  ((T.mapW (WExpr.subst x v)).simp []).mapW WExpr.subAdd

theorem Tree.eval_key {ρ : Val} {x : WExpr} {v : Nat} (hx : x.eval ρ = v % wordSize) (T : Tree) :
    (T.key x v).eval ρ = T.eval ρ := by
  rw [Tree.key, Tree.eval_mapW (WExpr.eval_subAdd ρ), Tree.eval_simp (Facts.hold_nil ρ),
    Tree.eval_mapW (WExpr.eval_subst hx)]

/-- The word a condition makes a constant: `x` in `eq x k` or `eq k x`. -/
def eqLit? : WExpr → Option (WExpr × Nat)
  | .bin .eq x (.lit k) => some (x, k)
  | .bin .eq (.lit k) x => some (x, k)
  | _ => none

theorem eval_eqLit? {ρ : Val} {c x : WExpr} {k : Nat} (h : eqLit? c = some (x, k))
    (hc : c.eval ρ ≠ 0) : x.eval ρ = k % wordSize := by
  unfold eqLit? at h
  split at h
  next x' k' =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval_bin, eval_lit, BinOp.eval] at hc
    by_cases hk : x'.eval ρ = k' % wordSize
    · exact hk
    · simp [hk] at hc
  next k' x' _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval_bin, eval_lit, BinOp.eval] at hc
    by_cases hk : k' % wordSize = x'.eval ρ
    · exact hk.symm
    · simp [hk] at hc
  · simp at h

theorem Tree.eval_ite_of_left {ρ : Val} {c : WExpr} {t e : Tree}
    (h : c.eval ρ ≠ 0 → t.eval ρ = e.eval ρ) : e.eval ρ = (Tree.ite c t e).eval ρ := by
  show e.eval ρ = if c.eval ρ = 0 then e.eval ρ else t.eval ρ
  split
  · rfl
  · rename_i h0; exact (h h0).symm

theorem Tree.eval_ite_of_right {ρ : Val} {c : WExpr} {t e : Tree}
    (h : c.eval ρ = 0 → t.eval ρ = e.eval ρ) : t.eval ρ = (Tree.ite c t e).eval ρ := by
  show t.eval ρ = if c.eval ρ = 0 then e.eval ρ else t.eval ρ
  split
  · rename_i h0; exact h h0
  · rfl

theorem Tree.eval_ite_congr {ρ : Val} {c : WExpr} {t t' e : Tree}
    (h : c.eval ρ ≠ 0 → t'.eval ρ = t.eval ρ) :
    (Tree.ite c t' e).eval ρ = (Tree.ite c t e).eval ρ := by
  show (if c.eval ρ = 0 then e.eval ρ else t'.eval ρ) = (if c.eval ρ = 0 then e.eval ρ else t.eval ρ)
  split
  · rfl
  · rename_i h0; exact h h0

/-- Two trees give the same result where `x` is `v` when their keys are equal. -/
theorem Tree.eval_eq_of_key {ρ : Val} {x : WExpr} {v : Nat} (hx : x.eval ρ = v % wordSize)
    {t e : Tree} (hk : t.key x v = e.key x v) : t.eval ρ = e.eval ρ :=
  (Tree.eval_key hx t).symm.trans ((congrArg (Tree.eval ρ) hk).trans (Tree.eval_key hx e))

/-- Whether a tree is a halt. -/
def Tree.isHalt : Tree → Bool
  | .halt .. => true
  | .ite .. => false

/-- A branch on `c`, after its sides: one side when both are the same; for two halts, the side
`eq x k` takes with `x` as `k`, and one side when the two give the same result on the side the
condition decides. -/
def mergeIte (c : WExpr) (t e : Tree) : Tree :=
  if t = e then t else
  if t.isHalt ∧ e.isHalt then
    match eqLit? c with
    | some (x, k) =>
      if ((t.mapW (WExpr.subst x k)).simp []).key x k = e.key x k then e
      else .ite c ((t.mapW (WExpr.subst x k)).simp []) e
    | none =>
      if t.key c 0 = e.key c 0 then t
      else if c.isCmp ∧ t.key c 1 = e.key c 1 then e
      else .ite c t e
  else .ite c t e

theorem mergeIte_eval (ρ : Val) (c : WExpr) (t e : Tree) :
    (mergeIte c t e).eval ρ = (Tree.ite c t e).eval ρ := by
  unfold mergeIte
  split
  · rename_i he; subst he; exact Tree.eval_ite_of_right (fun _ => rfl)
  · split
    · split
      · rename_i x k hxk
        have hside : c.eval ρ ≠ 0 →
            ((t.mapW (WExpr.subst x k)).simp []).eval ρ = t.eval ρ := fun h0 =>
          (Tree.eval_simp (Facts.hold_nil ρ) _).trans
            (Tree.eval_mapW (WExpr.eval_subst (eval_eqLit? hxk h0)) t)
        split
        · rename_i hk
          exact Tree.eval_ite_of_left fun h0 =>
            (hside h0).symm.trans (Tree.eval_eq_of_key (eval_eqLit? hxk h0) hk)
        · exact Tree.eval_ite_congr hside
      · split
        · rename_i hk
          exact Tree.eval_ite_of_right fun h0 =>
            Tree.eval_eq_of_key (show c.eval ρ = 0 % wordSize by simp [h0]) hk
        · split
          · rename_i hk
            obtain ⟨hc, hk⟩ := hk
            exact Tree.eval_ite_of_left fun h0 => by
              have hx : c.eval ρ = 1 % wordSize := by
                rcases WExpr.eval_isCmp ρ hc with h1 | h1
                · exact absurd h1 h0
                · simp [h1]
              exact Tree.eval_eq_of_key hx hk
          · rfl
    · rfl

/-- Every branch of a tree merged (`mergeIte`), from the leaves up. -/
def Tree.merge : Tree → Tree
  | .halt ok out ws ls => .halt ok out ws ls
  | .ite c t e => mergeIte c t.merge e.merge

theorem Tree.eval_merge (ρ : Val) : ∀ T : Tree, T.merge.eval ρ = T.eval ρ
  | .halt _ _ _ _ => rfl
  | .ite c t e => by
    rw [Tree.merge, mergeIte_eval]
    simp only [Tree.eval, Tree.eval_merge ρ t, Tree.eval_merge ρ e]

/-! ### The normalizations after the canonical form -/

/-- The normalizations after the canonical form: words simplified with `sBinX`'s rules, joined
checks and negations split, comparisons computed with lifted to branches, words simplified
again along the new paths, branches that do not matter merged, and a subtraction of a constant
spelled as an addition (`WExpr.subAdd`). -/
def Tree.post (T : Tree) : Tree :=
  ((((((T.simpX []).splitAnd).splitNeg).lift).simpX []).merge).mapW WExpr.subAdd

theorem Tree.eval_post (ρ : Val) (T : Tree) : T.post.eval ρ = T.eval ρ := by
  rw [Tree.post, Tree.eval_mapW (WExpr.eval_subAdd ρ), Tree.eval_merge, Tree.eval_simpX (Facts.hold_nil ρ), Tree.eval_lift,
    Tree.eval_splitNeg, Tree.eval_splitAnd, Tree.eval_simpX (Facts.hold_nil ρ)]

/-! ## The canonical form -/

/-- The canonical form of a tree: constants folded (`Tree.norm`), disjunctions split, and
words simplified along each path; then negations and the disjunctions the simplification left
split (`Tree.splitNeg`), and the words simplified again along the new paths; then the
normalizations after it (`Tree.post`). -/
def Tree.canon (T : Tree) : Tree := ((((T.norm.split).simp []).splitNeg).simp []).post

theorem Tree.eval_canon (ρ : Val) (T : Tree) : T.canon.eval ρ = T.eval ρ := by
  rw [Tree.canon, Tree.eval_post, Tree.eval_simp (fun _ h => absurd h (List.not_mem_nil)),
    Tree.eval_splitNeg, Tree.eval_simp (fun _ h => absurd h (List.not_mem_nil)), Tree.eval_split,
    Tree.eval_norm]

/-! ### Hashes of constants -/

/-- A word with the hash of two constants folded by `h`, and a slot a constant names read as
that slot. -/
def WExpr.foldHash (h : Nat → Nat → Nat) : WExpr → WExpr
  | .hash a b =>
    match a.foldHash h, b.foldHash h with
    | .lit x, .lit y => .lit (h (x % wordSize) (y % wordSize))
    | a', b' => .hash a' b'
  | .sinit k =>
    match k.foldHash h with
    | .lit n => .init (n % wordSize)
    | k' => .sinit k'
  | .un op a => .un op (a.foldHash h)
  | .bin op a b => .bin op (a.foldHash h) (b.foldHash h)
  | .sel c a b => .sel (c.foldHash h) (a.foldHash h) (b.foldHash h)
  | .lit n => .lit n
  | .arg i => .arg i
  | .init k => .init k

theorem WExpr.eval_foldHash {ρ : Val} {h : Nat → Nat → Nat} (hρ : ρ.hash = h) :
    ∀ e : WExpr, (e.foldHash h).eval ρ = e.eval ρ
  | .hash a b => by
    have iha := WExpr.eval_foldHash hρ a
    have ihb := WExpr.eval_foldHash hρ b
    simp only [WExpr.foldHash]
    split
    · rename_i x y hx hy
      rw [hx] at iha
      rw [hy] at ihb
      simp only [eval_lit] at iha ihb
      simp only [WExpr.eval, ← iha, ← ihb, hρ]
    · simp only [WExpr.eval, iha, ihb]
  | .sinit k => by
    have ih := WExpr.eval_foldHash hρ k
    simp only [WExpr.foldHash]
    split
    · rename_i n hn
      rw [hn, eval_lit] at ih
      simp only [WExpr.eval, ← ih]
    · simp only [WExpr.eval, ih]
  | .un op a => by simp only [WExpr.foldHash, WExpr.eval, WExpr.eval_foldHash hρ a]
  | .bin op a b => by
    simp only [WExpr.foldHash, WExpr.eval, WExpr.eval_foldHash hρ a, WExpr.eval_foldHash hρ b]
  | .sel c a b => by
    simp only [WExpr.foldHash, WExpr.eval, WExpr.eval_foldHash hρ c, WExpr.eval_foldHash hρ a,
      WExpr.eval_foldHash hρ b]
  | .lit _ => rfl
  | .arg _ => rfl
  | .init _ => rfl

/-- The canonical form, with the hash of two constants folded by `h`. -/
def Tree.canonWith (h : Nat → Nat → Nat) (T : Tree) : Tree := T.canon.mapW (WExpr.foldHash h)

theorem Tree.eval_canonWith {ρ : Val} {h : Nat → Nat → Nat} (hρ : ρ.hash = h) (T : Tree) :
    (T.canonWith h).eval ρ = T.eval ρ := by
  rw [Tree.canonWith, Tree.eval_mapW (WExpr.eval_foldHash hρ), Tree.eval_canon]

end SolidCore.Refinement.Generic
