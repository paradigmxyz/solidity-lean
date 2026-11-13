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
  `a` with its sides swapped, a branch on `not a` (solar's `a != type(uint256).max`) into a
  branch on `eq a maxWord` with its sides swapped, and splits the disjunctions the simplification left, such as
  `uint256`'s mul overflow check `iszero (or (iszero r) …)` against solar's branch on
  `or (eq r 0) …`; a second `Tree.simp` simplifies along the new paths.

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
with its sides swapped, a branch on `not a` (zero exactly when `a` is the largest word) into a
branch on `eq a maxWord` with its sides swapped, and a disjunction split as `splitCond` does. -/
def splitNeg : WExpr → Tree → Tree → Tree
  | .un .iszero a, t, e => splitNeg a e t
  | .bin .eq a (.lit 0), t, e => splitNeg a e t
  | .bin .eq (.lit 0) a, t, e => splitNeg a e t
  | .bin .or a b, t, e => splitNeg a t (splitNeg b t e)
  | .un .not a, t, e => .ite (.bin .eq a (.lit maxWord)) e t
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
  | case5 a t e =>
    have ha := a.eval_le ρ
    have hm : maxWord % wordSize = maxWord := Nat.mod_eq_of_lt (by decide)
    simp only [Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, hm]
    by_cases h : a.eval ρ = maxWord
    · simp [h]
    · have hlt := a.eval_lt ρ
      have h3 : (wordSize - 1 - a.eval ρ) % wordSize ≠ 0 := by
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [maxWord] at h
        omega
      have h4 : (if a.eval ρ = maxWord then 1 else 0) % wordSize = 0 := by
        split
        · exact absurd ‹_› h
        · rfl
      rw [h4, if_pos rfl]
      exact (ite_cond_eq_false _ _ (eq_false h3)).symm
  | case6 => rfl

theorem Tree.eval_splitNeg (ρ : Val) : ∀ T : Tree, T.splitNeg.eval ρ = T.eval ρ
  | .halt _ _ _ _ => rfl
  | .ite c t e => by
    rw [Tree.splitNeg, splitNeg_eval, Tree.eval_splitNeg ρ t, Tree.eval_splitNeg ρ e]
    rfl

/-! ## The canonical form -/

/-- The canonical form of a tree: constants folded (`Tree.norm`), disjunctions split, and
words simplified along each path; then negations and the disjunctions the simplification left
split (`Tree.splitNeg`), and the words simplified again along the new paths. -/
def Tree.canon (T : Tree) : Tree := (((T.norm.split).simp []).splitNeg).simp []

theorem Tree.eval_canon (ρ : Val) (T : Tree) : T.canon.eval ρ = T.eval ρ := by
  rw [Tree.canon, Tree.eval_simp (fun _ h => absurd h (List.not_mem_nil)), Tree.eval_splitNeg,
    Tree.eval_simp (fun _ h => absurd h (List.not_mem_nil)), Tree.eval_split, Tree.eval_norm]

end SolidCore.Refinement.Generic
