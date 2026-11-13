import SolidCore.Verify.VC.Term

/-!
# Checking solar-verify's obligations against the Lean generator's

`checkOb e (hs, φ)` decides, by evaluation, that an obligation `e` solar-verify sent the solver (the
facts one `check-sat` reads) implies the obligation `hs ⟹ φ` the Lean generator computes:
`checkOb_sound` shows that if `e` has no model then every assignment that makes `hs` hold makes `φ`
hold. The check normalizes `e` and compares it with the Lean obligation by syntax:

1. `inline`: a fact `(= x t)`, where `x` is a constant that `t` does not mention, of `t`'s sort, is a
   definition (solar-verify names its intermediate terms so): `x` is replaced by `t` in the other
   facts and the fact dropped. An obligation without a model keeps none (`inline_sound`).
2. `rename`: solar-verify's constants are `name@N` and its bound variables `name!N`; each is
   renamed to `name` (`strip`), provided no renaming makes a bound variable meet another name in its
   scope (`renameOk`).
3. The last fact must be `(not φ')` with `φ'` equal to `φ`. Every other fact, its conjunctions
   flattened, must be one of `hs`, a range fact `0 ≤ t` or `t ≤ M` that `hs` imply (`inRange`:
   through `select`, `store` and `ite`), or a range fact `0 ≤ x` or `x ≤ M` (`0 ≤ M`) of a constant the
   Lean obligation does not mention, which 0 satisfies.

Each step is proved once, so the check is sound whatever the terms are; a step that does not
apply leaves the obligation unmatched, and the check fails.
-/

namespace SolidCore.Verify.VC

/-! ## Variables -/

mutual
/-- Every name a term mentions, free or bound, of any sort. -/
def Tm.vars : Tm → List String
  | .num _ | .tt | .ff => []
  | .ivar x | .bvar x | .avar x => [x]
  | .app _ args => Tm.varsList args
  | .all x body => x :: Tm.vars body
def Tm.varsList : List Tm → List String
  | [] => []
  | t :: ts => Tm.vars t ++ Tm.varsList ts
end

/-- Two assignments agree on a name, in every sort. -/
def Env.Agree (σ τ : Env) (x : String) : Prop := σ.i x = τ.i x ∧ σ.b x = τ.b x ∧ σ.a x = τ.a x

theorem Env.Agree.setI {σ τ : Env} {x : String} (h : σ.Agree τ x) (y : String) (n : Int) :
    (σ.setI y n).Agree (τ.setI y n) x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  by_cases hx : x = y <;> simp [Env.setI, hx, h1]

mutual
theorem Tm.eval_congr : ∀ (t : Tm) {σ τ : Env}, (∀ x ∈ t.vars, σ.Agree τ x) → t.eval σ = t.eval τ
  | .num _, _, _, _ => rfl
  | .tt, _, _, _ => rfl
  | .ff, _, _, _ => rfl
  | .ivar x, _, _, h => by simp [Tm.eval, (h x (by simp [Tm.vars])).1]
  | .bvar x, _, _, h => by simp [Tm.eval, (h x (by simp [Tm.vars])).2.1]
  | .avar x, _, _, h => by simp [Tm.eval, (h x (by simp [Tm.vars])).2.2]
  | .app f args, σ, τ, h => by
    simp only [Tm.eval]
    rw [Tm.evalList_congr args (by simpa [Tm.vars] using h)]
  | .all x body, σ, τ, h => by
    simp only [Tm.eval]
    have : ∀ n : Int, Tm.eval (σ.setI x n) body = Tm.eval (τ.setI x n) body := fun n =>
      Tm.eval_congr body fun y hy => Env.Agree.setI (h y (by simp [Tm.vars, hy])) x n
    simp only [this]
theorem Tm.evalList_congr : ∀ (ts : List Tm) {σ τ : Env}, (∀ x ∈ Tm.varsList ts, σ.Agree τ x) →
    Tm.evalList σ ts = Tm.evalList τ ts
  | [], _, _, _ => rfl
  | t :: ts, σ, τ, h => by
    simp only [Tm.evalList]
    rw [Tm.eval_congr t (fun x hx => h x (by simp [Tm.varsList, hx])),
      Tm.evalList_congr ts (fun x hx => h x (by simp [Tm.varsList, hx]))]
end

/-! ## Sorts of values -/

/-- The sort of a value. -/
def Value.sortOf : Value → Srt
  | .int _ => .int
  | .prop _ => .bool
  | .arr _ => .arr

/-- Values whose sorts are the ones the list gives, where it gives one. -/
def SortsAgree : List (Option Srt) → List Value → Prop
  | [], [] => True
  | o :: os, v :: vs => (∀ s, o = some s → v.sortOf = s) ∧ SortsAgree os vs
  | _, _ => False

theorem applyOp_sortOf (f : String) : ∀ (os : List (Option Srt)) (vs : List Value),
    SortsAgree os vs → ∀ {s : Srt}, sortOp f os = some s → (applyOp f vs).sortOf = s := by
  intro os vs h s hs
  unfold sortOp at hs
  split at hs
  all_goals first
    | (simp at hs; done)
    | (rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vs⟩⟩⟩⟩ <;>
        simp_all [SortsAgree, applyOp, Value.sortOf] <;> done)
    | skip
  all_goals
    split at hs <;> simp at hs
    subst_vars
    rcases vs with _ | ⟨c, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vs⟩⟩⟩⟩ <;> simp [SortsAgree] at h
    obtain ⟨-, h1, h2⟩ := h
    cases v1 <;> cases v2 <;> simp [Value.sortOf, applyOp] at h1 h2 ⊢ <;> (try subst h1) <;> simp_all

mutual
theorem Tm.eval_sortOf : ∀ (t : Tm) (σ : Env) {s : Srt}, t.sort? = some s → (t.eval σ).sortOf = s
  | .num _, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .tt, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .ff, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .ivar _, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .bvar _, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .avar _, _, s, h => by simp_all [Tm.sort?, Tm.eval, Value.sortOf]
  | .all _ _, _, s, h => by
    simp only [Tm.sort?] at h
    split at h <;> simp at h
    subst h; simp [Tm.eval, Value.sortOf]
  | .app f args, σ, s, h => by
    simp only [Tm.sort?] at h
    simp only [Tm.eval]
    exact applyOp_sortOf f _ _ (Tm.evalList_sortOf args σ) h
theorem Tm.evalList_sortOf : ∀ (ts : List Tm) (σ : Env), SortsAgree (Tm.sortList ts) (Tm.evalList σ ts)
  | [], _ => trivial
  | t :: ts, σ => ⟨fun _ h => Tm.eval_sortOf t σ h, Tm.evalList_sortOf ts σ⟩
end

/-! ## Substitution -/

mutual
/-- The names a term binds. -/
def Tm.binders : Tm → List String
  | .app _ args => Tm.bindersList args
  | .all x body => x :: Tm.binders body
  | _ => []
def Tm.bindersList : List Tm → List String
  | [] => []
  | t :: ts => Tm.binders t ++ Tm.bindersList ts
end

/-- Whether `t` is the constant of sort `s` named `x`. -/
def Tm.isVar : Tm → Srt → String → Bool
  | .ivar y, .int, x => y == x
  | .bvar y, .bool, x => y == x
  | .avar y, .arr, x => y == x
  | _, _, _ => false

mutual
/-- Replace the constant of sort \`s\` named \`x\` by \`u\`. A bound variable of the same name shadows
it. -/
def Tm.subst : Tm → Srt → String → Tm → Tm
  | .num n, _, _, _ => .num n
  | .tt, _, _, _ => .tt
  | .ff, _, _, _ => .ff
  | .ivar y, s, x, u => if (Tm.ivar y).isVar s x then u else .ivar y
  | .bvar y, s, x, u => if (Tm.bvar y).isVar s x then u else .bvar y
  | .avar y, s, x, u => if (Tm.avar y).isVar s x then u else .avar y
  | .app f args, s, x, u => .app f (Tm.substList args s x u)
  | .all y body, s, x, u => if s = .int ∧ y = x then .all y body else .all y (Tm.subst body s x u)
def Tm.substList : List Tm → Srt → String → Tm → List Tm
  | [], _, _, _ => []
  | t :: ts, s, x, u => Tm.subst t s x u :: Tm.substList ts s x u
end

/-- The assignment with the constant of sort `s` named `x` set to the value `v`. -/
def Env.set (σ : Env) : Srt → String → Value → Env
  | .int, x, v => σ.setI x v.toInt
  | .bool, x, v => σ.setB x v.toProp
  | .arr, x, v => σ.setA x v.toArr

theorem Env.setI_setI (σ : Env) (x : String) (m n : Int) : (σ.setI x m).setI x n = σ.setI x n := by
  cases σ; simp only [Env.setI, Env.mk.injEq, and_true]; funext y; split <;> rfl

theorem Env.set_setI_comm (σ : Env) (s : Srt) (x y : String) (v : Value) (n : Int)
    (h : ¬ (s = .int ∧ y = x)) : (σ.setI y n).set s x v = (σ.set s x v).setI y n := by
  cases σ
  cases s <;> simp only [Env.set, Env.setI, Env.setB, Env.setA, Env.mk.injEq, and_true]
  funext z
  have : y ≠ x := fun e => h ⟨rfl, e⟩
  by_cases hz : z = x
  · subst hz; simp [this.symm]
  · simp [hz]

theorem Value.eq_refl : ∀ v : Value, v.eq v
  | .int _ => rfl
  | .prop _ => Iff.rfl
  | .arr _ => rfl

theorem Value.sortOf_int {v : Value} (h : v.sortOf = .int) : v = .int v.toInt := by
  cases v <;> simp_all [Value.sortOf, Value.toInt]
theorem Value.sortOf_bool {v : Value} (h : v.sortOf = .bool) : v = .prop v.toProp := by
  cases v <;> simp_all [Value.sortOf, Value.toProp]
theorem Value.sortOf_arr {v : Value} (h : v.sortOf = .arr) : v = .arr v.toArr := by
  cases v <;> simp_all [Value.sortOf, Value.toArr]

/-- The constant of sort `s` named `x` reads the value of sort `s` set at it. -/
theorem Env.set_var (σ : Env) (s : Srt) (x : String) (v : Value) (hv : v.sortOf = s) (y : Tm)
    (hy : y.isVar s x = true) : y.eval (σ.set s x v) = v := by
  cases y <;> cases s <;> simp [Tm.isVar] at hy <;> subst hy <;>
    simp [Tm.eval, Env.set, Env.setI, Env.setB, Env.setA]
  · exact (Value.sortOf_int hv).symm
  · exact (Value.sortOf_bool hv).symm
  · exact (Value.sortOf_arr hv).symm

theorem Env.set_other (σ : Env) (s : Srt) (x : String) (v : Value) :
    ∀ y : Tm, (y matches .ivar _ | .bvar _ | .avar _) → y.isVar s x = false →
      y.eval (σ.set s x v) = y.eval σ := by
  intro y hy hn
  cases y <;> simp at hy <;> cases s <;>
    simp_all [Tm.isVar, Tm.eval, Env.set, Env.setI, Env.setB, Env.setA]

mutual
theorem Tm.eval_subst (s : Srt) (x : String) (u : Tm) (hu : u.sort? = some s) :
    ∀ (A : Tm) (σ : Env), (∀ y ∈ A.binders, y ∉ u.vars) →
      (A.subst s x u).eval σ = A.eval (σ.set s x (u.eval σ))
  | .num _, σ, _ => rfl
  | .tt, σ, _ => rfl
  | .ff, σ, _ => rfl
  | .ivar y, σ, _ => by
    simp only [Tm.subst]
    split
    · rename_i h; exact (Env.set_var σ s x _ (Tm.eval_sortOf u σ hu) _ h).symm
    · rename_i h; exact (Env.set_other σ s x _ _ rfl (by simpa using h)).symm
  | .bvar y, σ, _ => by
    simp only [Tm.subst]
    split
    · rename_i h; exact (Env.set_var σ s x _ (Tm.eval_sortOf u σ hu) _ h).symm
    · rename_i h; exact (Env.set_other σ s x _ _ rfl (by simpa using h)).symm
  | .avar y, σ, _ => by
    simp only [Tm.subst]
    split
    · rename_i h; exact (Env.set_var σ s x _ (Tm.eval_sortOf u σ hu) _ h).symm
    · rename_i h; exact (Env.set_other σ s x _ _ rfl (by simpa using h)).symm
  | .app f args, σ, hb => by
    simp only [Tm.subst, Tm.eval]
    rw [Tm.evalList_subst s x u hu args σ (by simpa [Tm.binders] using hb)]
  | .all y body, σ, hb => by
    simp only [Tm.subst]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Tm.eval, Env.set, Env.setI_setI]
    · rename_i h
      simp only [Tm.eval]
      have hy : y ∉ u.vars := hb y (by simp [Tm.binders])
      have key : ∀ n : Int, (body.subst s x u).eval (σ.setI y n) =
          body.eval ((σ.set s x (u.eval σ)).setI y n) := by
        intro n
        rw [Tm.eval_subst s x u hu body (σ.setI y n) (fun z hz => hb z (by simp [Tm.binders, hz]))]
        have : u.eval (σ.setI y n) = u.eval σ := Tm.eval_congr u fun z hz => by
          have : z ≠ y := fun e => hy (e ▸ hz)
          exact ⟨by simp [Env.setI, this], rfl, rfl⟩
        rw [this, Env.set_setI_comm σ s x y _ n h]
      simp only [key]
theorem Tm.evalList_subst (s : Srt) (x : String) (u : Tm) (hu : u.sort? = some s) :
    ∀ (ts : List Tm) (σ : Env), (∀ y ∈ Tm.bindersList ts, y ∉ u.vars) →
      Tm.evalList σ (Tm.substList ts s x u) = Tm.evalList (σ.set s x (u.eval σ)) ts
  | [], _, _ => rfl
  | t :: ts, σ, hb => by
    simp only [Tm.substList, Tm.evalList]
    rw [Tm.eval_subst s x u hu t σ (fun y hy => hb y (by simp [Tm.bindersList, hy])),
      Tm.evalList_subst s x u hu ts σ (fun y hy => hb y (by simp [Tm.bindersList, hy]))]
end

/-! ## Inlining definitions -/

/-- A definition `(= x u)`: a constant `x` that `u` does not mention, of `u`'s sort. -/
def defOf? : Tm → Option (Srt × String × Tm)
  | .app "=" [.ivar x, u] => if u.sort? = some .int ∧ x ∉ u.vars then some (.int, x, u) else none
  | .app "=" [.bvar x, u] => if u.sort? = some .bool ∧ x ∉ u.vars then some (.bool, x, u) else none
  | .app "=" [.avar x, u] => if u.sort? = some .arr ∧ x ∉ u.vars then some (.arr, x, u) else none
  | _ => none

/-- The definition's variable, as a term. -/
def varOf : Srt → String → Tm
  | .int, x => .ivar x
  | .bool, x => .bvar x
  | .arr, x => .avar x

theorem defOf?_spec {t : Tm} {s : Srt} {x : String} {u : Tm} (h : defOf? t = some (s, x, u)) :
    u.sort? = some s ∧ x ∉ u.vars ∧ ∀ σ, t.eval σ = .prop (((varOf s x).eval σ).eq (u.eval σ)) := by
  unfold defOf? at h
  split at h <;> (try simp at h)
  all_goals
    obtain ⟨⟨hs1, hs2⟩, rfl, rfl, rfl⟩ := h
    exact ⟨hs1, hs2, fun σ => by simp [Tm.eval, applyOp, Tm.evalList, varOf]⟩

theorem varOf_isVar (s : Srt) (x : String) : (varOf s x).isVar s x = true := by
  cases s <;> simp [varOf, Tm.isVar]

/-- Whether the facts have a model. -/
def Sat (σ : Env) (fs : List Tm) : Prop := ∀ t ∈ fs, t.Holds σ

/-- A definition holds where its variable is set to its term's value. -/
theorem def_holds {t : Tm} {s : Srt} {x : String} {u : Tm} (h : defOf? t = some (s, x, u))
    (σ : Env) : t.Holds (σ.set s x (u.eval σ)) := by
  obtain ⟨hu, hx, he⟩ := defOf?_spec h
  have hv : u.eval (σ.set s x (u.eval σ)) = u.eval σ := Tm.eval_congr u fun z hz => by
    have : z ≠ x := fun e => hx (e ▸ hz)
    cases s <;> refine ⟨?_, ?_, ?_⟩ <;> simp [Env.set, Env.setI, Env.setB, Env.setA, this]
  have hvar : (varOf s x).eval (σ.set s x (u.eval σ)) = u.eval σ :=
    Env.set_var σ s x (u.eval σ) (Tm.eval_sortOf u σ hu) (varOf s x) (varOf_isVar s x)
  simp only [Tm.Holds, he, hvar, hv, Value.toProp]
  exact Value.eq_refl _

/-- Inline the definitions among `rest`, with `done` the facts already seen (newest first), with
`fuel` steps. -/
def inlineFuel : Nat → List Tm → List Tm → List Tm
  | 0, done, rest => done.reverse ++ rest
  | _ + 1, done, [] => done.reverse
  | n + 1, done, f :: rest =>
    match defOf? f with
    | some (s, x, u) =>
      if (done ++ rest).all (fun t => t.binders.all (fun y => !u.vars.contains y)) then
        inlineFuel n (done.map (·.subst s x u)) (rest.map (·.subst s x u))
      else inlineFuel n (f :: done) rest
    | none => inlineFuel n (f :: done) rest

def inline (fs : List Tm) : List Tm := inlineFuel fs.length [] fs

theorem shift {t f : Tm} {done rest : List Tm} (ht : t ∈ done ∨ t ∈ f :: rest) :
    t ∈ f :: done ∨ t ∈ rest := by
  rcases ht with ht | ht
  · exact Or.inl (List.mem_cons_of_mem _ ht)
  · rcases List.mem_cons.mp ht with h | h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    · exact Or.inr h

theorem inlineFuel_sound : ∀ (n : Nat) (done rest : List Tm),
    (∀ σ, ¬ ∀ t, t ∈ done ∨ t ∈ rest → t.Holds σ) → ∀ σ, ¬ Sat σ (inlineFuel n done rest)
  | 0, done, rest, h, σ, hs => h σ fun t ht => hs t (by
      simp only [inlineFuel, List.mem_append, List.mem_reverse]; exact ht)
  | _ + 1, done, [], h, σ, hs => h σ fun t ht => hs t (by simp [inlineFuel]; simpa using ht)
  | n + 1, done, f :: rest, h, σ, hs => by
    simp only [inlineFuel] at hs
    split at hs
    · rename_i s x u hd
      split at hs
      · rename_i hcap
        refine inlineFuel_sound n _ _ ?_ σ hs
        intro τ hτ
        have hu := (defOf?_spec hd).1
        have hcap' : ∀ t ∈ done ++ rest, ∀ y ∈ t.binders, y ∉ u.vars := by
          intro t ht y hy hyu
          have := List.all_eq_true.mp hcap t ht
          have := List.all_eq_true.mp this y hy
          simp [hyu] at this
        apply h (τ.set s x (u.eval τ))
        intro t ht
        rcases ht with ht | ht
        · have := hτ (t.subst s x u) (Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩))
          simp only [Tm.Holds] at this ⊢
          rwa [Tm.eval_subst s x u hu t τ (hcap' t (by simp [ht]))] at this
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact def_holds hd τ
          · have := hτ (t.subst s x u) (Or.inr (List.mem_map.mpr ⟨t, ht, rfl⟩))
            simp only [Tm.Holds] at this ⊢
            rwa [Tm.eval_subst s x u hu t τ (hcap' t (by simp [ht]))] at this
      · exact inlineFuel_sound n (f :: done) rest
          (fun τ hτ => h τ fun t ht => hτ t (shift ht)) σ hs
    · exact inlineFuel_sound n (f :: done) rest
        (fun τ hτ => h τ fun t ht => hτ t (shift ht)) σ hs

theorem inline_sound {fs : List Tm} (h : ∀ σ, ¬ Sat σ fs) : ∀ σ, ¬ Sat σ (inline fs) :=
  inlineFuel_sound _ [] fs (fun σ hσ => h σ fun t ht => hσ t (Or.inr ht))

/-! ## Renaming solar-verify's names -/

/-- `name@N` and `name!N` to `name`. -/
def strip (x : String) : String := String.ofList (x.toList.takeWhile fun c => c ≠ '@' ∧ c ≠ '!')

mutual
def Tm.rename : Tm → Tm
  | .num n => .num n
  | .tt => .tt
  | .ff => .ff
  | .ivar x => .ivar (strip x)
  | .bvar x => .bvar (strip x)
  | .avar x => .avar (strip x)
  | .app f args => .app f (Tm.renameList args)
  | .all x body => .all (strip x) (Tm.rename body)
def Tm.renameList : List Tm → List Tm
  | [] => []
  | t :: ts => Tm.rename t :: Tm.renameList ts
end

mutual
/-- No renaming makes a bound variable meet another name in its scope. -/
def Tm.renameOk : Tm → Bool
  | .app _ args => Tm.renameOkList args
  | .all x body => body.vars.all (fun y => y == x || strip y != strip x) && Tm.renameOk body
  | _ => true
def Tm.renameOkList : List Tm → Bool
  | [] => true
  | t :: ts => Tm.renameOk t && Tm.renameOkList ts
end

/-- `σ` reads each name as `τ` reads its renaming. -/
def Env.Renamed (σ τ : Env) (y : String) : Prop :=
  σ.i y = τ.i (strip y) ∧ σ.b y = τ.b (strip y) ∧ σ.a y = τ.a (strip y)

mutual
theorem Tm.eval_rename : ∀ (t : Tm) {σ τ : Env}, t.renameOk = true →
    (∀ y ∈ t.vars, σ.Renamed τ y) → t.eval σ = t.rename.eval τ
  | .num _, _, _, _, _ => rfl
  | .tt, _, _, _, _ => rfl
  | .ff, _, _, _, _ => rfl
  | .ivar x, _, _, _, h => by simp [Tm.rename, Tm.eval, (h x (by simp [Tm.vars])).1]
  | .bvar x, _, _, _, h => by simp [Tm.rename, Tm.eval, (h x (by simp [Tm.vars])).2.1]
  | .avar x, _, _, _, h => by simp [Tm.rename, Tm.eval, (h x (by simp [Tm.vars])).2.2]
  | .app f args, σ, τ, ho, h => by
    simp only [Tm.rename, Tm.eval]
    rw [Tm.evalList_rename args (by simpa [Tm.renameOk] using ho) (by simpa [Tm.vars] using h)]
  | .all x body, σ, τ, ho, h => by
    simp only [Tm.renameOk, Bool.and_eq_true, List.all_eq_true] at ho
    simp only [Tm.rename, Tm.eval]
    have key : ∀ n : Int, body.eval (σ.setI x n) = body.rename.eval (τ.setI (strip x) n) := by
      intro n
      apply Tm.eval_rename body ho.2
      intro y hy
      obtain ⟨h1, h2, h3⟩ := h y (by simp [Tm.vars, hy])
      refine ⟨?_, h2, h3⟩
      by_cases hyx : y = x
      · subst hyx; simp [Env.setI]
      · have := ho.1 y hy
        have hs : strip y ≠ strip x := by simpa [hyx] using this
        simp [Env.setI, hyx, hs, h1]
    simp only [key]
theorem Tm.evalList_rename : ∀ (ts : List Tm) {σ τ : Env}, Tm.renameOkList ts = true →
    (∀ y ∈ Tm.varsList ts, σ.Renamed τ y) → Tm.evalList σ ts = Tm.evalList τ (Tm.renameList ts)
  | [], _, _, _, _ => rfl
  | t :: ts, σ, τ, ho, h => by
    simp only [Tm.renameOkList, Bool.and_eq_true] at ho
    simp only [Tm.renameList, Tm.evalList]
    rw [Tm.eval_rename t ho.1 (fun y hy => h y (by simp [Tm.varsList, hy])),
      Tm.evalList_rename ts ho.2 (fun y hy => h y (by simp [Tm.varsList, hy]))]
end

theorem rename_sound {fs : List Tm} (hok : fs.all Tm.renameOk = true) (h : ∀ σ, ¬ Sat σ fs) :
    ∀ τ, ¬ Sat τ (fs.map Tm.rename) := by
  intro τ hτ
  let σ : Env := ⟨fun y => τ.i (strip y), fun y => τ.b (strip y), fun y => τ.a (strip y)⟩
  apply h σ
  intro t ht
  have := hτ t.rename (List.mem_map.mpr ⟨t, ht, rfl⟩)
  simp only [Tm.Holds] at this ⊢
  rwa [Tm.eval_rename t (List.all_eq_true.mp hok t ht) (fun y _ => ⟨rfl, rfl, rfl⟩)]

/-! ## Flattening conjunctions -/

mutual
def flatten : Tm → List Tm
  | .tt => []
  | .app "and" args => flattenList args
  | t => [t]
def flattenList : List Tm → List Tm
  | [] => []
  | t :: ts => flatten t ++ flattenList ts
end

mutual
theorem flatten_holds : ∀ (t : Tm) (σ : Env), (∀ c ∈ flatten t, c.Holds σ) → t.Holds σ
  | .tt, _, _ => by simp [Tm.Holds, Tm.eval, Value.toProp]
  | .app f args, σ, h => by
    by_cases hf : f = "and"
    · subst hf
      simp only [flatten] at h
      have := flattenList_holds args σ h
      simp only [Tm.Holds, Tm.eval, applyOp, Value.toProp, Tm.evalList_eq]
      intro v hv
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      exact this t ht
    · have : flatten (.app f args) = [.app f args] := by
        unfold flatten; split <;> simp_all
      exact h _ (by simp [this])
  | .num n, _, h => h _ (by simp [flatten])
  | .ff, _, h => h _ (by simp [flatten])
  | .ivar x, _, h => h _ (by simp [flatten])
  | .bvar x, _, h => h _ (by simp [flatten])
  | .avar x, _, h => h _ (by simp [flatten])
  | .all x b, _, h => h _ (by simp [flatten])
theorem flattenList_holds : ∀ (ts : List Tm) (σ : Env), (∀ c ∈ flattenList ts, c.Holds σ) →
    ∀ t ∈ ts, t.Holds σ
  | [], _, _ => by simp
  | t :: ts, σ, h => by
    simp only [flattenList, List.mem_append] at h
    intro u hu
    cases hu with
    | head => exact flatten_holds t σ fun c hc => h c (Or.inl hc)
    | tail _ hu => exact flattenList_holds ts σ (fun c hc => h c (Or.inr hc)) u hu
end

theorem mem_flattenList {t c : Tm} : ∀ {ts : List Tm}, t ∈ ts → c ∈ flatten t → c ∈ flattenList ts
  | _ :: _, .head _, hc => by simp only [flattenList, List.mem_append]; exact Or.inl hc
  | _ :: _, .tail _ ht, hc => by
    simp only [flattenList, List.mem_append]; exact Or.inr (mem_flattenList ht hc)

/-! ## Range facts -/

/-- The fact that the elements of the array `m` lie in `[0, M]`, as the Lean generator states it of
the arrays of its storage: `(forall ((k Int)) (and (<= 0 (select m k)) (<= (select m k) M)))`. -/
def arrFact (k m : String) (M : Nat) : Tm :=
  .all k (.app "and" [.app "<=" [.num 0, .app "select" [.avar m, .ivar k]],
    .app "<=" [.app "select" [.avar m, .ivar k], .num M]])

/-- An array fact of `m` among `hs` bounds its elements by at most `M`. -/
def arrBound (hs : List Tm) (m : String) (M : Nat) : Bool :=
  hs.any fun h => match h with
    | .all k (.app "and" [.app "<=" [.num 0, .app "select" [.avar m', .ivar k']],
        .app "<=" [.app "select" [.avar m'', .ivar k''], .num M']]) =>
      m' == m && m'' == m && k' == k && k'' == k && decide (M' ≤ M)
    | _ => false

theorem arrBound_sound {hs : List Tm} {m : String} {M : Nat} (h : arrBound hs m M = true)
    {σ : Env} (hh : ∀ x ∈ hs, x.Holds σ) (n : Int) : 0 ≤ σ.a m n ∧ σ.a m n ≤ M := by
  obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp h
  split at hm
  · rename_i k m' k' m'' k'' M'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hM⟩ := hm
    have := hh _ hf
    simp only [Tm.Holds, Tm.eval, Value.toProp] at this
    have := this n
    simp [Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Env.setI] at this
    exact ⟨this.1, Int.le_trans this.2 (by exact_mod_cast hM)⟩
  · simp at hm

/-- `hs` imply `0 ≤ t`, with `fuel` steps: a fact of `hs`, or through an `ite`, a `select` of a
`store` and a `select` of an array whose elements `hs` bound. -/
def lowerOk (hs : List Tm) : Nat → Tm → Bool
  | 0, t => hs.any (·.beq (.app "<=" [.num 0, t]))
  | n + 1, t => hs.any (·.beq (.app "<=" [.num 0, t])) || match t with
    | .app "ite" [_, a, b] => lowerOk hs n a && lowerOk hs n b
    | .app "select" [.app "store" [a, _, v], j] => lowerOk hs n v && lowerOk hs n (.app "select" [a, j])
    | .app "select" [.avar m, _] => hs.any fun h => match h with
      | .all k (.app "and" [.app "<=" [.num 0, .app "select" [.avar m', .ivar k']], _]) =>
        m' == m && k' == k
      | _ => false
    | _ => false

/-- `hs` imply `t ≤ M`, as `lowerOk` does `0 ≤ t`. -/
def upperOk (hs : List Tm) (M : Nat) : Nat → Tm → Bool
  | 0, t => hs.any fun h => match h with
    | .app "<=" [t', .num M'] => t'.beq t && decide (M' ≤ M)
    | _ => false
  | n + 1, t => (hs.any fun h => match h with
    | .app "<=" [t', .num M'] => t'.beq t && decide (M' ≤ M)
    | _ => false) || match t with
    | .app "ite" [_, a, b] => upperOk hs M n a && upperOk hs M n b
    | .app "select" [.app "store" [a, _, v], j] =>
      upperOk hs M n v && upperOk hs M n (.app "select" [a, j])
    | .app "select" [.avar m, _] => arrBound hs m M
    | _ => false

theorem holds_le (σ : Env) (a b : Tm) :
    (Tm.app "<=" [a, b]).Holds σ ↔ (a.eval σ).toInt ≤ (b.eval σ).toInt := by
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp]

theorem eval_select (σ : Env) (a j : Tm) :
    (Tm.app "select" [a, j]).eval σ = .int ((a.eval σ).toArr (j.eval σ).toInt) := by
  simp [Tm.eval, Tm.evalList, applyOp]

theorem eval_store_select (σ : Env) (a i v j : Tm) :
    ((Tm.app "select" [.app "store" [a, i, v], j]).eval σ).toInt =
      if (j.eval σ).toInt = (i.eval σ).toInt then (v.eval σ).toInt
      else ((Tm.app "select" [a, j]).eval σ).toInt := by
  simp only [Tm.eval, Tm.evalList, applyOp, Value.toInt]
  rfl

open Classical in
theorem eval_ite_int (σ : Env) (c a b : Tm) :
    ((Tm.app "ite" [c, a, b]).eval σ).toInt = ((Tm.app "ite" [c, a, b]).eval σ).toInt := rfl

/-- The integer an `ite` takes is one of its branches', whatever their sorts. -/
theorem ite_toInt (σ : Env) (c a b : Tm) :
    ((Tm.app "ite" [c, a, b]).eval σ).toInt = (a.eval σ).toInt ∨
      ((Tm.app "ite" [c, a, b]).eval σ).toInt = (b.eval σ).toInt ∨
      ((Tm.app "ite" [c, a, b]).eval σ).toInt = 0 := by
  simp only [Tm.eval, Tm.evalList]
  cases a.eval σ <;> cases b.eval σ
  all_goals first
    | (simp [applyOp, Value.toInt]; done)
    | (simp only [applyOp, Value.toInt]; split <;> simp)

theorem lowerOk_sound (hs : List Tm) {σ : Env} (hh : ∀ x ∈ hs, x.Holds σ) :
    ∀ n t, lowerOk hs n t = true → 0 ≤ (t.eval σ).toInt := by
  have mem : ∀ t, (hs.any (·.beq (.app "<=" [.num 0, t]))) = true → 0 ≤ (t.eval σ).toInt := by
    intro t h
    obtain ⟨f, hf, he⟩ := List.any_eq_true.mp h
    have := hh f hf
    rw [Tm.eq_of_beq he, holds_le] at this
    simpa [Tm.eval, Value.toInt] using this
  intro n
  induction n with
  | zero => exact fun t h => mem t h
  | succ n ih =>
    intro t h
    simp only [lowerOk, Bool.or_eq_true] at h
    rcases h with h | h
    · exact mem t h
    · split at h
      · rename_i c a b
        simp only [Bool.and_eq_true] at h
        rcases ite_toInt σ c a b with e | e | e <;> rw [e]
        · exact ih a h.1
        · exact ih b h.2
        · exact Int.le_refl 0
      · rename_i a i v j
        simp only [Bool.and_eq_true] at h
        rw [eval_store_select]
        split
        · exact ih v h.1
        · exact ih _ h.2
      · rename_i m j
        obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp h
        split at hm
        · rename_i k m' k' rest
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          have := hh _ hf
          simp only [Tm.Holds, Tm.eval, Value.toProp] at this
          have := this (j.eval σ).toInt
          simp [Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Env.setI] at this
          rw [eval_select]
          simpa [Value.toInt, Tm.eval, Value.toArr] using this.1
        · simp at hm
      · simp at h

theorem upperOk_sound (hs : List Tm) (M : Nat) {σ : Env} (hh : ∀ x ∈ hs, x.Holds σ) :
    ∀ n t, upperOk hs M n t = true → (t.eval σ).toInt ≤ M := by
  have mem : ∀ t, (hs.any fun h => match h with
      | .app "<=" [t', .num M'] => t'.beq t && decide (M' ≤ M)
      | _ => false) = true → (t.eval σ).toInt ≤ M := by
    intro t h
    obtain ⟨f, hf, he⟩ := List.any_eq_true.mp h
    split at he
    · rename_i t' M'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      have := hh _ hf
      rw [Tm.eq_of_beq he.1, holds_le] at this
      simp only [Tm.eval, Value.toInt] at this
      exact Int.le_trans this (by exact_mod_cast he.2)
    · simp at he
  intro n
  induction n with
  | zero => exact fun t h => mem t h
  | succ n ih =>
    intro t h
    simp only [upperOk, Bool.or_eq_true] at h
    rcases h with h | h
    · exact mem t h
    · split at h
      · rename_i c a b
        simp only [Bool.and_eq_true] at h
        rcases ite_toInt σ c a b with e | e | e <;> rw [e]
        · exact ih a h.1
        · exact ih b h.2
        · exact Int.natCast_nonneg M
      · rename_i a i v j
        simp only [Bool.and_eq_true] at h
        rw [eval_store_select]
        split
        · exact ih v h.1
        · exact ih _ h.2
      · rename_i m j
        rw [eval_select]
        exact (arrBound_sound h hh _).2
      · simp at h

/-! ## The check of one obligation -/

/-- A range fact of a constant the Lean obligation does not mention, which 0 satisfies. -/
def defaultOk (V : List String) : Tm → Bool
  | .app "<=" [.num 0, .ivar x] => !V.contains x
  | .app "<=" [.ivar x, .num _] => !V.contains x
  | _ => false

/-- A fact of solar-verify's obligation that the Lean obligation's facts `hs` give. -/
def hypOk (hs : List Tm) (V : List String) (h : Tm) : Bool :=
  hs.any (·.beq h) || defaultOk V h || match h with
    | .app "<=" [.num 0, t] => lowerOk hs 64 t
    | .app "<=" [t, .num M] => upperOk hs M 64 t
    | _ => false

/-- The names the Lean obligation mentions. -/
def leanVars (hs : List Tm) (φ : Tm) : List String := Tm.varsList hs ++ φ.vars

/-- solar-verify's obligation `e` gives the Lean obligation `hs ⟹ φ`. -/
def checkOb (e hs : List Tm) (φ : Tm) : Bool :=
  let e1 := inline e
  e1.all Tm.renameOk &&
  match (e1.map Tm.rename).reverse with
  | .app "not" [φ'] :: rhyps => φ'.beq φ && (flattenList rhyps).all (hypOk hs (leanVars hs φ))
  | _ => false

/-- The assignment that reads as `σ` the names of `V`, and every other name as 0. -/
def Env.restrict (σ : Env) (V : List String) : Env :=
  ⟨fun x => if x ∈ V then σ.i x else 0, fun x => if x ∈ V then σ.b x else False,
    fun x => if x ∈ V then σ.a x else fun _ => 0⟩

theorem Env.restrict_agree (σ : Env) {V : List String} {x : String} (h : x ∈ V) :
    (σ.restrict V).Agree σ x := by
  simp [Env.restrict, Env.Agree, h]

theorem mem_varsList {t : Tm} : ∀ {ts : List Tm}, t ∈ ts → ∀ x ∈ t.vars, x ∈ Tm.varsList ts
  | _ :: _, .head _, x, hx => by simp only [Tm.varsList, List.mem_append]; exact Or.inl hx
  | _ :: _, .tail _ ht, x, hx => by
    simp only [Tm.varsList, List.mem_append]; exact Or.inr (mem_varsList ht x hx)

theorem holds_restrict {σ : Env} {V : List String} {t : Tm} (h : ∀ x ∈ t.vars, x ∈ V) :
    t.Holds (σ.restrict V) ↔ t.Holds σ := by
  simp only [Tm.Holds]
  rw [Tm.eval_congr t fun x hx => Env.restrict_agree σ (h x hx)]

theorem hypOk_sound {hs : List Tm} {φ : Tm} {σ : Env} (hh : ∀ x ∈ hs, x.Holds σ) {h : Tm}
    (ok : hypOk hs (leanVars hs φ) h = true) : h.Holds (σ.restrict (leanVars hs φ)) := by
  have hV : ∀ x ∈ hs, ∀ y ∈ x.vars, y ∈ leanVars hs φ := fun x hx y hy => by
    simp only [leanVars, List.mem_append]; exact Or.inl (mem_varsList hx y hy)
  have hh' : ∀ x ∈ hs, x.Holds (σ.restrict (leanVars hs φ)) := fun x hx =>
    (holds_restrict (hV x hx)).mpr (hh x hx)
  simp only [hypOk, Bool.or_eq_true] at ok
  rcases ok with (ok | ok) | ok
  · obtain ⟨f, hf, he⟩ := List.any_eq_true.mp ok
    rw [← Tm.eq_of_beq he]; exact hh' f hf
  · unfold defaultOk at ok
    split at ok
    · rename_i x
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at ok
      rw [holds_le]; simp [Tm.eval, Env.restrict, ok, Value.toInt]
    · rename_i x M
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at ok
      rw [holds_le]; simp [Tm.eval, Env.restrict, ok, Value.toInt]
    · simp at ok
  · split at ok
    · rename_i t
      rw [holds_le]
      simpa [Tm.eval, Value.toInt] using lowerOk_sound hs hh' 64 t ok
    · rename_i t M _
      rw [holds_le]
      simpa [Tm.eval, Value.toInt] using upperOk_sound hs M hh' 64 t ok
    · simp at ok

theorem checkOb_sound {e hs : List Tm} {φ : Tm} (h : checkOb e hs φ = true)
    (hv : ∀ σ, ¬ Sat σ e) (σ : Env) (hh : ∀ x ∈ hs, x.Holds σ) : φ.Holds σ := by
  simp only [checkOb, Bool.and_eq_true] at h
  obtain ⟨hok, h⟩ := h
  have h2 := rename_sound hok (inline_sound hv)
  split at h
  · rename_i φ' rhyps hr
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hφ, hyps⟩ := h
    have he := Tm.eq_of_beq hφ
    subst he
    have hφV : ∀ x ∈ φ'.vars, x ∈ leanVars hs φ' := fun x hx => by
      simp only [leanVars, List.mem_append]; exact Or.inr hx
    apply Classical.byContradiction
    intro hn
    apply h2 (σ.restrict (leanVars hs φ'))
    intro t ht
    have ht' : t ∈ (Tm.app "not" [φ'] :: rhyps).reverse := by
      rw [← hr, List.reverse_reverse]; exact ht
    rw [List.mem_reverse] at ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · simp only [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp]
      intro hp
      exact hn ((holds_restrict hφV).mp hp)
    · exact flatten_holds t _ fun c hc =>
        hypOk_sound hh (hyps c (mem_flattenList ht' hc))
  · simp at h

/-! ## The check of a script -/

/-- Every Lean obligation `(hs, φ)` is given by one of the script's obligations. -/
def checkScript (cs : List Cmd) (obs : List (List Tm × Tm)) : Bool :=
  let es := (obligations cs).filter (fun e => !isProbe e)
  obs.all fun o => es.any fun e => checkOb e o.1 o.2

/-- What the Lean obligations claim: each one's facts imply its goal. -/
def ObsValid (obs : List (List Tm × Tm)) : Prop :=
  ∀ o ∈ obs, ∀ σ : Env, (∀ x ∈ o.1, x.Holds σ) → o.2.Holds σ

theorem checkScript_sound {cs : List Cmd} {obs : List (List Tm × Tm)}
    (h : checkScript cs obs = true) (hv : Valid cs) : ObsValid obs := by
  intro o ho σ hh
  have := List.all_eq_true.mp h o ho
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp this
  rw [List.mem_filter] at he
  have hp : isProbe e = false := by simpa using he.2
  exact checkOb_sound hc (fun τ hτ => hv e he.1 hp τ hτ) σ hh

/-! ## One function's obligations -/

/-- The commands of the function `name` (`Contract.fn`): those after its `; ===== name` line, up to
the next function's. -/
def fnSlice (cs : List Cmd) (name : String) : List Cmd :=
  let isMark : Cmd → String → Bool := fun c n => match c with
    | .raw l => l == "; ===== " ++ n
    | _ => false
  let isAny : Cmd → Bool := fun c => match c with
    | .raw l => l.startsWith "; ===== "
    | _ => false
  ((cs.dropWhile (fun c => !isMark c name)).drop 1).takeWhile (fun c => !isAny c)

/-- An obligation of solar-verify's, normalized as `checkOb` normalizes it: its facts, flattened,
and its goal. -/
def normOb (e : List Tm) : Option (List Tm × Tm) :=
  let e1 := inline e
  if e1.all Tm.renameOk then
    match (e1.map Tm.rename).reverse with
    | .app "not" [φ] :: rhyps => some (flattenList rhyps, φ)
    | _ => none
  else none

/-- The obligations of the function `name`, normalized, without the probe. -/
def fnObs (cs : List Cmd) (name : String) : List (List Tm × Tm) :=
  ((obligations (fnSlice cs name)).filter (fun e => !isProbe e)).filterMap normOb

end SolidCore.Verify.VC
