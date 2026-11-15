import Verify.Spec.Contract

/-!
# Ghost-free specs ignore ghosts

A term that reads no ghost variable, through the spec functions it calls (`Term.GhostFree`), has the
same value in two environments that differ only in their ghost states (`Env.ghostEquiv`). So a
ghost-free spec clause cannot tell a run with ghost code apart from its erasure, which only changes
ghost state (`Ghost.sound`).
-/

namespace SolidCore.Spec

namespace Env.ghostEquiv

theorem refl (e : Env) : e.ghostEquiv e := by
  simp [Env.ghostEquiv]

theorem symm {e e' : Env} (h : e.ghostEquiv e') : e'.ghostEquiv e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm⟩

theorem storage {e e' : Env} (h : e.ghostEquiv e') : e.cur.storage = e'.cur.storage := by
  obtain ⟨-, -, -, -, h5, h6, -, h8, -⟩ := h
  simp only [Env.cur, h5]; split <;> assumption

theorem time {e e' : Env} (h : e.ghostEquiv e') : e.cur.time = e'.cur.time := by
  obtain ⟨-, -, -, -, h5, -, h7, -, h9⟩ := h
  simp only [Env.cur, h5]; split <;> assumption

theorem bind {e e' : Env} (h : e.ghostEquiv e') (x : String) (v : Int) :
    (e.bind x v).ghostEquiv (e'.bind x v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, by simp [Env.bind, h4], h5, h6, h7, h8, h9⟩

theorem old {e e' : Env} (h : e.ghostEquiv e') :
    ({ e with inOld := true } : Env).ghostEquiv { e' with inOld := true } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, rfl, h6, h7, h8, h9⟩

theorem withVars {e e' : Env} (h : e.ghostEquiv e') (vs : List (String × Int)) :
    ({ e with vars := vs } : Env).ghostEquiv { e' with vars := vs } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, rfl, h5, h6, h7, h8, h9⟩

end Env.ghostEquiv

/-- What `k` promises of the spec function bodies at one fuel level: they ignore ghosts when
evaluated with one less fuel. -/
def BodiesIgnoreGhosts (fns : List SpecFn) (fuel : Nat) (k : Term → Bool) : Prop :=
  ∀ body, k body = true → ∀ fuel', fuel = fuel' + 1 →
    ∀ e e', e.ghostEquiv e' → eval fns fuel' body e = eval fns fuel' body e'

mutual
theorem eval_ghostEquiv_with {fns : List SpecFn} {fuel : Nat} {k : Term → Bool}
    (hk : BodiesIgnoreGhosts fns fuel k) :
    ∀ (t : Term), Term.ghostFreeWith fns k t = true →
      ∀ e e', e.ghostEquiv e' → eval fns fuel t e = eval fns fuel t e'
  | .lit _, _, e, e', h => by simp only [eval]
  | .arg _, _, e, e', h => by simp only [eval, h.1]
  | .ret _, _, e, e', h => by simp only [eval, h.2.1]
  | .var _, _, e, e', h => by simp only [eval, h.2.2.2.1]
  | .env v, _, e, e', h => by
    cases v <;> simp only [eval, h.2.2.1, h.time]
  | .load p off size ty, hg, e, e', h => by
    simp only [Term.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [eval, h.storage, slotOf_ghostEquiv_with hk p hg.1 e e' h,
      eval_ghostEquiv_with hk off hg.2 e e' h]
  | .len p, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    simp only [eval, h.storage, slotOf_ghostEquiv_with hk p hg e e' h]
  | .ghost _ _, hg, _, _, _ => by simp [Term.ghostFreeWith] at hg
  | .old t, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    simp only [eval]; exact eval_ghostEquiv_with hk t hg _ _ h.old
  | .un op t, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    cases op <;> simp only [eval, eval_ghostEquiv_with hk t hg e e' h]
  | .bin op a b, hg, e, e', h => by
    simp only [Term.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [eval, eval_ghostEquiv_with hk a hg.1 e e' h, eval_ghostEquiv_with hk b hg.2 e e' h]
  | .shl t _, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    simp only [eval, eval_ghostEquiv_with hk t hg e e' h]
  | .shr t _, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    simp only [eval, eval_ghostEquiv_with hk t hg e e' h]
  | .ite c a b, hg, e, e', h => by
    simp only [Term.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [eval, eval_ghostEquiv_with hk c hg.1.1 e e' h, eval_ghostEquiv_with hk a hg.1.2 e e' h,
      eval_ghostEquiv_with hk b hg.2 e e' h]
  | .all x _ body, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    have hb : ∀ v, eval fns fuel body (e.bind x v) = eval fns fuel body (e'.bind x v) :=
      fun v => eval_ghostEquiv_with hk body hg _ _ (h.bind x v)
    simp only [eval, hb]
  | .ex x _ body, hg, e, e', h => by
    simp only [Term.ghostFreeWith] at hg
    have hb : ∀ v, eval fns fuel body (e.bind x v) = eval fns fuel body (e'.bind x v) :=
      fun v => eval_ghostEquiv_with hk body hg _ _ (h.bind x v)
    simp only [eval, hb]
  | .call f args, hg, e, e', h => by
    simp only [Term.ghostFreeWith, Bool.and_eq_true] at hg
    have ha := evalList_ghostEquiv_with hk args hg.1 e e' h
    obtain ⟨-, hb⟩ := hg
    cases fuel with
    | zero => rw [eval.eq_def, eval.eq_def]
    | succ fuel' =>
      cases hf : fns.find? (·.name == f) with
      | none => rw [eval.eq_def, eval.eq_def]; simp only [hf]
      | some sf =>
        rw [hf] at hb
        rw [eval.eq_def, eval.eq_def]; simp only [hf, ha]
        exact hk sf.body hb fuel' rfl _ _ (h.withVars _)
termination_by t => sizeOf t

theorem evalList_ghostEquiv_with {fns : List SpecFn} {fuel : Nat} {k : Term → Bool}
    (hk : BodiesIgnoreGhosts fns fuel k) :
    ∀ (ts : List Term), Term.ghostFreeListWith fns k ts = true →
      ∀ e e', e.ghostEquiv e' → evalList fns fuel ts e = evalList fns fuel ts e'
  | [], _, e, e', _ => by simp only [evalList]
  | t :: ts, hg, e, e', h => by
    simp only [Term.ghostFreeListWith, Bool.and_eq_true] at hg
    simp only [evalList, eval_ghostEquiv_with hk t hg.1 e e' h,
      evalList_ghostEquiv_with hk ts hg.2 e e' h]
termination_by ts => sizeOf ts

theorem slotOf_ghostEquiv_with {fns : List SpecFn} {fuel : Nat} {k : Term → Bool}
    (hk : BodiesIgnoreGhosts fns fuel k) :
    ∀ (p : Place), Place.ghostFreeWith fns k p = true →
      ∀ e e', e.ghostEquiv e' → slotOf fns fuel p e = slotOf fns fuel p e'
  | .slot _, _, e, e', _ => by simp only [slotOf]
  | .offset b i, hg, e, e', h => by
    simp only [Place.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [slotOf, slotOf_ghostEquiv_with hk b hg.1 e e' h, eval_ghostEquiv_with hk i hg.2 e e' h]
  | .entry b i, hg, e, e', h => by
    simp only [Place.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [slotOf, slotOf_ghostEquiv_with hk b hg.1 e e' h, eval_ghostEquiv_with hk i hg.2 e e' h]
  | .elem b i _, hg, e, e', h => by
    simp only [Place.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [slotOf, slotOf_ghostEquiv_with hk b hg.1 e e' h, eval_ghostEquiv_with hk i hg.2 e e' h]
  | .packedElem b i _, hg, e, e', h => by
    simp only [Place.ghostFreeWith, Bool.and_eq_true] at hg
    simp only [slotOf, slotOf_ghostEquiv_with hk b hg.1 e e' h, eval_ghostEquiv_with hk i hg.2 e e' h]
termination_by p => sizeOf p
end

/-- A ghost-free term has the same value in two environments that differ only in their ghost
states: a spec that reads no ghost cannot tell ghost code apart from its erasure. -/
theorem eval_ghostEquiv {fns : List SpecFn} :
    ∀ (fuel : Nat) {t : Term}, Term.GhostFree fns fuel t = true →
      ∀ {e e' : Env}, e.ghostEquiv e' → eval fns fuel t e = eval fns fuel t e'
  | 0, t, hg, e, e', h => by
    refine eval_ghostEquiv_with ?_ t hg e e' h
    intro _ _ fuel' h0; cases h0
  | n + 1, t, hg, e, e', h => by
    refine eval_ghostEquiv_with ?_ t hg e e' h
    intro body hb fuel' hf _ _ h'
    cases hf
    exact eval_ghostEquiv n hb h'

/-- A ghost-free clause holds in one environment exactly when it holds in another that differs only
in its ghost state. -/
theorem Bundle.sat_ghostEquiv (b : Bundle) {t : Term} (hg : Term.GhostFree b.spec.fns b.fuel t = true)
    {e e' : Env} (h : e.ghostEquiv e') : b.sat t e ↔ b.sat t e' := by
  simp only [Bundle.sat, eval_ghostEquiv b.fuel hg h]

end SolidCore.Spec
