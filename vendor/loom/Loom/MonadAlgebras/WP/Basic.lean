import Loom.MonadAlgebras.Defs

import Loom.MonadAlgebras.Instances.Basic

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}

section
variable [CompleteLattice l]
section
variable [mprop : MAlgOrdered m l]

/- WP definition -/
def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
/- Hoare triple definition -/
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post

/- WP of pure (defintion 4 from the paper) -/
lemma wp_pure (x : α) (post : α -> l) : wp (m := m) (pure x) post = post x := by
  simp [wp, liftM]
  rfl

/- WP of bind (defintion 5 from the paper) -/
lemma triple_pure (pre : l) (x : α) (post : α -> l) :
  triple pre (pure (f := m) x) post <-> pre ≤ (post x)
  := by
    rw [triple, wp]; simp [liftM]; rfl

end

variable [MAlgOrdered m l]

lemma wp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
    wp (x >>= f) post = wp x (fun x => wp (f x) post) := by
    simp [wp, liftM]; rfl

lemma wp_map {β} (x : m α) (f : α -> β) (post : β -> l) :
  wp (f <$> x) post = wp x (fun x => post (f x)) := by
    rw [map_eq_pure_bind, wp_bind]; simp [wp_pure]

/- monotonicity for WP (definition 9 from the paper) -/
lemma wp_cons (x : m α) (post post' : α -> l) :
  (∀ y, post y ≤ post' y) ->
  wp x post ≤ wp x post' := by
    intros h; simp [wp, liftM, monadLift]; apply Cont.monotone_lift; intros y
    apply h

lemma triple_cons (x : m α) {pre pre' : l} {post post' : α -> l} :
  pre' ≤ pre ->
  (∀ y, post y ≤ post' y) ->
  triple pre x post ->
  triple pre' x post' := by
    intros hpre hpost h
    apply le_trans'; apply wp_cons; apply hpost
    solve_by_elim [le_trans]

lemma triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]

omit [LawfulMonad m] in
@[simp]
lemma wp_top (c : m α) [NoFailure m] :
  wp c (fun _ => ⊤) = ⊤ := by
    simp [wp, liftM, monadLift, NoFailure.noFailure]

end

section
variable [CompleteLattice l] [MAlgOrdered m l]

noncomputable
def spec (pre : l) (post : α -> l) : Cont l α :=
  fun p => pre ⊓ ⌜post ≤ p⌝

lemma triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec pre post <= wp c <->
  triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp [trueE] }
    intro t p; unfold spec
    by_cases h: post ≤ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    have : (post ≤ p) = False := by simp [h]
    simp [this, falseE]

end

section Determinism

variable [inst: CompleteLattice l] [MAlgOrdered m l]

lemma wp_iInf {ι : Type u} [Nonempty ι] [MAlgDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨅ i, post i x) = ⨅ i, wp c (post i) := by
    apply le_antisymm
    { refine le_iInf ?_; intros i; apply wp_cons; intro y
      exact iInf_le (fun i ↦ post i y) i }
    apply MAlgDet.demonic

lemma wp_and [MAlgDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊓ post₂ x) = wp c post₁ ⊓ wp c post₂ := by
  apply le_antisymm
  { simp; constructor <;> apply wp_cons <;> simp }
  have h := MAlgDet.demonic (l := l) (ι := ULift Bool) (c := c) (p := fun | .up true => post₁ | .up false => post₂)
  simp at h
  apply le_trans; apply le_trans'; apply h
  { simp [wp]; constructor; exact inf_le_right
    exact inf_le_left }
  apply wp_cons (m := m); simp; intros; constructor
  { refine iInf_le_of_le true ?_; simp }
  refine iInf_le_of_le false ?_; simp

lemma wp_iSup {ι : Type u} [Nonempty ι] [MAlgDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨆ i, post i x) = ⨆ i, wp c (post i) := by
    apply le_antisymm
    { apply MAlgDet.angelic }
    refine iSup_le ?_; intros i; apply wp_cons; intro y
    exact le_iSup (fun i ↦ post i y) i


lemma wp_or [MAlgDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊔ post₂ x) = wp c post₁ ⊔ wp c post₂ := by
  apply le_antisymm
  { have h := MAlgDet.angelic (l := l) (ι := ULift Bool) (c := c) (p := fun | .up true => post₁ | .up false => post₂)
    simp [-iSup_le_iff] at h
    apply le_trans; apply le_trans'; apply h
    { apply wp_cons (m := m); simp; intros; constructor
      { refine le_iSup_of_le true ?_; simp }
      refine le_iSup_of_le false ?_; simp }
    simp [wp]; constructor; exact le_sup_right
    exact le_sup_left }
  simp; constructor <;> apply wp_cons <;> simp


end Determinism


-- solidity-lean: the loop, lifting, ExceptT, StateT, ReaderT and Gen sections of
-- this file are dropped with the transformer instances; see vendor/loom/README.md.
