import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

/- Ordered Monad Algebra instance for StateT -/
instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (StateT σ m) (σ -> l) where
  μ := (MAlgOrdered.μ $ (fun fs => fs.1 fs.2) <$> · ·)
  μ_ord_pure := by
    intro f; funext s₁
    show MAlgOrdered.μ ((fun fs : (σ → l) × σ => fs.1 fs.2) <$> (pure (f, s₁) : m _)) = f s₁
    rw [map_pure, MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intro α f g le x s
    have leM := inst.μ_ord_bind (α := α × σ)
      (fun as => (fun fs : (σ → l) × σ => fs.1 fs.2) <$> f as.1 as.2)
      (fun as => (fun fs : (σ → l) × σ => fs.1 fs.2) <$> g as.1 as.2)
      (fun as => le as.1 as.2) (x s)
    show MAlgOrdered.μ ((fun fs : (σ → l) × σ => fs.1 fs.2) <$> (x s >>= fun p => f p.1 p.2)) ≤
      MAlgOrdered.μ ((fun fs : (σ → l) × σ => fs.1 fs.2) <$> (x s >>= fun p => g p.1 p.2))
    rw [map_bind, map_bind]; exact leM

instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] [inst': MAlgDet m l]
   : MAlgDet (StateT σ m) (σ -> l) where
    angelic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, StateT.map]
      have h := inst'.angelic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MAlg.lift, MAlg.μ] at h
      apply h
    demonic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, StateT.map]
      have h := inst'.demonic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MAlg.lift, MAlg.μ] at h
      apply h

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (StateT ε m α) := by
  unfold StateT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (StateT ε m) where
  bind_mono_left h₁₂ _ := by
    simp [bind, StateT.bind]
    apply Lean.Order.MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ _ := by
    simp [bind, StateT.bind]
    apply Lean.Order.MonoBind.bind_mono_right (m := m)
    intro x; apply h₁₂

/-- solidity-lean (Lean 4.35): the supremum of a chain of state transformers, at a state, is
the supremum of their results there; `CCPO.csup` is now a choice, so this replaces unfolding
it to `fun_csup`. -/
theorem StateT.csup_apply [Monad m] [∀ α, Lean.Order.CCPO (m α)] {α : Type u}
    (c : StateT ε m α → Prop) (hc : Lean.Order.chain c) (s : ε) :
    (Lean.Order.CCPO.csup hc : StateT ε m α) s =
      Lean.Order.CCPO.csup (Lean.Order.chain_apply (β := fun _ : ε => m (α × ε)) hc s) :=
  congrFun (Lean.Order.fun_csup_eq (β := fun _ : ε => m (α × ε)) c hc).symm s

theorem StateT.bot_apply [Monad m] [∀ α, Lean.Order.CCPO (m α)] {α : Type u} (s : ε) :
    (Lean.Order.bot : StateT ε m α) s = Lean.Order.bot := by
  unfold Lean.Order.bot
  rw [StateT.csup_apply]
  apply Lean.Order.is_sup_unique (Lean.Order.CCPO.csup_spec _)
  intro x; constructor
  · intro _ y hy; obtain ⟨f, hf, _⟩ := hy; exact hf.elim
  · intro _; apply Lean.Order.csup_le; intro y hy; exact hy.elim

instance [Monad m] [CCPOBot m] : CCPOBot (StateT σ m) where
  compBot := fun _ => CCPOBot.compBot

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (StateT σ m) where
  prop {α} := by
    funext s
    rw [StateT.bot_apply]
    exact CCPOBotLawful.prop (m := m)


lemma MAlg.lift_StateT [Monad m] [LawfulMonad m] [CompleteLattice l] [inst: MAlgOrdered m l] (x : StateT σ m α) :
  MAlg.lift x post = fun s => MAlg.lift (x s) (fun xs => post xs.1 xs.2) := by
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ, StateT.map]

open Lean.Order
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (StateT σ m) where
  csup_lift {α} chain := by
    intro post hchain s
    simp only [MAlg.lift_StateT, iInf_apply]
    erw [StateT.csup_apply]
    apply le_trans' (MAlgPartial.csup_lift (m := m) _ _ _)
    refine le_iInf₂ ?_
    rintro y ⟨f, hf, rfl⟩
    exact iInf₂_le f hf

attribute [-simp] le_bot_iff in
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)]  [MonoBind m]
  [MAlgTotal m] : MAlgTotal (StateT σ m) where
  bot_lift {α} post := by
    intro s
    simp only [MAlg.lift_StateT]
    rw [StateT.bot_apply]
    exact MAlgTotal.bot_lift (m := m) _

instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [inst': NoFailure m] : NoFailure (StateT σ m) where
  noFailure := by
    intro _ _; simp [MAlg.lift_StateT, inst'.noFailure]; rfl

/- Monad Transformer Algebra instance for StateT -/
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l] :
  MAlgLift m l (StateT σ m) (σ -> l) where
    μ_lift := by
      intro α f x
      rw [MAlg.lift_StateT]
      funext s
      show MAlg.lift (liftM (n := StateT σ m) x s) (fun xs => f xs.1 xs.2) = MAlg.lift x (f · s)
      simp only [MAlg.lift, liftM, monadLift, MonadLift.monadLift, StateT.lift, map_bind, map_pure]
      rw [map_eq_pure_bind]
