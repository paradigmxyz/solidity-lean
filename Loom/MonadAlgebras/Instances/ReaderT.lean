import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

/- Ordered Monad Algebra instance for ReaderT -/
instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ReaderT σ m) (σ -> l) where
  μ := fun rp r => inst.μ $ (· r) <$> rp r
  μ_ord_pure := by
    intros l; simp [pure, ReaderT.pure]; ext r
    solve_by_elim [MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intro α f g le x r
    have leM := inst.μ_ord_bind (α := α) (fun a => (fun y : σ → l => y r) <$> f a r) (fun a => (fun y : σ → l => y r) <$> g a r)
      (fun a => le a r) (x r)
    show MAlgOrdered.μ ((fun y : σ → l => y r) <$> (x r >>= fun a => f a r)) ≤
      MAlgOrdered.μ ((fun y : σ → l => y r) <$> (x r >>= fun a => g a r))
    rw [map_bind, map_bind]; exact leM


instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] [inst': MAlgDet m l]
   : MAlgDet (ReaderT σ m) (σ -> l) where
    angelic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.angelic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h
    demonic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.demonic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h


instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (ReaderT ε m α) := by
  unfold ReaderT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (ReaderT ε m) where
  bind_mono_left h₁₂ _ := by
    simp [bind, ReaderT.bind]
    apply Lean.Order.MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ _ := by
    simp [bind]
    apply Lean.Order.MonoBind.bind_mono_right (m := m)
    intro x; apply h₁₂

/-- solidity-lean (Lean 4.35): the supremum of a chain of readers, at an environment, is the
supremum of their results there. -/
theorem ReaderT.csup_apply [Monad m] [∀ α, Lean.Order.CCPO (m α)] {α : Type u}
    (c : ReaderT ε m α → Prop) (hc : Lean.Order.chain c) (s : ε) :
    (Lean.Order.CCPO.csup hc : ReaderT ε m α) s =
      Lean.Order.CCPO.csup (Lean.Order.chain_apply (β := fun _ : ε => m α) hc s) :=
  congrFun (Lean.Order.fun_csup_eq (β := fun _ : ε => m α) c hc).symm s

theorem ReaderT.bot_apply [Monad m] [∀ α, Lean.Order.CCPO (m α)] {α : Type u} (s : ε) :
    (Lean.Order.bot : ReaderT ε m α) s = Lean.Order.bot := by
  unfold Lean.Order.bot
  rw [ReaderT.csup_apply]
  apply Lean.Order.is_sup_unique (Lean.Order.CCPO.csup_spec _)
  intro x; constructor
  · intro _ y hy; obtain ⟨f, hf, _⟩ := hy; exact hf.elim
  · intro _; apply Lean.Order.csup_le; intro y hy; exact hy.elim

instance [Monad m] [CCPOBot m] : CCPOBot (ReaderT σ m) where
  compBot := fun _ => CCPOBot.compBot

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ReaderT σ m) where
  prop {α} := by
    funext s
    rw [ReaderT.bot_apply]
    exact CCPOBotLawful.prop (m := m)

lemma MAlg.lift_ReaderT [Monad m] [LawfulMonad m] [CompleteLattice l] [inst: MAlgOrdered m l] (x : ReaderT σ m α) :
  MAlg.lift x post = fun s => MAlg.lift (x s) (fun xs => post xs s) := by
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ]

open Lean.Order
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ReaderT σ m) where
  csup_lift {α} chain := by
    intro post hchain s
    simp only [MAlg.lift_ReaderT, iInf_apply]
    erw [ReaderT.csup_apply]
    apply le_trans' (MAlgPartial.csup_lift (m := m) _ _ _)
    refine le_iInf₂ ?_
    rintro y ⟨f, hf, rfl⟩
    exact iInf₂_le f hf

attribute [-simp] le_bot_iff in
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)]  [MonoBind m]
  [MAlgTotal m] : MAlgTotal (ReaderT σ m) where
  bot_lift {α} post := by
    intro s
    simp only [MAlg.lift_ReaderT]
    rw [ReaderT.bot_apply]
    exact MAlgTotal.bot_lift (m := m) _

instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [inst': NoFailure m] : NoFailure (ReaderT σ m) where
  noFailure := by
    intro _ _; simp [MAlg.lift_ReaderT, inst'.noFailure]; rfl

/- Monad Transformer Algebra instance for ReaderT -/
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l] :
  MAlgLift m l (ReaderT σ m) (σ -> l) where
    μ_lift := by
      intro α f x
      rw [MAlg.lift_ReaderT]
      funext s
      rfl
