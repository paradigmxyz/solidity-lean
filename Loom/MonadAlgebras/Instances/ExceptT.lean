import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

abbrev Except.getD {ε α} (default : ε -> α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error e => default e

abbrev Except.bind' {m : Type u -> Type v} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type u -> Type v} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, ExceptT.bind]; rfl

/- Ordered Monad Algebra instance for ExceptT -/
noncomputable
def MAlgExcept (ε : Type u) (df : ε -> Prop) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD (⌜df ·⌝) <$> e
  μ_ord_pure := by
    intro l
    show inst.μ (Except.getD (⌜df ·⌝) <$> (pure (Except.ok l) : m _)) = l
    rw [map_pure]; exact MAlgOrdered.μ_ord_pure _
  μ_ord_bind := by
    intro α f g le x
    have leM := inst.μ_ord_bind (α := Except ε α)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x f)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x g) ?_ x
    · simp only [← map_bind, Except.bind'_bind] at leM; exact leM
    · rintro (e | p)
      · show inst.μ (Except.getD (⌜df ·⌝) <$> (ExceptT.mk (pure (Except.error e) >>= ExceptT.bindCont f) : m _)) ≤
          inst.μ (Except.getD (⌜df ·⌝) <$> (ExceptT.mk (pure (Except.error e) >>= ExceptT.bindCont g) : m _))
        simp only [ExceptT.mk, pure_bind, ExceptT.bindCont]; exact le_refl _
      · show inst.μ (Except.getD (⌜df ·⌝) <$> (ExceptT.mk (pure (Except.ok p) >>= ExceptT.bindCont f) : m _)) ≤
          inst.μ (Except.getD (⌜df ·⌝) <$> (ExceptT.mk (pure (Except.ok p) >>= ExceptT.bindCont g) : m _))
        simp only [ExceptT.mk, pure_bind, ExceptT.bindCont]; exact le p

section ExeceptHandler

variable (ε : Type u) (l : Type u) (m : Type u -> Type v) [Monad m] [LawfulMonad m]

class IsHandler {ε : Type*} (handler : outParam (ε -> Prop)) where

set_option linter.unusedVariables false in
noncomputable
instance OfHd {hd : ε -> Prop} [hdInst : IsHandler hd]
  [CompleteLattice l] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l := MAlgExcept ε hd l m


lemma MAlg.lift_ExceptT ε (hd : ε -> Prop) [IsHandler hd] [CompleteLattice l] [inst: MAlgOrdered m l]
   (c : ExceptT ε m α) post :
  MAlg.lift c post = MAlg.lift (m := m) c (fun | .ok x => post x | .error e => ⌜hd e⌝) := by
    show MAlgOrdered.μ (Except.getD (⌜hd ·⌝) <$> (ExceptT.map post c : m _)) =
      MAlgOrdered.μ ((fun (r : Except ε α) => match r with
        | .ok x => post x | .error e => ⌜hd e⌝) <$> (c : m _))
    simp only [ExceptT.map, ExceptT.mk, map_bind]
    rw [map_eq_pure_bind]; apply MAlgOrdered.bind; funext a; cases a <;> simp [Except.getD]


instance MAlgExceptHdDet (hd : ε -> Prop)
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler hd]
  [inst': MAlgDet m l] : MAlgDet (ExceptT ε m) l where
  angelic := by
    intro α ι c p _
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p := fun i e => match e with
        | Except.ok a => p i a
        | Except.error e => ⌜hd e⌝)
    simp only [MAlg.lift_ExceptT (l := l) (m := m) (hd := hd)]
    refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_))
    · congr 1; funext e; cases e <;> simp [iSup_const]
    · congr 1; funext i; congr 1; funext e; cases e <;> rfl
  demonic := by
    intro α ι c p _
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p := fun i e => match e with
        | Except.ok a => p i a
        | Except.error e => ⌜hd e⌝)
    simp only [MAlg.lift_ExceptT (l := l) (m := m) (hd := hd)]
    refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_))
    · congr 1; funext i; congr 1; funext e; cases e <;> rfl
    · congr 1; funext e; cases e <;> simp [iInf_const]

instance
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler (fun (_ : ε) => True)]
  [inst': NoFailure m] : NoFailure (ExceptT ε m) where
  noFailure := by
    intro α c
    rw [MAlg.lift_ExceptT (l := l) (m := m) (hd := fun _ => True)]
    rw (occs := [2]) [← inst'.noFailure (c := c)]
    congr 1; funext e; cases e <;> simp [LE.pure]

/- Monad Transformer Algebra instance for ExceptT -/
noncomputable
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [IsHandler (ε := ε) hd]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (ExceptT ε m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intro α f x
      rw [MAlg.lift_ExceptT (l := l) (m := m) (hd := hd)]
      show MAlgOrdered.μ (_ <$> (Except.ok <$> x : m _)) = MAlgOrdered.μ (f <$> x)
      rw [Functor.map_map]

end ExeceptHandler

namespace ExceptionAsSuccess
scoped instance PartialHandler {ε} : IsHandler (ε := ε) fun _ => True where
end ExceptionAsSuccess

namespace ExceptionAsFailure
scoped instance TotalHandler {ε} : IsHandler (ε := ε) fun _ => False where
end ExceptionAsFailure

open Lean.Order

instance [Monad m] [inst : ∀ α, CCPO (m α)] : CCPO (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : MonoBind (ExceptT ε m) where
  bind_mono_left h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

instance [Monad m] [CCPOBot m] : CCPOBot (ExceptT ε m) where
  compBot := CCPOBot.compBot (m := m)

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ExceptT ε m) where
  prop := CCPOBotLawful.prop (m := m)

instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ExceptT ε m) where
  csup_lift {α} chain := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgPartial.csup_lift (m := m)]

attribute [-simp] le_bot_iff in
instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgTotal m] : MAlgTotal (ExceptT ε m) where
  bot_lift := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgTotal.bot_lift (m := m)]
