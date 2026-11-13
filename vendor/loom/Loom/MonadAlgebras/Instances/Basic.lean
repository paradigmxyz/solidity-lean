import Loom.MonadAlgebras.Defs
universe u v w

instance : MAlgOrdered Id Prop where
  μ := id
  μ_ord_pure := by simp [pure]
  μ_ord_bind := by solve_by_elim

instance : MAlgDet Id Prop where
  demonic := by
    intros α c p q;
    simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ]
    solve_by_elim
  angelic := by
    intros α c p q;
    simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ]
    solve_by_elim

inductive DivM (α : Type u) where
  | res (x : α)
  | div

def DivM.run {α : Type u} [Inhabited α] : DivM α -> α
  | DivM.res x => x
  | DivM.div => default

instance : Monad DivM where
  pure := DivM.res
  bind := fun x y => match x with
    | DivM.res x => y x
    | DivM.div => DivM.div

class CCPOBot (m : Type u -> Type v)  where
  compBot {α} : m α

class CCPOBotLawful (m : Type u -> Type v) [∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] where
  prop {α} : CCPOBot.compBot (m := m) (α := α) = Lean.Order.bot

instance : LawfulMonad DivM := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; cases x <;> rfl }
  { introv; rfl }
  introv; cases x <;> rfl

noncomputable instance : Lean.Order.CCPO (DivM α) := inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder .div))
/-- solidity-lean (Lean 4.35): the supremum of a chain of `DivM` is the flat order's. -/
theorem DivM.csup_eq {α : Type u} (c : DivM α → Prop) (hc : Lean.Order.chain c) :
    Lean.Order.CCPO.csup hc = Lean.Order.flat_csup (b := (DivM.div : DivM α)) c :=
  (Lean.Order.flat_csup_eq (b := (DivM.div : DivM α)) c hc).symm

instance : CCPOBot DivM where
  compBot := .div

instance : CCPOBotLawful DivM where
  prop {α} := by
    show (DivM.div : DivM α) = Lean.Order.CCPO.csup (Lean.Order.chain_empty _)
    rw [DivM.csup_eq]
    simp [Lean.Order.flat_csup, Lean.Order.empty_chain]; rfl

instance : Lean.Order.MonoBind DivM where
  bind_mono_left := by
    rintro _ _ (_|_) _ _ (_|_) <;> solve_by_elim
  bind_mono_right := by
    rintro _ _ (_|_) <;> solve_by_elim

namespace PartialCorrectness


scoped instance : MAlgOrdered DivM Prop where
  μ := fun x => match x with
    | .res x => x
    | .div => ⊤
  μ_ord_pure := by intro; rfl
  μ_ord_bind {α} f g := by
    rintro h (_|_)
    · exact h _
    · exact le_refl _

scoped instance : MAlgDet DivM Prop where
  demonic := by
    rintro _ _ (_|_) <;> simp [MAlg.lift, MAlgOrdered.μ, Functor.map]
  angelic := by
    rintro _ _ (_|_) <;> simp [MAlg.lift, MAlgOrdered.μ, Functor.map]

instance : MAlgPartial DivM where
  csup_lift {α} chain := by
    intro post hchain
    erw [DivM.csup_eq]
    simp only [Lean.Order.flat_csup]
    split_ifs with ch
    · exact iInf₂_le _ (Classical.choose_spec ch).1
    · exact fun _ => trivial

instance : NoFailure DivM where
  noFailure := by
    rintro _ (_|_) <;> simp [MAlg.lift, MAlgOrdered.μ, Functor.map]

end PartialCorrectness

namespace TotalCorrectness

scoped instance : MAlgOrdered DivM Prop where
  μ := fun x => match x with
    | .res x => ⌜x⌝
    | .div => ⊥
  μ_ord_pure := by intro l; show ⌜l⌝ = l; simp [LE.pure]
  μ_ord_bind {α} f g := by
    rintro h (_|_)
    · exact h _
    · exact le_refl _

scoped instance : MAlgDet DivM Prop where
  angelic := by
    rintro _ _ (_|_) <;> simp [MAlg.lift, MAlgOrdered.μ, Functor.map, LE.pure]
  demonic := by
    rintro _ _ (_|_) <;> simp [MAlg.lift, MAlgOrdered.μ, Functor.map, LE.pure]

instance : MAlgTotal DivM where
  bot_lift {α} post := by
    rw [← CCPOBotLawful.prop (m := DivM)]
    exact fun h => h

end TotalCorrectness
