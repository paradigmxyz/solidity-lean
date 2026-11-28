import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.Instances.StateT

/-!
# An error-aware algebra for `ExceptT`

Loom's `ExceptT` algebra (`MAlgExcept`) fixes, by a handler, what an exception means:
`ε → Prop` once and for all. Here the assertion instead takes the predicate an exception must
meet as an argument: over an algebra of `m` on `l`, `ExceptT ε m` has an ordered algebra on
`(ε → l) → l`. Its weakest precondition, given `herr`, is the weakest precondition of `m`
for the postcondition on a result and `herr` on an exception, so one weakest precondition
covers both outcomes, which is what a specification of a reverting call needs.

The same construction is given directly for `Except ε`, the monad of a state program that
fails with data (`StateT σ (Except ε)`), whose assertions are then, by Loom's `StateT`
algebra, `σ → (ε → Prop) → Prop`.
-/

universe u v

section ExceptTErr

variable {ε : Type u} {l : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [CompleteLattice l] [inst : MAlgOrdered m l]

/-- What an outcome means for an error-aware assertion, given the exception predicate. -/
def Except.errAssn (herr : ε → l) : Except ε ((ε → l) → l) → l
  | .ok p => p herr
  | .error e => herr e

/-- The error-aware ordered algebra of `ExceptT ε m` on `(ε → l) → l`. -/
noncomputable def MAlgExceptErr : MAlgOrdered (ExceptT ε m) ((ε → l) → l) where
  μ x := fun herr => inst.μ (Except.errAssn herr <$> (x : m _))
  μ_ord_pure := by
    intro p; funext herr
    show inst.μ (Except.errAssn herr <$> (pure (Except.ok p) : m _)) = p herr
    rw [map_pure]; exact MAlgOrdered.μ_ord_pure _
  μ_ord_bind := by
    intro α f g hfg x herr
    show inst.μ (Except.errAssn herr <$> ((x : m (Except ε α)) >>= ExceptT.bindCont f)) ≤
      inst.μ (Except.errAssn herr <$> ((x : m (Except ε α)) >>= ExceptT.bindCont g))
    rw [map_bind, map_bind]
    apply inst.μ_ord_bind
    rintro (e | a)
    · exact le_refl _
    · exact hfg a herr

attribute [local instance] MAlgExceptErr

theorem MAlgExceptErr.lift_eq (c : ExceptT ε m α) (post : α → (ε → l) → l) (herr : ε → l) :
    MAlg.lift c post herr =
      MAlg.lift (m := m) (c : m (Except ε α)) (fun | .ok a => post a herr | .error e => herr e) := by
  show inst.μ (Except.errAssn herr <$> (ExceptT.map post c : m _)) = inst.μ (_ <$> (c : m _))
  simp only [ExceptT.map, ExceptT.mk, map_bind]
  rw [map_eq_pure_bind]
  apply MAlgOrdered.bind; funext r; cases r <;> simp [Except.errAssn]

end ExceptTErr

/-! ## `Except ε` directly -/

section ExceptErr

variable {ε : Type u}

/-- What an outcome means for an error-aware assertion on `Prop`. -/
def Except.errProp (herr : ε → Prop) : Except ε ((ε → Prop) → Prop) → Prop
  | .ok p => p herr
  | .error e => herr e

/-- The error-aware ordered algebra of `Except ε` on `(ε → Prop) → Prop`. -/
instance MAlgExceptErrProp : MAlgOrdered (Except ε) ((ε → Prop) → Prop) where
  μ x := fun herr => Except.errProp herr x
  μ_ord_pure := by intro p; rfl
  μ_ord_bind := by
    intro α f g hfg x herr
    cases x with
    | error e => exact le_refl _
    | ok a => exact hfg a herr

theorem MAlgExceptErrProp.lift_eq (c : Except ε α) (post : α → (ε → Prop) → Prop)
    (herr : ε → Prop) :
    MAlg.lift c post herr = match c with
      | .ok a => post a herr
      | .error e => herr e := by
  cases c <;> rfl

instance : MAlgDet (Except ε) ((ε → Prop) → Prop) where
  demonic := by
    intro α ι c p _ herr
    simp only [iInf_apply, MAlgExceptErrProp.lift_eq]
    cases c with
    | error e => simp
    | ok a => simp
  angelic := by
    intro α ι c p _ herr
    simp only [iSup_apply, MAlgExceptErrProp.lift_eq]
    cases c with
    | error e => simp
    | ok a => simp

end ExceptErr
