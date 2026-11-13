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

class CCPOBot (m : Type u -> Type v)  where
  compBot {α} : m α

class CCPOBotLawful (m : Type u -> Type v) [∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] where
  prop {α} : CCPOBot.compBot (m := m) (α := α) = Lean.Order.bot

-- solidity-lean: Loom's DivM (the divergence monad) and its partial- and
-- total-correctness algebras are dropped; see vendor/loom/README.md.
