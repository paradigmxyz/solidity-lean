import Verify.LoopSource.Equiv.CounterCtor
import SolidCore.Refinement.Generic.CtorAll

/-!
# Challenge: Counter's admission and load-level deployment for every word

The exact statements, each with `sorry`: a statement file only. Nothing imports it and no proof
uses it. `Verify.LoopSource.Equiv.CounterAllAudit` checks each proved declaration in
`Verify.LoopSource.Equiv.CounterLoad` against its statement here with `example`.
-/

namespace Verify.LoopSource.Equiv.CounterAllChallenge

open SolidCore.Refinement.Generic

theorem counter_admits_all : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract}, Contracts.VerifyCounter.Source.contract? = .ok c → ∀ {n : Nat}, n < 2 ^ 256 → CtorAdmits c Verify.LoopSource.Equiv.CounterCtor.counterInit (Verify.Lifecycle.initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [n]) [n] := sorry

theorem counter_deployedAtLoad : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract}, Contracts.VerifyCounter.Source.contract? = .ok c → ∀ {n : Nat}, n < 2 ^ 256 → ∃ d, DeployedAtLoad Contracts.VerifyCounter.Source.fuel c [n] [(1, n)] d := sorry

end Verify.LoopSource.Equiv.CounterAllChallenge
