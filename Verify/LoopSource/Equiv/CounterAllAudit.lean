import Verify.LoopSource.Equiv.CounterLoad

/-!
# Audit: Counter's every-word statements against the Challenge

Each proved declaration is checked against its statement in
`Verify.LoopSource.Equiv.CounterAllChallenge`, copied verbatim, with `example`.
-/

open SolidCore.Refinement.Generic

example : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract}, Contracts.VerifyCounter.Source.contract? = .ok c → ∀ {n : Nat}, n < 2 ^ 256 → CtorAdmits c Verify.LoopSource.Equiv.CounterCtor.counterInit (Verify.Lifecycle.initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [n]) [n] := Verify.LoopSource.Equiv.CounterLoad.counter_admits_all

example : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract}, Contracts.VerifyCounter.Source.contract? = .ok c → ∀ {n : Nat}, n < 2 ^ 256 → ∃ d, DeployedAtLoad Contracts.VerifyCounter.Source.fuel c [n] [(1, n)] d := Verify.LoopSource.Equiv.CounterLoad.counter_deployedAtLoad

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_admits_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_admits_all

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_deployedAtLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_deployedAtLoad
