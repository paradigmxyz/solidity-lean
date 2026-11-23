import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter's expected theorem with its creation

`counter_expected_created` is `counter_expected`'s `Expected` together with the creation
conjunct the composed statement needs, for one witness `c` of the source's own checked contract
(`(src n).checked = .ok c`): the creation bytes `initArgs counterInit [n]` are typed-admitted for
`c`'s constructor with exactly the source's arguments (`Source.CreatedBy`), and those arguments are
`[n]`. `created_args_unique`: no other source is created by the same bytes with other arguments.
-/

namespace Verify.LoopSource.Equiv.CounterCreated

open SolidCore.Refinement.Generic SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterCtx Verify.LoopSource.Equiv.CounterCtor

/-- The creation bytes of Counter deployed with `[n]`. -/
abbrev creation (n : Nat) : ByteArray := Verify.Lifecycle.initArgs counterInit [n]

/-- **Expected, and the creation at the same checked witness.** -/
theorem counter_expected_created {n : Nat} (hn : n = 5 ∨ n = 8) {K : Nat} (hK : K ≤ Kmax) :
    Expected (src n) (spec n K) SolarTV.Export.Counter.bytecode ∧
      ∃ c, (src n).checked = .ok c ∧ (src n).CreatedBy c counterInit (creation n) ∧
        (src n).ctorArgs = [n] := by
  refine ⟨(counter_expected hn hK).1, ?_⟩
  obtain ⟨c, hc⟩ := Contracts.VerifyCounter.Source.contract_ok
  exact ⟨c, (src_checked n).trans hc, counter_admits hc hn, rfl⟩

/-- **No other arguments**: a source created by Counter's creation bytes for `[n]` has arguments
`[n]`. -/
theorem created_args_unique {n : Nat} (hn : n = 5 ∨ n = 8) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : (src n).checked = .ok c) {ws : List Nat} {src' : Source ws}
    (h' : src'.CreatedBy c counterInit (creation n)) : src'.ctorArgs = [n] :=
  Source.CreatedBy.unique (src := src') (src' := src n) h'
    (show (src n).CreatedBy c counterInit (creation n) from
      counter_admits ((src_checked n).symm.trans hc) hn)

end Verify.LoopSource.Equiv.CounterCreated

/-- info: 'Verify.LoopSource.Equiv.CounterCreated.counter_expected_created' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCreated.counter_expected_created
