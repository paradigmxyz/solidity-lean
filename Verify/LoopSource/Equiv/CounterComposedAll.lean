import Verify.LoopSource.Equiv.CounterExact
import Verify.LoopSource.Equiv.CounterCreated

/-!
# Counter's composed statement with its creation, for every constructor argument word

`CounterCtx.counter_expected` and `CounterCreated.counter_expected_created` are stated for the
pinned words `n ∈ {5, 8}`, and take the lifecycle statement as a premise. Every piece they use
holds for every word `n < 2 ^ 256`:

* the load-level deployment `CounterLoad.counter_load_deployed` and `CounterCtx.certifiedAt`;
* the typed admission `CounterLoad.counter_admits_all`;
* the lifecycle statement `CounterExact.counter_lifecycle_all` (the bytecode's `Deploys`, from one
  kernel evaluation of the symbolic creation frame, and SolidCore's `DeployedAtWith`), whose runtime
  bytes `CounterSame.runtime` are the expected theorem's (`CounterSame.code_eq`).

So this module states, for every `n < 2 ^ 256`:

* `counter_expected_all`: `Expected (src n) (spec n K)` on the exact runtime bytes, `K ≤ Kmax`;
* `counter_composed_all`: the shape of the driver's generated `Composed.composed`
  (`generic.py composed_lean`) with the words free: `Expected`, and at one checked contract `c` of
  the source, `Source.CreatedBy` for the creation bytes `initArgs counterInit [n]`, the lifecycle
  statement with the storage `[(1, n)]` and the deployment of the runtime bytes by those creation
  bytes, with no lifecycle premise left;
* `created_args_unique_all`: no other source is created by the same bytes with other arguments.

Bounds kept from the parts: the argument is one static word; the creation frame is the one
`SolidCore.Refinement.Deploy` fixes (no value, no address derivation or code deposit); valid calls
are `CounterCtx.valid n K` (`bump(a)`, `a ≤ K`, value 0, storage writing slot 1 when `n ≠ 0`).
-/

namespace Verify.LoopSource.Equiv.CounterComposedAll

open SolidCore.Refinement.Generic SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterCtx Verify.LoopSource.Equiv.CounterCtor

/-- **Expected for every argument word**: `CounterCtx.counter_expected`'s first conjunct with
`n < 2 ^ 256` in place of `n ∈ {5, 8}`. -/
theorem counter_expected_all {n : Nat} (hn : n < 2 ^ 256) {K : Nat} (hK : K ≤ Kmax) :
    Expected (src n) (spec n K) SolarTV.Export.Counter.bytecode := by
  refine ⟨by decide, covered n K, fun _ ctx hctx => ?_⟩
  obtain ⟨c, hc⟩ := Contracts.VerifyCounter.Source.contract_ok
  obtain ⟨d, hd, hl⟩ := Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed hc hn
  exact ⟨c, hc, certifiedAt hK hc hd hl ctx hctx⟩

/-- **The composed statement for every argument word**: for every `n < 2 ^ 256` and `K ≤ Kmax`,
Counter's `Expected` on the exact runtime bytes, and at one checked contract `c` of its source:
the source is created by solar's init code with exactly the arguments `[n]` (`Source.CreatedBy`),
the lifecycle statement holds with the storage `[(1, n)]` (EthLib's creation returns the runtime
bytes with that storage, and SolidCore's constructor on `[n]` leaves exactly those entries and no
logs), and the creation bytes deploy the runtime bytes with that storage. -/
theorem counter_composed_all {n : Nat} (hn : n < 2 ^ 256) {K : Nat} (hK : K ≤ Kmax) :
    Expected (src n) (spec n K) SolarTV.Export.Counter.bytecode ∧
      ∃ c, (src n).checked = .ok c ∧
        (src n).CreatedBy c counterInit (Verify.Lifecycle.initArgs counterInit [n]) ∧
        Verify.Lifecycle.Statement (src n).fuel c counterInit
          (runtimeCode SolarTV.Export.Counter.bytecode) [n] [(1, n)] ∧
        SolidCore.Refinement.Deploys (Verify.Lifecycle.initArgs counterInit [n])
          (runtimeCode SolarTV.Export.Counter.bytecode) [(1, n)] := by
  refine ⟨counter_expected_all hn hK, ?_⟩
  obtain ⟨c, hc⟩ := Contracts.VerifyCounter.Source.contract_ok
  have hl := Verify.LoopSource.Equiv.CounterExact.counter_lifecycle_all hc hn
  rw [← Verify.LoopSource.Equiv.CounterSame.code_eq] at hl
  have hcb := Verify.LoopSource.Equiv.CounterLoad.counter_admits_all hc hn
  have hsc : (src n).checked = .ok c := (src_checked n).trans hc
  exact ⟨c, hsc, hcb, hl, (Source.run_of_statement (src := src n) hsc hcb hl).1⟩

/-- **No other arguments, for every word**: a source created by Counter's creation bytes for `[n]`
has arguments `[n]`. -/
theorem created_args_unique_all {n : Nat} (hn : n < 2 ^ 256)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : (src n).checked = .ok c) {ws : List Nat}
    {src' : Source ws} (h' : src'.CreatedBy c counterInit (Verify.Lifecycle.initArgs counterInit [n])) :
    src'.ctorArgs = [n] :=
  Source.CreatedBy.unique (src := src') (src' := src n) h'
    (show (src n).CreatedBy c counterInit (Verify.Lifecycle.initArgs counterInit [n]) from
      Verify.LoopSource.Equiv.CounterLoad.counter_admits_all ((src_checked n).symm.trans hc) hn)

/-- The pinned row is an instance: `n = 8` is below `2 ^ 256`. -/
example {K : Nat} (hK : K ≤ Kmax) :
    Expected (src 8) (spec 8 K) SolarTV.Export.Counter.bytecode ∧
      ∃ c, (src 8).checked = .ok c ∧
        (src 8).CreatedBy c counterInit (Verify.Lifecycle.initArgs counterInit [8]) ∧
        Verify.Lifecycle.Statement (src 8).fuel c counterInit
          (runtimeCode SolarTV.Export.Counter.bytecode) [8] [(1, 8)] ∧
        SolidCore.Refinement.Deploys (Verify.Lifecycle.initArgs counterInit [8])
          (runtimeCode SolarTV.Export.Counter.bytecode) [(1, 8)] :=
  counter_composed_all (by decide) hK

end Verify.LoopSource.Equiv.CounterComposedAll

/-- info: 'Verify.LoopSource.Equiv.CounterComposedAll.counter_expected_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterComposedAll.counter_expected_all

/-- info: 'Verify.LoopSource.Equiv.CounterComposedAll.counter_composed_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterComposedAll.counter_composed_all

/-- info: 'Verify.LoopSource.Equiv.CounterComposedAll.created_args_unique_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterComposedAll.created_args_unique_all
