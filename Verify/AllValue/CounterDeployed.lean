import Verify.LoopSource.Equiv.CounterComposedAll
import Verify.Partial.CounterAny
import Verify.AllValue.CounterValue
import SolidCore.Refinement.Generic.StageFromValue

/-!
# Counter's runtime statements, created and deployed, for every constructor argument word

`Verify.Partial.CounterAny.counter_partial_any` and `Verify.AllValue.CounterValue.counter_nonpayable`
are runtime-only: their source side is SolidCore's runtime code from the call's storage
(`Loop.solidCoreRuntimeFrom`, `Loop.runtimeRunFrom`), and the init code is not part of them. This
module composes each with the creation, for every word `n < 2 ^ 256`:

* the creation bytes `initArgs counterInit [n]` are typed-admitted for the source's checked contract
  with exactly `[n]` (`Source.CreatedBy`, `CounterLoad.counter_admits_all`);
* the lifecycle statement (`CounterExact.counter_lifecycle_all`): EthLib runs those creation bytes
  to success, returns the exact runtime bytes the runtime statements are about
  (`CounterSame.code_eq`) and leaves the storage `[(1, n)]`, and SolidCore's constructor on `[n]`
  leaves exactly `[(1, n)]` and no logs;
* the source side is the deployed source, `(src n).semAt ctx`: SolidCore's constructor on `[n]`,
  then the call from `ctx.caller` against the state it left with the call's storage written over it.

Statements:

* `counter_partial_deployed`: `counter_partial_any`'s three parts with the deployed source, for
  every call storage that writes slot 1 when `n ≠ 0` (`CounterCtx.CoverN`, the load cover; without
  it the deployed source and the runtime code differ: `CounterLoad.cover_needed`);
* `counter_partial_created`: the same for the first call after the creation, whose storage is the
  one the creation left (`[(1, n)]`), with the bytecode's `Deploys` of that storage;
* `counter_nonpayable_deployed`: a nonzero value is rejected by the deployed source (any call
  storage; the dispatcher refuses before the body reads storage) and by the bytes from `G0` on;
* `counter_all_value` (runtime, both values in one statement) and `counter_all_value_deployed`
  (the same, created and deployed).

The bounds are the runtime statements': part 3 of the partial statement says nothing where
`G a ≥ 2 ^ 256` (`CounterAny.control_empty`); the creation frame is the one
`SolidCore.Refinement.Deploy` fixes (no value, no address derivation or code deposit); the argument
is one static word.
-/

namespace Verify.AllValue.CounterDeployed
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Solar Contracts.VerifyCounter.Source SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterCtx Verify.LoopSource.Equiv.CounterCtor
open Verify.AllValue.CounterValue (bumpCallV G0)

/-- The exact runtime bytes the runtime statements are about. -/
abbrev code : ByteArray := runtimeCode SolarTV.Export.Counter.bytecode

/-- The creation bytes of Counter with the word `n`. -/
abbrev creation (n : Nat) : ByteArray := Verify.Lifecycle.initArgs counterInit [n]

/-! ## The creation, for every word -/

/-- The creation half for every word: typed admission and the lifecycle statement on `code`. -/
theorem created {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256) :
    (src n).CreatedBy c counterInit (creation n) ∧
      Verify.Lifecycle.Statement fuel c counterInit code [n] [(1, n)] := by
  have hl := Verify.LoopSource.Equiv.CounterExact.counter_lifecycle_all hc hn
  rw [← Verify.LoopSource.Equiv.CounterSame.code_eq] at hl
  exact ⟨Verify.LoopSource.Equiv.CounterLoad.counter_admits_all hc hn, hl⟩

/-! ## The deployed source -/

/-- **The deployed source equals the runtime code on load-covering calls**, from every caller below
`2 ^ 160`: both run `bump(a)` to the same observable. -/
theorem deployed_eq_runtime {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) (ctx : Context) (hctx : ctx.Ok) {σ : List (Nat × Nat)} (hcov : CoverN n σ)
    {a : Nat} (ha : a < 2 ^ 256) :
    ((src n).semAt ctx).run c (Verify.LoopSource.MirLink.bumpCall σ a) =
      (Loop.solidCoreRuntimeFrom ctx.caller fuel).run c (Verify.LoopSource.MirLink.bumpCall σ a) := by
  obtain ⟨d, hd, hld⟩ := Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed hc hn
  have h1 := src_run hc hd hld ctx.caller hcov ha
  have h2 := Verify.Partial.CounterAny.src_run_rt hc ctx.caller hctx.1 σ ha
  exact h1.trans h2.symm

/-- **The deployed source rejects a nonzero value**, from every caller, for every call storage. -/
theorem source_rejects_deployed {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) (x : Nat) (σ : List (Nat × Nat)) {a v : Nat} (ha : a < 2 ^ 256)
    (hv : v < 2 ^ 256) (hv0 : v ≠ 0) :
    SolidCore.Refinement.Source.runFromArgs x fuel [n] c (bumpCallV σ a v) = some (Abi.rejected σ) := by
  obtain ⟨d, hd, -⟩ := Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed hc hn
  obtain ⟨vs, hdep⟩ := hd.cons
  have hfind := (Contracts.VerifyCounter.Source.shape_of hc).2.2
  have hw : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [2 ^ 256 - 1] := rfl
  have hargs : ∀ v ∈ [a], v < 2 ^ 256 := by simpa using ha
  have hclean : argsClean [2 ^ 256 - 1] [a] = true := by
    show (decide (a < 2 ^ 256) && true) = true
    simp only [Bool.and_true, decide_eq_true_eq]; exact ha
  have hdec : Source.ABI.decodeFunctionArgs? bumpFn (Dirty.argBytes [a]) = .ok ([a].map .word) := by
    rw [decode_args hw [a] rfl hargs, if_pos hclean]
  have hs : bumpSel < 2 ^ 32 := by decide
  have hsel : Source.ABI.readSelector? (callBytes (bumpCallV σ a v)) = some bumpSel := by
    simp only [callBytes, bumpCallV, Dirty.bytes_calldata, Dirty.readSelector_calldata _ hs]
  have hargs' : Source.ABI.decodeFunctionArgs? bumpFn
      ((callBytes (bumpCallV σ a v)).drop Source.ABI.selectorBytes) = .ok ([a].map .word) := by
    simp only [callBytes, bumpCallV, Dirty.bytes_calldata]
    rw [show ((EthLib.Base.natToBytes 4 bumpSel).map (·.toNat) ++ Dirty.argBytes [a]).drop
        Source.ABI.selectorBytes = Dirty.argBytes [a] by
      simp [Source.ABI.selectorBytes, EthLib.Base.natToBytes_length]]
    exact hdec
  have hvm : v % SolidCore.Solidity.Shared.wordModulus = v := Nat.mod_eq_of_lt hv
  have hvn : SolidCore.Solidity.Shared.norm (bumpCallV σ a v).callvalue ≠ 0 := by
    simpa [SolidCore.Solidity.Shared.norm, bumpCallV, hvm] using hv0
  have hr := resultFromArgs?_value_rejected (caller := x) hdep hsel hfind hargs' rfl hvn
  unfold SolidCore.Refinement.Source.runFromArgs
  rw [hr]
  simp [SolidCore.Refinement.Source.observe, Abi.rejected, bumpCallV]

/-! ## Partial correctness, created and deployed -/

/-- **Counter.bump, partial correctness of the created and deployed source from every caller.**
For the checked contract `c` and every word `n < 2 ^ 256`: the creation bytes with `n` are
typed-admitted for `c` with exactly `[n]`, and the lifecycle statement holds on the exact runtime
bytes with the storage `[(1, n)]`. Then for every context `ctx.Ok`, every call storage `σ` that
writes slot 1 when `n ≠ 0` and every argument word `a < 2 ^ 256`, with one call `bumpCall σ a`
(value 0), one source result `obs` of the deployed source `(src n).semAt ctx` such that:

1. the deployed source runs to `obs`, `obs` is allowed and meets `BumpPost`;
2. at every gas, every bytecode result is `obs`, or an inert failure at a gas below `G a`;
3. at every gas from `G a` on below `2 ^ 256`, the bytecode runs to `obs`. -/
theorem counter_partial_deployed :
    ∃ c, contract? = .ok c ∧ ∀ n : Nat, n < 2 ^ 256 →
      (src n).CreatedBy c counterInit (creation n) ∧
      Verify.Lifecycle.Statement fuel c counterInit code [n] [(1, n)] ∧
      ∀ ctx : Context, ctx.Ok → ∀ (σ : List (Nat × Nat)) (a : Nat), CoverN n σ → a < 2 ^ 256 →
        let call := Verify.LoopSource.MirLink.bumpCall σ a
        ∃ obs, ((src n).semAt ctx).run c call = some obs ∧ allowed call obs ∧
          Verify.LoopSource.MirLink.BumpPost call obs ∧
          (∀ gas : Nat, ∀ obs', runAt ctx gas code call = some obs' →
            obs' = obs ∨ (gas < G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
          (∀ gas : Nat, G a ≤ gas → gas < 2 ^ 256 → runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc, H⟩ := Verify.Partial.CounterAny.counter_partial_any
  refine ⟨c, hc, fun n hn => ⟨(created hc hn).1, (created hc hn).2, fun ctx hctx σ a hcov ha => ?_⟩⟩
  obtain ⟨obs, hrun, hal, hpost, hb, hf⟩ := H ctx hctx σ a ha
  exact ⟨obs, (deployed_eq_runtime hc hn ctx hctx hcov ha).trans hrun, hal, hpost, hb, hf⟩

/-- **The first call after the creation**: for every word `n < 2 ^ 256`, the creation bytes deploy
the exact runtime bytes with the storage `[(1, n)]`, and `counter_partial_deployed`'s three parts
hold for `bump(a)` on that storage, for every context `ctx.Ok` and argument word `a < 2 ^ 256`. -/
theorem counter_partial_created :
    ∃ c, contract? = .ok c ∧ ∀ n : Nat, n < 2 ^ 256 →
      (src n).CreatedBy c counterInit (creation n) ∧
      SolidCore.Refinement.Deploys (creation n) code [(1, n)] ∧
      ∀ ctx : Context, ctx.Ok → ∀ a : Nat, a < 2 ^ 256 →
        let call := Verify.LoopSource.MirLink.bumpCall [(1, n)] a
        ∃ obs, ((src n).semAt ctx).run c call = some obs ∧ allowed call obs ∧
          Verify.LoopSource.MirLink.BumpPost call obs ∧
          (∀ gas : Nat, ∀ obs', runAt ctx gas code call = some obs' →
            obs' = obs ∨ (gas < G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
          (∀ gas : Nat, G a ≤ gas → gas < 2 ^ 256 → runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc, H⟩ := counter_partial_deployed
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨hcb, hl, H'⟩ := H n hn
  have hsc : (src n).checked = .ok c := (src_checked n).trans hc
  refine ⟨hcb, (Source.run_of_statement (src := src n) hsc hcb hl).1, fun ctx hctx a ha => ?_⟩
  exact H' ctx hctx [(1, n)] a (fun _ => ⟨(1, n), List.mem_singleton_self _, rfl⟩) ha

/-! ## Non-payable, created and deployed -/

/-- **Counter is non-payable, created and deployed.** For the checked contract `c` and every word
`n < 2 ^ 256`: the creation half as above, and for every context `ctx.Ok`, every call storage `σ`,
every argument `a < 2 ^ 256` and every value `0 < v < 2 ^ 256`, the deployed source rejects
`bump(a)` (failure, no output, no logs, storage `σ`), and EthLib runs the exact runtime bytes from
`ctx.caller` to that same observable at every gas from `G0` on. -/
theorem counter_nonpayable_deployed :
    ∃ c, contract? = .ok c ∧ ∀ n : Nat, n < 2 ^ 256 →
      (src n).CreatedBy c counterInit (creation n) ∧
      Verify.Lifecycle.Statement fuel c counterInit code [n] [(1, n)] ∧
      ∀ ctx : Context, ctx.Ok → ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 →
        v ≠ 0 →
        ((src n).semAt ctx).run c (bumpCallV σ a v) = some (Abi.rejected σ) ∧
          ∀ gas, G0 ≤ gas → runAt ctx gas code (bumpCallV σ a v) = some (Abi.rejected σ) := by
  obtain ⟨c, hc⟩ := Contracts.VerifyCounter.Source.contract_ok
  refine ⟨c, hc, fun n hn => ⟨(created hc hn).1, (created hc hn).2,
    fun ctx hctx σ a v ha hv hv0 => ⟨?_, ?_⟩⟩⟩
  · exact source_rejects_deployed hc hn ctx.caller σ ha hv hv0
  · exact ((Verify.AllValue.CounterValue.counter_nonpayable c hc ctx hctx σ a v ha hv hv0).2)

/-! ## Every value -/

/-- **Counter at every call value, runtime only**: `counter_partial_any` at value 0 and
`counter_nonpayable` at every other value, in one statement over `bumpCallV σ a v`. -/
theorem counter_all_value :
    ∃ c, contract? = .ok c ∧ ∀ ctx : Context, ctx.Ok →
      ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 →
        (v = 0 →
          let call := bumpCallV σ a v
          ∃ obs, (Loop.solidCoreRuntimeFrom ctx.caller fuel).run c call = some obs ∧
            allowed call obs ∧ Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', runAt ctx gas code call = some obs' →
              obs' = obs ∨ (gas < G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, G a ≤ gas → gas < 2 ^ 256 → runAt ctx gas code call = some obs)) ∧
        (v ≠ 0 →
          Loop.runtimeRunFrom ctx.caller fuel c (bumpCallV σ a v) = some (Abi.rejected σ) ∧
            ∀ gas, G0 ≤ gas → runAt ctx gas code (bumpCallV σ a v) = some (Abi.rejected σ)) := by
  obtain ⟨c, hc, H⟩ := Verify.Partial.CounterAny.counter_partial_any
  refine ⟨c, hc, fun ctx hctx σ a v ha hv => ⟨fun hv0 => ?_, fun hv0 => ?_⟩⟩
  · subst hv0
    exact H ctx hctx σ a ha
  · exact Verify.AllValue.CounterValue.counter_nonpayable c hc ctx hctx σ a v ha hv hv0

/-- **Counter at every call value, created and deployed.** For the checked contract `c` and every
word `n < 2 ^ 256`: the creation half (typed admission of `[n]` and the lifecycle statement on the
exact runtime bytes with storage `[(1, n)]`), and for every context `ctx.Ok`, call storage `σ`,
argument `a < 2 ^ 256` and value `v < 2 ^ 256`: at value 0 on a storage writing slot 1 when
`n ≠ 0`, `counter_partial_deployed`'s three parts; at any other value, the deployed source and the
bytes (from `G0`) reject the call. -/
theorem counter_all_value_deployed :
    ∃ c, contract? = .ok c ∧ ∀ n : Nat, n < 2 ^ 256 →
      (src n).CreatedBy c counterInit (creation n) ∧
      Verify.Lifecycle.Statement fuel c counterInit code [n] [(1, n)] ∧
      ∀ ctx : Context, ctx.Ok → ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 →
        (v = 0 → CoverN n σ →
          let call := bumpCallV σ a v
          ∃ obs, ((src n).semAt ctx).run c call = some obs ∧ allowed call obs ∧
            Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', runAt ctx gas code call = some obs' →
              obs' = obs ∨ (gas < G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, G a ≤ gas → gas < 2 ^ 256 → runAt ctx gas code call = some obs)) ∧
        (v ≠ 0 →
          ((src n).semAt ctx).run c (bumpCallV σ a v) = some (Abi.rejected σ) ∧
            ∀ gas, G0 ≤ gas → runAt ctx gas code (bumpCallV σ a v) = some (Abi.rejected σ)) := by
  obtain ⟨c, hc, H⟩ := counter_partial_deployed
  obtain ⟨c', hc', H'⟩ := counter_nonpayable_deployed
  have e : c' = c := by
    rw [hc] at hc'
    injection hc' with h
    exact h.symm
  rw [e] at H'
  refine ⟨c, hc, fun n hn => ⟨(H n hn).1, (H n hn).2.1, fun ctx hctx σ a v ha hv =>
    ⟨fun hv0 hcov => ?_, fun hv0 => ?_⟩⟩⟩
  · subst hv0
    exact (H n hn).2.2 ctx hctx σ a hcov ha
  · exact (H' n hn).2.2 ctx hctx σ a v ha hv hv0

end Verify.AllValue.CounterDeployed

/-- info: 'Verify.AllValue.CounterDeployed.source_rejects_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.source_rejects_deployed

/-- info: 'Verify.AllValue.CounterDeployed.counter_partial_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.counter_partial_deployed

/-- info: 'Verify.AllValue.CounterDeployed.counter_partial_created' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.counter_partial_created

/-- info: 'Verify.AllValue.CounterDeployed.counter_nonpayable_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.counter_nonpayable_deployed

/-- info: 'Verify.AllValue.CounterDeployed.counter_all_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.counter_all_value

/-- info: 'Verify.AllValue.CounterDeployed.counter_all_value_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterDeployed.counter_all_value_deployed
