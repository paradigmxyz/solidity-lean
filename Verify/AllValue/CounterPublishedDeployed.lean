import verify_counter.Final
import Verify.LoopSource.Equiv.CounterLoad
import Verify.Lifecycle.Symbolic

/-!
# The published verify_counter statement, on the created and deployed source

`Certified.verify_counter.Final.final` (solar's generated `verify_counter/shape.json`) is stated on
`Loop.solidCoreRuntime fuel`, SolidCore's runtime code from the call's storage; its `excluded` list
says "deployment: the init code is not covered". This module moves it onto the created and deployed
source, for every constructor word `n < 2 ^ 256`, with no premise.

It imports neither `CounterExact` nor `CounterCtx`: those reach the LoopSource cone's copy of the
Counter export (`Verify.LoopSource.Equiv.Counter.gen.Counter.Bytecode`), which declares the same
`SolarTV.Export.Counter.bytecode` as the published run's `verify_counter.gen.Counter.Bytecode`, so
the two cannot be imported together. The bytecode half is therefore its own kernel evaluation of
the symbolic creation frame on the published bytes (`published_symCheck`), and the source half is
the load-level deployment (`CounterLoad.counter_load_deployed`), which is what the deployed
source runs from.

* `certified_transfer`: `Shapes.Certified` moves to another source semantics and a smaller
  inhabited precondition on which the two sources agree (nothing about Counter);
* `deployed_eq_runtime_fixed`: from the published statement's fixed caller, Counter deployed with
  `[n]` (`solidCoreFromArgs callerAddress fuel [n]`: SolidCore's constructor on `[n]`, then the call
  against the state it left with the call's storage written over it) runs every `ValidS` call whose
  storage writes slot 1 when `n ≠ 0` (`CoverN`) as the runtime code does;
* `published_deploys_all`: EthLib runs `publishedInit` (solar's init code for `verify_counter.sol`,
  whose returned bytes the kernel checks) with the encoded `n` to success, returns the published
  runtime bytes `Final.code` and leaves the storage `[(1, n)]`; `counterInit_not_published`: the
  LoopSource cone's pinned init code does not;
* `verify_counter_deployed`: for every `n < 2 ^ 256`, typed admission of exactly `[n]`, that
  deployment, SolidCore's constructor on `[n]` leaving a state with no logs that loads `n` at slot 1
  and 0 elsewhere, and `Shapes.Certified` for the deployed source with the published bytes, allowed
  statuses, specification and gas bound, on `ValidS` calls with the load cover.

The cover is a real restriction: `CounterLoad.cover_needed` shows a call whose storage omits
slot 1 on which the deployed source and the runtime code differ.
-/

namespace Verify.AllValue.CounterPublishedDeployed
open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop
open Contracts.VerifyCounter.Source

/-- The call writes slot 1 when the deployment's `n` is nonzero (`CounterCtx.CoverN`'s body). -/
def CoverN (n : Nat) (σ : List (Nat × Nat)) : Prop := n ≠ 0 → ∃ kv ∈ σ, kv.1 % 2 ^ 256 = 1

theorem coversLoad {n : Nat} {d : SolidCore.Solidity.Source.State}
    (hl : ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0)
    {σ : List (Nat × Nat)} (h : CoverN n σ) : CoversLoad d σ := by
  intro k hk
  rw [hl k] at hk
  split at hk
  · rename_i h1
    obtain ⟨kv, hm, he⟩ := h hk
    exact ⟨kv, hm, by show kv.1 % 2 ^ 256 = k % 2 ^ 256; rw [he, h1]⟩
  · exact absurd rfl hk

/-- **`Shapes.Certified` moves along an agreeing source**: from `S` on `V` to `S'` on an
inhabited `V' ⊆ V` on which `S'` and `S` give the same result. -/
theorem certified_transfer {S S' : Sem} {p : S.Prog} {p' : S'.Prog} {code : ByteArray}
    {V V' : Call → Prop} {A P : Call → Observable → Prop} {G : Call → Nat}
    (h : Shapes.Certified S p code V A P G) (hi : ∃ call, V' call) (hv : ∀ call, V' call → V call)
    (hrun : ∀ call, V' call → S'.run p' call = S.run p call) :
    Shapes.Certified S' p' code V' A P G := by
  refine ⟨hi, fun gas hg call hc obs hobs => ?_, fun call hc => ?_, fun call hc obs hobs => ?_,
    fun call hc => ?_⟩
  · rw [hrun call hc]; exact h.equiv gas hg call (hv call hc) obs hobs
  · rw [hrun call hc]; exact h.terminates call (hv call hc)
  · rw [hrun call hc] at hobs; exact h.meets call (hv call hc) obs hobs
  · rw [hrun call hc]; exact h.resources call (hv call hc)

/-- A covered `ValidS` call is a load-covering call of `bump`. -/
theorem selCallLoad {n : Nat} {d : SolidCore.Solidity.Source.State}
    (hl : ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0) {call : Call}
    (hv : Contracts.VerifyCounter.ShapeSource.ValidS call) (hcov : CoverN n call.storage) :
    SelCallLoad bumpSel bumpFn [2 ^ 256 - 1] d call := by
  obtain ⟨σ, a, ha, rfl⟩ := hv
  have ha' : a < 2 ^ 256 := lt_trans ha (by decide)
  refine ⟨⟨σ, [a], ⟨rfl, ?_, ?_⟩, rfl⟩, coversLoad hl hcov⟩
  · simpa using ha'
  · show (decide (a < 2 ^ 256) && true) = true
    simp only [Bool.and_true, decide_eq_true_eq]; exact ha'

/-- **From the fixed caller, the deployed source is the runtime code on covered `ValidS` calls.** -/
theorem deployed_eq_runtime_fixed {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256) {call : Call}
    (hv : Contracts.VerifyCounter.ShapeSource.ValidS call) (hcov : CoverN n call.storage) :
    (solidCoreFromArgs callerAddress fuel [n]).run c call = (solidCoreRuntime fuel).run c call := by
  obtain ⟨d, hd, H⟩ := Verify.LoopSource.Equiv.CounterLoad.counter_semAt_eq_runtime_all hc hn
  obtain ⟨d', hd', hl⟩ := Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed hc hn
  obtain rfl := Verify.LoopSource.Equiv.CounterLoad.loadDeployed_unique hd hd'
  exact H call (selCallLoad hl hv hcov)

/-! ## The bytecode half on the published bytes -/

/-- Solar's init code for `verify_counter.sol` (`-Ogas --evm-version osaka`), 556 bytes: a 60-byte
constructor followed by the 496 published runtime bytes. It is the `bin` of a solar build whose
`bin-runtime` is byte-for-byte `Final.runtimeHex`; that provenance is not trusted, since
`published_symCheck` checks in the kernel that this code returns exactly `Final.code`. -/
def publishedInit : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat 3630700961472003563256557910689601933156171886836011784700556264913698877811325895007796421303096130615806984007039064260108374341957246557378702778023382068991930617846625530443973304370948861023405802388024017499829025304981740406784037684670220758025406047157062351396974537632932522995085042957324459090784684254735985525546039610239132626820541580162519263300161745336921603473654825561877059504812719350266481803832885454670217599298067668910263406267779343704327791818567268620371541194243021216571995780697048051832623247604573475994114973186388866970431235063933318640550935720934125867144528876758211125913522430027146748580185116372188874676633606884019955056429124497430186275109396586772635398504124072387487506833375907278661102353767166064118002943491108928751920783832018993562575181081630930943308764606497272336272535443042237791428545069514419410734784429840960511516203338961230128993073035533057583745891641324432520476643813068644273964578938285503260303770525692752620744509737985361234056397091283567280323876905809578415693749721975492857516304106214524393477132757193047051703114047661425856004300020961439898069435811655491768502047759898701680637496311400897223041627097453053633005818731265796000118556463360010157530935206736532909243899413285287800302781238039029077609796766159072488306949946187320477693526 556

section Bytecode
open Verify.Lifecycle.Creation.Sym

set_option maxRecDepth 100000 in
/-- One kernel evaluation of the symbolic creation frame on `publishedInit` with one argument word:
no path condition, the returned code is the published runtime bytes with no argument byte in it,
and the one storage write is the argument word at slot 1. -/
theorem published_symCheck : symCheck 4096 publishedInit 1 []
    (patched Certified.verify_counter.Final.code []) [(1, .arg 0)] = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Control**: the LoopSource cone's pinned init code (`CounterCtor.counterInit`, a different
compile whose runtime is `CounterSame.runtime`) does not deploy the published bytes. -/
theorem counterInit_not_published : symCheck 4096 Verify.LoopSource.Equiv.CounterCtor.counterInit 1 []
    (patched Certified.verify_counter.Final.code []) [(1, .arg 0)] = false := by decide +kernel

/-- **The init code deploys the published runtime bytes for every argument word.** -/
theorem published_deploys_all {n : Nat} (hn : n < 2 ^ 256) :
    Deploys (Verify.Lifecycle.initArgs publishedInit [n]) Certified.verify_counter.Final.code
      [(1, n)] := by
  have h := deploys_all published_symCheck [BitVec.ofNat 256 n] rfl (by simp)
  have e1 : [BitVec.ofNat 256 n].map BitVec.toNat = [n] := by
    simp only [List.map_cons, List.map_nil, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have e2 : storeOf [BitVec.ofNat 256 n] [(1, .arg 0)] = [(1, n)] := by
    simp only [storeOf, E.eval, List.map_cons, List.map_nil, List.getD_cons_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn]
  rw [e1, e2, codeOf_patched, List.foldl_nil] at h
  exact h

end Bytecode

/-- Typed admission of `[n]` for the creation bytes of `publishedInit`, for every word. -/
theorem published_admits_all {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256) :
    CtorAdmits c publishedInit (Verify.Lifecycle.initArgs publishedInit [n]) [n] :=
  CtorAdmits.of_fn (Verify.LoopSource.Equiv.CounterLoad.ctor_of hc) rfl rfl
    (by simp [Verify.LoopSource.Equiv.CounterLoad.ctorFn]) (Or.inr rfl) (by simpa using hn)

/-! ## The published statement, created and deployed -/

/-- **The published verify_counter statement, created and deployed, for every constructor word.**
For the checked contract `c` and every `n < 2 ^ 256`: the creation bytes `initArgs publishedInit [n]`
are typed-admitted for `c` with exactly `[n]`; EthLib runs them to success, returning the published
runtime bytes with storage `[(1, n)]`; SolidCore's constructor on `[n]` returns a state with no
logs that loads `n` at slot 1 and 0 elsewhere; and `Shapes.Certified` holds for Counter deployed
with `[n]` (fixed caller `callerAddress`), the published bytes, allowed statuses, specification and
gas bound, on every `ValidS` call (`bump(a)`, `a < 2 ^ 32`, value 0) whose storage writes slot 1
when `n ≠ 0`. -/
theorem verify_counter_deployed :
    ∃ c, contract? = .ok c ∧ ∀ n : Nat, n < 2 ^ 256 →
      CtorAdmits c publishedInit (Verify.Lifecycle.initArgs publishedInit [n]) [n] ∧
      Deploys (Verify.Lifecycle.initArgs publishedInit [n]) Certified.verify_counter.Final.code
        [(1, n)] ∧
      (∃ d, LoadDeployed fuel c [n] d ∧ ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0) ∧
      Shapes.Certified (solidCoreFromArgs callerAddress fuel [n]) c
        Certified.verify_counter.Final.code
        (fun call => Contracts.VerifyCounter.ShapeSource.ValidS call ∧ CoverN n call.storage)
        Contracts.VerifyCounter.ShapeSource.Allowed
        (Shapes.bundlePost Certified.verify_counter.gen.Counter.Spec.Counter Shapes.ctxOfCall
          Shapes.idStep)
        SolarTV.Milestone.VerifyCounter.Bump.gasBound := by
  obtain ⟨-, -, c, hc, hcert⟩ := Certified.verify_counter.Final.final
  refine ⟨c, hc, fun n hn => ⟨published_admits_all hc hn, published_deploys_all hn,
    Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed hc hn,
    certified_transfer hcert ?_ (fun _ h => h.1) (fun _ h => deployed_eq_runtime_fixed hc hn h.1 h.2)⟩⟩
  exact ⟨{ calldata := Abi.calldata bumpSel [0], callvalue := 0, storage := [(1, n)] },
    ⟨[(1, n)], 0, by decide, rfl⟩, fun _ => ⟨(1, n), List.mem_singleton_self _, rfl⟩⟩

end Verify.AllValue.CounterPublishedDeployed

/-- info: 'Verify.AllValue.CounterPublishedDeployed.certified_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterPublishedDeployed.certified_transfer

/-- info: 'Verify.AllValue.CounterPublishedDeployed.published_deploys_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterPublishedDeployed.published_deploys_all

/-- info: 'Verify.AllValue.CounterPublishedDeployed.verify_counter_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.AllValue.CounterPublishedDeployed.verify_counter_deployed
