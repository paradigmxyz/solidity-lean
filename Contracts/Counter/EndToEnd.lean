import Contracts.Counter.Verdict
import Contracts.Counter.VC.Inc
import Contracts.Counter.VC.Get
import Contracts.Counter.VC.Mutants

/-!
# The counter milestone: solar-verify's spec of `inc` holds of the deployed bytecode

One theorem from solar-verify's checked obligation to solar's runtime bytecode, for
`inc(uint256 d)` of the counter milestone (`scripts/refinement/counter/counter.sol`; its annotated
copy `scripts/verify/CounterMilestone.sol` adds `@custom:ensures x == old(x) + d`):

* `SolidCore.Verify.VC.Counter.inc_triple`: SolidCore's checked counter meets `incPost` on every
  call of `inc` (any argument word, no value, any storage). It is read off solar-verify's
  exported obligation, which `checkScript` accepts by the kernel (`inc_check`), and bound to
  SolidCore's run of `inc` (`inc_binding`).
* `Counter.Verdict.bytecode_of_triple`: the stage from SolidCore's checked counter to solar's
  bytecode (`Counter.Verdict.agree`, through solar-tv's backend stages and the assembly stage)
  carries it to the bytecode under EthLib.
* `Counter.Final.bound`, `Counter.Final.frameLocal`: the bytecode is the exporter's (its hex and
  SHA-256, checked by the kernel), and it runs in one frame: no instruction calls out, creates or
  reads outside its frame.

`incPost` says the call succeeds exactly when `x + d` does not overflow, and then sets slot 0 to
`x + d` and leaves every other slot as it was. It is not met trivially: `Counter.Final.inc_succeeds`
and `inc_overflow_fails` run the bytecode both ways, and solar-verify's checked script rejects
a source mutant and a spec mutant (`CounterMutants.lean`).

The trusted base is empty here: the counter hashes nothing and calls nothing, and the theorem
takes no hypothesis. `get_spec_bytecode` does the same for `get`, from a direct proof (no NatSpec, no VC). What they do not cover: deployment (the constructor),
gas limits other than EthLib's default (`Target.run`), and calls with value (not in
`stageScope`; the bytecode rejects them, as `Counter.Final`'s `scopeEvery` shows).
-/

namespace SolidCore.Refinement.Solar.Counter.EndToEnd

open SolidCore.Refinement SolidCore.Refinement.Final

/-- Every call of `inc` in solar-verify's binding scope is in the stage's scope. -/
theorem inc_in_scope {call : Call}
    (h : SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnInc [] call) :
    scopeEvery call := by
  obtain ⟨σ, -, fn, hfn, args, hl, hargs, rfl⟩ := h
  simp only [List.mem_singleton] at hfn
  subst hfn
  match args, hl with
  | [a], _ =>
    have ha : a < 2 ^ 256 := hargs a (List.mem_singleton_self a)
    refine ⟨Nat.two_pow_pos 256, Or.inl ⟨BitVec.ofNat 256 a, ?_⟩⟩
    simp only [Evm.Wide.callOf, List.map, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    rfl

/-- **The counter's `inc`: solar-verify's spec holds of the deployed bytecode.** The bytecode is
the exporter's and runs in one frame, and on every call of `inc(uint256)` with any argument
word, no value and any storage, EthLib runs it to an observable meeting `incPost`. -/
theorem inc_spec_bytecode :
    Bound Final.manifest code ∧ FrameLocal code = true ∧
      ∀ call, SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnInc [] call →
        ∃ obs, Target.run code call = some obs ∧ SolidCore.Verify.VC.Counter.incPost call obs := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨Final.bound, Final.frameLocal, fun call h =>
    Verdict.bytecode_of_triple hc (fun _ h => inc_in_scope h)
      (SolidCore.Verify.VC.Counter.inc_triple (by exact hc)) call h trivial⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.EndToEnd.inc_spec_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inc_spec_bytecode

/-- Every call of §get§ in the binding scope is in the stage's scope. -/
theorem get_in_scope {call : Call}
    (h : SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnGet [] call) :
    scopeEvery call := by
  obtain ⟨σ, -, fn, hfn, args, hl, -, rfl⟩ := h
  simp only [List.mem_singleton] at hfn
  subst hfn
  match args, hl with
  | [], _ =>
    refine ⟨Nat.two_pow_pos 256, Or.inr (Or.inl ?_)⟩
    simp only [Evm.Wide.callOf, List.map]
    rfl

/-- **The counter's §get§ on the deployed bytecode.** On every call of §get()§ with no value and
any storage, EthLib runs the bytecode to a success that returns slot 0 as a word and changes no
slot. §get§ has no NatSpec clause, so solar-verify emits no obligation for it: §get_triple§ is
proved directly of SolidCore's run, with no VC behind it. -/
theorem get_spec_bytecode :
    Bound Final.manifest code ∧ FrameLocal code = true ∧
      ∀ call, SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnGet [] call →
        ∃ obs, Target.run code call = some obs ∧ SolidCore.Verify.VC.Counter.getPost call obs := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨Final.bound, Final.frameLocal, fun call h =>
    Verdict.bytecode_of_triple hc (fun _ h => get_in_scope h)
      (SolidCore.Verify.VC.Counter.get_triple (by exact hc)) call h trivial⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.EndToEnd.get_spec_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms get_spec_bytecode

end SolidCore.Refinement.Solar.Counter.EndToEnd
