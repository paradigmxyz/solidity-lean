import Examples.Counter.Verdict
import Examples.Counter.Spec.Export
import Examples.Counter.Spec.ExportWrong
import Examples.Counter.EndToEnd

/-!
# Counter: solar-verify's spec holds of solar's deployed bytecode

The counter milestone (`scripts/refinement/counter/counter.sol`, solar-tv/milestone/counter,
`-Ogas --evm-version osaka`) annotated for solar-verify in `scripts/verify/CounterMilestone.sol`
(the same text plus one NatSpec line, which `scripts/verify/check.sh` checks):

    contract Counter {
        uint256 x;
        /// @custom:ensures x == old(x) + d
        function inc(uint256 d) external { x += d; }
        function get() external view returns (uint256) { return x; } }

`solar-verify --emit-lean-spec` writes that spec as `Export.Counter.Counter` (a
`SolidCore.Spec.Bundle`; `get` has no spec, so the exporter leaves it out). Its meaning is
`SolidCore.Spec.Holds`: every call of `inc` with a clean word argument finishes, and when it
succeeds slot 0 holds the old slot 0 plus the argument. There is no succeeds-if, so no claim
that it succeeds.

* `holds_source`: the spec of SolidCore's checked `Counter` on every call of `scopeEvery` (any
  value, any storage; inc's and get's ABI encodings, short call data, unknown selectors, short
  arguments), from SolidCore's run of each (`source_run_every`).
* `verdict`: solar-verify's verdict (`SolidCore.Spec.Verdict`, the one trusted item of
  `spec_of_verdict`) under Counter's trusted base `Verdict.hyps` (`Hyps.plain`: no hashing, no
  external call, no assembly, no assume, no trusted function), proved in Lean rather than
  trusted.
* `EndToEnd.inc_spec_bytecode`, `EndToEnd.get_spec_bytecode`: `inc`'s clause read off
  solar-verify's own checked obligation through the source bridge
  (`SolidCore.Verify.VC.Counter.inc_triple`, whose binding ties solar-verify's encoding of the new
  `x` and of the success guard to SolidCore's run), and `get`'s triple, each carried to the
  bytecode by the certified stage; the headline includes both.
* **`spec_holds_of_bytecode`**: the headline. solar's runtime bytecode, bound to the exporter's
  manifest by its hex and SHA-256 and to the spec export by the same SHA-256, runs in one frame,
  agrees with SolidCore's checked `Counter` on every call of the scope, and meets solar-verify's
  spec under EthLib, through the composition `Verdict.bytecode_spec_of_verdict` of the certified
  stages (source, backend, assembly) with the verdict.
* `wrong_fails`: the negative. The spec mutant `x == old(x) + d + 1`
  (`scripts/verify/mutant/CounterSpecMut.sol`, which solar-verify also rejects) does not hold of
  the bytecode, by a mismatch: `inc(1)` from the empty storage stores 1.

Trusted base left: Lean's kernel; EthLib's EVM (`Target.run`, at its default gas limit, one
frame) as the meaning of the bytecode; that `Export.Counter` is what solar-verify exports for the
annotated source (checked by `scripts/verify/check.sh` outside the kernel). Not covered:
deployment, other gas limits, and call data with bytes past the ABI encoding.
-/

namespace SolidCore.Refinement.Solar.Counter.Headline

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Final

/-- The exported spec. -/
abbrev spec : SolidCore.Spec.Bundle := SolidCore.Spec.Export.Counter.Counter

/-- The call context of SolidCore's and EthLib's interface (`Refinement.Statement`): sender
`0x2000`, the contract at `0x1000`, block timestamp 1. -/
def ctxOf (call : Call) : SolidCore.Spec.Ctx :=
  { sender := 0x2000, value := call.callvalue, timestamp := 1, self := 0x1000 }

/-- Counter has no ghost state. -/
def step : SolidCore.Spec.GhostStep := fun _ g => g

/-! ## Reading call data the way the spec does -/

theorem bytesWord_map (l : List UInt8) :
    SolidCore.Spec.bytesWord (l.map (·.toNat)) = EthLib.Base.bytesToNat l := by
  simp [SolidCore.Spec.bytesWord, EthLib.Base.bytesToNat, List.foldl_map]

theorem spec_selectorOf_append (s : Nat) (hs : s < 2 ^ 32) (data : ByteArray) (v : Nat)
    (σ : List (Nat × Nat)) :
    SolidCore.Spec.selectorOf { calldata := selectorOf s ++ data, callvalue := v, storage := σ } = s := by
  simp only [SolidCore.Spec.selectorOf, selectorOf, ByteArray.data_append, Array.toList_append,
    List.map_append, List.toList_toArray]
  rw [List.take_append_of_le_length (by simp [EthLib.Base.natToBytes_length]),
    List.take_of_length_le (by simp [EthLib.Base.natToBytes_length]), bytesWord_map,
    EthLib.Base.bytesToNat_natToBytes_of_lt (by simpa using hs)]

theorem bytesWord_word {v : Nat} (h : v < 2 ^ 256) : SolidCore.Spec.bytesWord (Verify.word v) = v := by
  rw [Verify.word, bytesWord_map, EthLib.Base.bytesToNat_natToBytes_of_lt]
  simpa using h

theorem length_word (v : Nat) : (Verify.word v).length = 32 := by
  simp [Verify.word, EthLib.Base.natToBytes_length]

theorem words_word {v : Nat} (h : v < 2 ^ 256) : SolidCore.Spec.words (Verify.word v) = [v] := by
  simp only [SolidCore.Spec.words, length_word, Nat.reduceDiv, List.range_one, List.map_cons,
    List.map_nil, Nat.mul_zero, List.drop_zero]
  rw [List.take_of_length_le (by rw [length_word]), bytesWord_word h]

theorem argBytes_one (a : Nat) : Dirty.argBytes [a] = Verify.word a := by
  simp [Dirty.argBytes, Verify.word]

/-- The argument words after the selector of inc's ABI call data. -/
theorem words_inc (d : U256) :
    SolidCore.Spec.words
        ((((callOf incSelector [d]).calldata).data.toList.map (·.toNat)).drop 4) = [d.toNat] := by
  simp only [callOf, List.map_cons, List.map_nil]
  rw [Dirty.bytes_calldata, Wide.drop_selector, argBytes_one, words_word d.isLt]

/-- Fewer than 32 bytes after the selector: no argument word. -/
theorem words_short (s : Nat) (data : ByteArray) (h : data.size < 32) :
    SolidCore.Spec.words (((selectorOf s ++ data).data.toList.map (·.toNat)).drop 4) = [] := by
  simp only [SolidCore.Spec.words, selectorOf, ByteArray.data_append, Array.toList_append,
    List.map_append, List.toList_toArray]
  rw [List.drop_append_of_le_length (by simp [EthLib.Base.natToBytes_length])]
  simp [EthLib.Base.natToBytes_length, ByteArray.size] at h ⊢
  omega

theorem rejected_success (σ : List (Nat × Nat)) : (Abi.rejected σ).success = false := rfl

/-! ## The spec of SolidCore's checked counter -/

/-- The one function the spec has: `inc`. -/
theorem mem_specs {fs : SolidCore.Spec.FnSpec} (h : fs ∈ spec.spec.specs) :
    fs = spec.spec.specs.head (by simp [spec, SolidCore.Spec.Export.Counter.Counter]) := by
  simpa [spec, SolidCore.Spec.Export.Counter.Counter] using h

/-- **What Counter does, read through the spec.** On every call of the scope, the observable
`expectedEvery` meets `inc`'s postcondition from any pre-state meeting its precondition. -/
theorem post_every {call : Call} (hs : scopeEvery call) {fs : SolidCore.Spec.FnSpec}
    (hfs : fs ∈ spec.spec.specs) {args : List Int} {pre : SolidCore.Spec.State}
    (hpre : SolidCore.Spec.Pre spec fs (ctxOf call) pre call args) :
    SolidCore.Spec.Post spec fs (ctxOf call) pre (step call pre.ghost) (expectedEvery call) args := by
  rw [mem_specs hfs] at hpre ⊢
  refine ⟨fun hsucc => ?_, fun hne => absurd rfl hne⟩
  obtain ⟨⟨h4, hsel, hdec⟩, hst, -, -, -⟩ := hpre
  rcases call with ⟨cd, v, σ⟩
  obtain ⟨hv, hcl⟩ := hs
  dsimp only at hv hcl hsucc hsel hdec h4 hst ⊢
  by_cases h0 : v = 0
  swap
  · rw [expectedEvery_value _ h0] at hsucc
    exact absurd hsucc (by simp [rejected_success])
  subst h0
  rcases hcl with ⟨d, rfl⟩ | rfl | hshort | ⟨s, data, hs, rfl, hsel'⟩
  · -- inc's ABI call data: the run adds the argument to slot 0.
    have hcall : ({ calldata := (callOf incSelector [d]).calldata, callvalue := 0, storage := σ } : Call) =
        { callOf incSelector [d] with storage := σ } := rfl
    rw [hcall, expectedEvery_inc] at hsucc ⊢
    rw [words_inc] at hdec
    simp only [SolidCore.Spec.Export.Counter.Counter, List.head, SolidCore.Spec.decodeWords,
      SolidCore.Spec.Ty.ofWord, d.isLt, ite_true, bind, pure, Option.bind, Option.some.injEq] at hdec
    subst hdec
    unfold expectedAt at hsucc ⊢
    split_ifs at hsucc ⊢ with hof
    · refine ⟨[], by simp [SolidCore.Spec.Export.Counter.Counter, SolidCore.Spec.decodeWords], ?_, ?_⟩
      · have hpre0 : pre.storage 0 = slotValue σ 0 := by rw [hst]
        have hlt : slotValue σ 0 < 2 ^ 256 := SolidCore.Refinement.Evm.Wide.slotValue_lt σ 0
        simp [SolidCore.Spec.Bundle.satAll, SolidCore.Spec.Bundle.sat, SolidCore.Spec.eval,
          SolidCore.Spec.slotOf, SolidCore.Spec.mkEnv, SolidCore.Spec.Env.cur,
          SolidCore.Spec.BinOp.apply, SolidCore.Spec.Ty.ofBits, SolidCore.Spec.toWord,
          SolidCore.Spec.Export.Counter.Counter, hpre0]
        omega
      · simp [SolidCore.Spec.Bundle.satAll, SolidCore.Spec.Export.Counter.Counter]
    · simp at hsucc
  · -- get's call data: not inc's selector.
    have : SolidCore.Spec.selectorOf
        ({ calldata := (callOf getSelector []).calldata, callvalue := 0, storage := σ } : Call) =
        getSelector := by
      rw [calldata_get]
      exact spec_selectorOf_append _ (by decide) _ _ _
    rw [this] at hsel
    simp [SolidCore.Spec.Export.Counter.Counter, getSelector] at hsel
  · exact absurd h4 (by omega)
  · rw [spec_selectorOf_append s hs data 0 σ] at hsel
    simp only [SolidCore.Spec.Export.Counter.Counter, List.head] at hsel
    rcases hsel' with ⟨hne, -⟩ | ⟨-, hshort⟩
    · exact absurd hsel (by simpa [incSelector] using hne)
    · rw [words_short s data hshort] at hdec
      simp [SolidCore.Spec.Export.Counter.Counter, SolidCore.Spec.decodeWords] at hdec

/-- **solar-verify's spec, of SolidCore's checked `Counter`**, on every call of the scope. -/
theorem holds_source {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    SolidCore.Spec.Holds (solidCore fuel) c scopeEvery spec ctxOf step :=
  fun _ hfs call hs _ _ hpre => ⟨_, source_run_every hc call hs, post_every hs hfs hpre⟩

/-- **solar-verify's verdict on Counter, proved.** The one trusted item of
`SolidCore.Spec.spec_of_verdict`, under Counter's trusted base, is a theorem here. -/
theorem verdict {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (deployed : Nat → Nat) :
    SolidCore.Spec.Verdict (solidCore fuel) c scopeEvery spec ctxOf step
      ((Verdict.hyps c deployed).toAssumptions scopeEvery spec ctxOf step) :=
  fun fs hfs => (holds_source hc fs hfs).mono fun _ h => h.1

/-! ## The headline -/

/-- The spec export names the bytecode the certificate binds. -/
theorem export_bound :
    SolidCore.Spec.Export.Counter.manifest.bytecodeSha256 = Final.manifest.runtimeSha256 := by
  decide +kernel

/-- **solar-verify's spec of `Counter` holds of solar's deployed bytecode.** solar's runtime
bytecode for the counter milestone is bound to the exporter's manifest (hex and SHA-256, by the
kernel) and to the spec export (the same SHA-256), runs in one frame, agrees with SolidCore's
checked `Counter` on every call of `scopeEvery`, and meets solar-verify's exported spec under
EthLib on every call of `scopeEvery`: any value, any storage, inc's and get's ABI encodings,
short call data, unknown selectors and short arguments. The spec's well-formedness is checked
by the kernel; the verdict and the trusted base are discharged (`verdict`,
`Instances.counter_on`). With it, the source bridge's two end-to-end theorems
(`EndToEnd.inc_spec_bytecode`: solar-verify's checked obligation for `inc`, bound to SolidCore's
run by `inc_triple`; `EndToEnd.get_spec_bytecode`: `get` returns slot 0 and writes nothing), on
the ABI calls of each with no value and any storage. -/
theorem spec_holds_of_bytecode :
    SolidCore.Spec.Export.Counter.manifest.bytecodeSha256 = Final.manifest.runtimeSha256 ∧
      Bound Final.manifest code ∧ FrameLocal code = true ∧
      ∃ c, contract? = .ok c ∧ Agree (solidCore fuel) ethLib c code scopeEvery ∧
        SolidCore.Spec.Holds ethLib code scopeEvery spec ctxOf step ∧
      (∀ call, SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnInc [] call →
        ∃ obs, Target.run code call = some obs ∧ SolidCore.Verify.VC.Counter.incPost call obs) ∧
      (∀ call, SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnGet [] call →
        ∃ obs, Target.run code call = some obs ∧ SolidCore.Verify.VC.Counter.getPost call obs) := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hb, hf, ha, hh⟩ := Verdict.bytecode_spec_of_verdict hc (b := spec) (ctxOf := ctxOf)
    (step := step) (fun _ => 0) SolidCore.Spec.Export.Counter.Counter_wf
    (SolidCore.Spec.opaqueInRange_of_none (by decide)) (verdict hc fun _ => 0)
  exact ⟨export_bound, hb, hf, c, hc, ha, hh, EndToEnd.inc_spec_bytecode.2.2,
    EndToEnd.get_spec_bytecode.2.2⟩

/-! ## The negative -/

/-- **The spec mutant fails, by a mismatch.** `x == old(x) + d + 1` does not hold of the
bytecode: `inc(1)` from the empty storage succeeds and stores 1, and the mutant asks for 2. -/
theorem wrong_fails :
    ¬ SolidCore.Spec.Holds ethLib code scopeEvery SolidCore.Spec.Export.CounterSpecMut.Counter
      ctxOf step := by
  intro h
  let call : Call := { callOf incSelector [1#256] with storage := [] }
  have hs : scopeEvery call := ⟨by decide, Or.inl ⟨1#256, rfl⟩⟩
  let pre : SolidCore.Spec.State := ⟨slotValue [], SolidCore.Spec.Ghost.zero, 0⟩
  have hne : SolidCore.Spec.Export.CounterSpecMut.Counter.spec.specs ≠ [] := by
    simp [SolidCore.Spec.Export.CounterSpecMut.Counter]
  have hfs := List.head_mem hne
  have hpre : SolidCore.Spec.Pre SolidCore.Spec.Export.CounterSpecMut.Counter
      (SolidCore.Spec.Export.CounterSpecMut.Counter.spec.specs.head hne) (ctxOf call) pre call [1] := by
    refine ⟨⟨?_, ?_, ?_⟩, rfl, by simp [pre, ctxOf], ?_, ?_⟩
    · have := size_callOf 1#256
      simp only [call] at this ⊢
      omega
    · show SolidCore.Spec.selectorOf call = _
      have := spec_selectorOf_append incSelector (by decide) (wordsBytes [1#256]) 0 []
      rw [← calldata_inc] at this
      simpa [SolidCore.Spec.Export.CounterSpecMut.Counter, incSelector] using this
    · show SolidCore.Spec.decodeWords _ (SolidCore.Spec.words
        (((callOf incSelector [1#256]).calldata.data.toList.map (·.toNat)).drop 4)) = _
      rw [words_inc]
      simp [SolidCore.Spec.Export.CounterSpecMut.Counter, SolidCore.Spec.decodeWords,
        SolidCore.Spec.Ty.ofWord, bind, pure]
    · simp [SolidCore.Spec.Bundle.satAll, SolidCore.Spec.Export.CounterSpecMut.Counter]
    · simp [SolidCore.Spec.Bundle.satAll, SolidCore.Spec.Export.CounterSpecMut.Counter]
  obtain ⟨obs, hrun, hpost⟩ := h _ hfs call hs [1] pre hpre
  rw [Final.target_every call hs] at hrun
  cases hrun
  have hcall : call = { callOf incSelector [1#256] with storage := [] } := rfl
  rw [hcall, expectedEvery_inc] at hpost
  have hok : (expectedAt [] 1#256).success = true := by simp [expectedAt, slotValue]
  obtain ⟨rets, -, hens, -⟩ := hpost.1 hok
  have := hens _ (List.mem_singleton_self _)
  simp [SolidCore.Spec.Bundle.sat, SolidCore.Spec.Export.CounterSpecMut.Counter,
    SolidCore.Spec.eval, SolidCore.Spec.slotOf, SolidCore.Spec.mkEnv, SolidCore.Spec.Env.cur,
    SolidCore.Spec.BinOp.apply, SolidCore.Spec.Ty.ofBits, SolidCore.Spec.toWord, pre,
    expectedAt, slotValue] at this

/-- info: 'SolidCore.Refinement.Solar.Counter.Headline.spec_holds_of_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_holds_of_bytecode

/-- info: 'SolidCore.Refinement.Solar.Counter.Headline.wrong_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_fails

end SolidCore.Refinement.Solar.Counter.Headline
