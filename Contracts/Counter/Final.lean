import Verify.Final
import SolidCore.Refinement.Solar.Counter.Every

/-!
# The counter milestone's certificate

The first instance of `Final.Certificate`: solar's runtime bytecode for

    contract Counter { uint256 x; function inc(uint256 d) external { x += d; }
      function get() external view returns (uint256) { return x; } }

(solar-tv/milestone/counter, `-Ogas --evm-version osaka`), bound to the manifest the exporter
wrote with its stages (`manifest`, `bound`: the hex and the SHA-256 of the bytecode, checked by
the kernel), meets its specification (`spec`: `inc(d)` ensures `x == old(x) + d` and returns
nothing, `get()` ensures `x == old(x)` and returns `x`; neither is payable) and agrees with
SolidCore's checked contract on every call of the specification, with any value and from any
storage (`certificate`). Every stage is a theorem: the source stage and the assembly stage of
`Every.lean` and solar-tv's backend stages, composed by `certifiedEvery`.

The non-vacuity lemmas show the specification is not met trivially: the bytecode succeeds on
`inc(1)` from the empty storage and stores 1 (`inc_succeeds`), reverts on the overflow
(`inc_overflow_fails`), and the postcondition rejects a state that did not change
(`ensures_rejects`).
-/

namespace SolidCore.Refinement.Solar.Counter.Final

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide SolidCore.Refinement.Evm
open EthLib.Base

/-! ## The specification -/

/-- `inc(uint256 d)`: `x == old(x) + d`, no return data. -/
def incSpec : FnSpec Nat where
  name := "inc"
  sel := incSelector
  params := [.uint 256]
  requires _ _ := True
  ensures args x x' out := x' = x + args.headD 0 ∧ out = []
  payable := false

/-- `get()`: `x == old(x)`, returns `x`. -/
def getSpec : FnSpec Nat where
  name := "get"
  sel := getSelector
  params := []
  requires _ _ := True
  ensures _ x x' out := x' = x ∧ out = Verify.word x
  payable := false

/-- Counter's specification: the abstract state is `x`, slot 0. -/
def spec : ContractSpec Nat where
  abs s := s 0
  invariant _ := True
  fns := [incSpec, getSpec]

/-! ## From the observable on every call -/

theorem inc_call (a v : Nat) (ha : a < 2 ^ 256) (σ : List (Nat × Nat)) :
    incSpec.call [a] v σ =
      { callOf incSelector [BitVec.ofNat 256 a] with callvalue := v, storage := σ } := by
  simp only [FnSpec.call, incSpec, callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha]

theorem get_call (v : Nat) (σ : List (Nat × Nat)) :
    getSpec.call [] v σ = { callAt getSelector [] σ with callvalue := v } := rfl

theorem scope_inc (a v : Nat) (ha : a < 2 ^ 256) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    scopeEvery (incSpec.call [a] v σ) := by
  rw [inc_call a v ha]
  exact ⟨hv, Or.inl ⟨_, rfl⟩⟩

theorem scope_get (v : Nat) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    scopeEvery (getSpec.call [] v σ) :=
  ⟨hv, Or.inr (Or.inl rfl)⟩

theorem rejected_outcome {f : FnSpec Nat} {args : List Nat} {call : Call} :
    spec.Outcome f args call (Abi.rejected call.storage) :=
  ⟨fun h => absurd h (by simp [Abi.rejected]), fun _ => ⟨rfl, rfl⟩⟩

theorem typed_inc {args : List Nat} (h : incSpec.Typed args) : ∃ a, a < 2 ^ 256 ∧ args = [a] := by
  unfold FnSpec.Typed incSpec at h
  cases h with
  | cons ha hrest =>
    cases hrest
    exact ⟨_, by simpa [Param.clean] using ha, rfl⟩

theorem typed_get {args : List Nat} (h : getSpec.Typed args) : args = [] := by
  unfold FnSpec.Typed getSpec at h
  cases h
  rfl

/-- The specification holds of every program that shows `expectedEvery` on every call of
`scopeEvery`. -/
theorem holds_of_every {S : Sem} {p : S.Prog}
    (h : ∀ call, scopeEvery call → S.run p call = some (expectedEvery call)) :
    Holds S p spec := by
  intro f hf args ht v hv σ _ _ obs hrun
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · obtain ⟨a, ha, rfl⟩ := typed_inc ht
    rw [h _ (scope_inc a v ha hv σ)] at hrun
    cases hrun
    by_cases h0 : v = 0
    · subst h0
      rw [inc_call a 0 ha]
      have hcall : { callOf incSelector [BitVec.ofNat 256 a] with callvalue := 0, storage := σ } =
          { callOf incSelector [BitVec.ofNat 256 a] with storage := σ } := rfl
      rw [hcall, expectedEvery_inc]
      unfold expectedAt
      have hd : (BitVec.ofNat 256 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
      split_ifs with hof
      · refine ⟨fun _ => ⟨?_, trivial, fun _ => rfl⟩, fun h => absurd h (by simp)⟩
        simp [spec, incSpec, ContractSpec.pre, hd, callOf]
      · exact ⟨fun h => absurd h (by simp), fun _ => ⟨rfl, rfl⟩⟩
    · rw [expectedEvery_value _ h0]
      exact rejected_outcome
  · obtain rfl := typed_get ht
    rw [h _ (scope_get v hv σ)] at hrun
    cases hrun
    by_cases h0 : v = 0
    · subst h0
      rw [get_call, show ({ callAt getSelector [] σ with callvalue := 0 } : Call) =
        callAt getSelector [] σ from rfl, expectedEvery_get]
      exact ⟨fun _ => ⟨⟨rfl, rfl⟩, trivial, fun _ => rfl⟩, fun h => absurd h (by simp [getAt])⟩
    · rw [expectedEvery_value _ h0]
      exact rejected_outcome

theorem calls_every {call : Call} (h : spec.Calls call) : scopeEvery call := by
  obtain ⟨f, hf, args, ht, v, hv, σ, rfl⟩ := h
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · obtain ⟨a, ha, rfl⟩ := typed_inc ht
    exact scope_inc a v ha hv σ
  · obtain rfl := typed_get ht
    exact scope_get v hv σ

/-- EthLib runs solar's bytecode to `expectedEvery` on every call of `scopeEvery`. -/
theorem target_every (call : Call) (h : scopeEvery call) :
    Target.run code call = some (expectedEvery call) := by
  obtain ⟨-, -, -, hsat⟩ := certifiedEvery
  obtain ⟨obs, hrun, hpost⟩ := hsat call h trivial
  change Target.run code call = some obs at hrun
  rw [hrun, show obs = expectedEvery call from hpost]

/-! ## The manifest -/

/-- The manifest the exporter wrote with Counter's stages. -/
def manifest : Manifest where
  contract := "Counter"
  sourceSha256 := (SolarTV.Export.Counter.Manifest.sources.headD ("", "")).2
  compilerCommit := SolarTV.Export.Counter.Manifest.compiler
  options := SolarTV.Export.Counter.Manifest.arguments
  runtimeHex := SolarTV.Export.Counter.Manifest.bytecodeHex
  runtimeSha256 := SolarTV.Export.Counter.Manifest.bytecodeSha256

theorem hex_bound : hexOf (code.data.toList.map (·.toNat)) = manifest.runtimeHex := by
  decide +kernel

theorem sha_bound :
    hexOf ((EthLib.Cryptography.Hash.Sha256.hash code).data.toList.map (·.toNat)) =
      manifest.runtimeSha256 := by
  decide +kernel

theorem bound : Bound manifest code := ⟨hex_bound, sha_bound⟩

theorem frameLocal : FrameLocal code = true := by decide +kernel

/-! ## The certificate -/

/-- **Counter's certificate.** solar's bytecode, bound to its manifest and running in one frame,
agrees with SolidCore's checked Counter on every call of `inc` and `get`, with any value and
from any storage, and meets Counter's specification, which SolidCore's Counter meets too. -/
noncomputable def certificate : Certificate spec manifest :=
  let c := Classical.choose contract_ok
  have hc : contract? = .ok c := Classical.choose_spec contract_ok
  { code
    fuel
    source := c
    bound
    frameLocal
    sourceHolds := holds_of_every fun call h => source_run_every hc call h
    refines := fun call h =>
      ⟨_, source_run_every hc call (calls_every h), target_every call (calls_every h)⟩
    holds := holds_of_every target_every }

/-- The certificate's two theorems, as one statement. -/
theorem certified :
    Bound manifest code ∧ FrameLocal code = true ∧
      ∃ c, contract? = .ok c ∧ Agree (solidCore fuel) ethLib c code spec.Calls ∧
        Holds (solidCore fuel) c spec ∧ Holds ethLib code spec := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨bound, frameLocal, c, hc,
    fun call h => ⟨_, source_run_every hc call (calls_every h), target_every call (calls_every h)⟩,
    holds_of_every fun call h => source_run_every hc call h, holds_of_every target_every⟩

/-- The invariants and the specification across every sequence of calls, each from the storage
the one before left. -/
theorem certified_trace {carry : Carry}
    (exact : ∀ call obs, Target.run code call = some obs → Carries carry call obs)
    (σ : List (Nat × Nat)) (steps : List (Step Nat))
    (hsteps : ∀ s ∈ steps, s.f ∈ spec.fns ∧ s.f.Typed s.args ∧ s.value < 2 ^ 256) :
    Trace spec (Target.run code) carry σ steps :=
  (holds_of_every target_every).trace (S := ethLib) exact σ steps trivial hsteps

/-! ## Non-vacuity -/

/-- The bytecode succeeds on `inc(1)` with no value from the empty storage and stores 1. -/
theorem inc_succeeds : ∃ obs, Target.run code (incSpec.call [1] 0 []) = some obs ∧
    obs.success = true ∧ obs.storage 0 = 1 := by
  refine ⟨_, target_every _ (scope_inc 1 0 (by decide) (by decide) []), ?_⟩
  rw [inc_call 1 0 (by decide)]
  rw [show ({ callOf incSelector [BitVec.ofNat 256 1] with callvalue := 0, storage := [] } : Call) =
    { callOf incSelector [BitVec.ofNat 256 1] with storage := [] } from rfl, expectedEvery_inc]
  simp [expectedAt, slotValue]

/-- The bytecode fails on `inc(1)` from a storage whose `x` is `2 ^ 256 - 1`. -/
theorem inc_overflow_fails : ∃ obs, Target.run code (incSpec.call [1] 0 [(0, 2 ^ 256 - 1)]) = some obs ∧
    obs.success = false := by
  refine ⟨_, target_every _ (scope_inc 1 0 (by decide) (by decide) _), ?_⟩
  rw [inc_call 1 0 (by decide)]
  have hcall : ({ callOf incSelector [BitVec.ofNat 256 1] with callvalue := 0, storage := [(0, 2 ^ 256 - 1)] } : Call) =
      { callOf incSelector [BitVec.ofNat 256 1] with storage := [(0, 2 ^ 256 - 1)] } := rfl
  rw [hcall, expectedEvery_inc]
  simp [expectedAt, slotValue]

/-- The postcondition of `inc(1)` rejects a state that did not change. -/
theorem ensures_rejects : ¬ incSpec.ensures [1] 0 0 [] := by
  simp [incSpec]

/-- info: 'SolidCore.Refinement.Solar.Counter.Final.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.Counter.Final.certified_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_trace

/-- info: 'SolidCore.Refinement.Solar.Counter.Final.inc_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_succeeds

/-- info: 'SolidCore.Refinement.Solar.Counter.Final.inc_overflow_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_overflow_fails

end SolidCore.Refinement.Solar.Counter.Final
