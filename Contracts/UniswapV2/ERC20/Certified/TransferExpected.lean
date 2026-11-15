import Verify.Generic.Instances.Transfer
import Contracts.UniswapV2.ERC20.Certified.TransferFrom

-- Untrusted proof script: the kernel checks it.

/-!
# UniswapV2ERC20.transfer from every caller as instances of the generic expected theorem

`Verify.Generic.Instances.Transfer` covers the default context (caller 0x2000) only. This module
restates `CertifiedFrom.certified_from` as `Generic.Expected src spec bytes` over every context,
with the same `src` (solc's AST of the pinned port, the contract `UniswapV2ERC20`, the slice's
fuel) and the same `bytes` (the exported code), in two forms:

* `specScoped` / `expected_scoped`: `certified_from` as stated. The valid calls of a context
  are `ValidInAt caller` (each carries the scoped hash premise
  `ScopedSep (transferFootprint 1 caller dst)`) and the postcondition is `TargetPostAt caller`.
  The coverage is every real caller whose own footprint premise holds
  (`ScopedSep (transferFootprint 1 caller caller)`), since only there are those valid calls known
  to be inhabited (`validInAt_inhabited`); the coverage says so.
* `spec` / `expected`: **every real caller, no hash premise anywhere in the coverage or the valid
  calls**. The translation (equivalence, termination, resources) never used the premise, only the
  step from the source's sequenced updates to the separated postcondition did
  (`targetPostAt_of_seq`). So the valid calls are `Valid deployed` (well-formed
  `transfer(to, v)` calldata, no value, storage writing the constructor's slot), inhabited in
  every context by the transfer of 0 to the caller itself, and the premise moves into the
  postcondition `PostAt caller`: the source's sequenced updates `SeqPostAt caller` (debit
  `caller`, then credit `to` reading the debited state: success condition, storage, log, return
  and revert data) unconditionally, and `TargetPostAt caller` for every call whose footprint
  premise holds. At a call with the premise, `PostAt` is at least `specScoped`'s postcondition.

Neither form has statement-level assumptions (`assumptions := []`).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec
open SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey Allowed balanceSlot fuel)

abbrev src : SolidCore.Verify.Generic.Source := SolidCore.Verify.Generic.Instances.Transfer.src
abbrev bytes : List Nat := SolidCore.Verify.Generic.Instances.Transfer.bytes

/-- The declared entrypoint, as in the default-context instance. -/
def entries : List (String × (SolidCore.Verify.Generic.Context → Call → Prop)) :=
  [("transfer(address,uint256)", fun _ call => SolarTV.Export.UniswapV2ERC20.CtxGas.TransferCall call)]

/-- A transfer of 0 from the caller to itself is a valid call from every real caller. -/
theorem valid_self (a : Nat) (ha : a < 2 ^ 160) :
    Valid Slice.Gen.deployed (transferCall Slice.σ0 a 0) :=
  ⟨Slice.σ0, a, 0, Slice.covers_σ0, ha, by decide, rfl⟩

/-- **SolidCore halts on every valid call sent by `a`**, with an allowed status, with no hash
premise. -/
theorem terminates_valid {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160) :
    Terminates (solidCoreFrom a fuel) c (Valid Slice.Gen.deployed) Allowed := by
  rintro _ ⟨σ, dst, v, hcov, hto, hv, rfl⟩
  refine ⟨_, run_tree hc ha hcov hto hv, ?_⟩
  have hs := fun k => Generic.slotValue_lt σ k
  by_cases hle : v ≤ slotValue σ (balKey a)
  · by_cases hov : debitAt a (slotValue σ) v (balKey dst) + v < 2 ^ 256
    · rw [res_ok ha hs hto hv hle hov]; exact Or.inl rfl
    · rw [res_add ha hs hto hv hle hov]; exact Or.inr (Or.inr rfl)
  · rw [res_sub ha hs hto hv hle]; exact Or.inr (Or.inl rfl)

/-- The source translation from every real caller on `Valid deployed`, with no hash premise. -/
theorem translation_from {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (ctx : SolidCore.Verify.Generic.Context)
    (hctx : ctx.Ok) :
    SolidCore.Verify.Generic.TranslationAt (solidCoreFrom ctx.caller fuel) c ctx
      SolidCore.Spec.UniswapV2.ERC20.Certified.code (Valid Slice.Gen.deployed) (fun _ => 8199112) where
  inhabited := ⟨_, valid_self ctx.caller hctx.1⟩
  equiv := fun gas hg call hv obs hrun => equiv_from hc ctx.caller hctx.1 hctx.2 gas hg call hv obs hrun
  terminates := fun call hv => by
    obtain ⟨obs, hs, -⟩ := terminates_valid hc ctx.caller hctx.1 call hv
    exact ⟨obs, hs, trivial⟩
  resources := fun call hv => by
    have h := SolidCore.Spec.UniswapV2.ERC20.Certified.resources_any_caller hc ctx.caller hctx.1 hctx.2
      call (SolidCore.Spec.UniswapV2.ERC20.Certified.valid_sub call hv)
    rw [SolarTV.Export.UniswapV2ERC20.CtxGas.G_eq] at h
    exact h

/-- Allowed statuses of every source result from `a`, from termination. -/
theorem allowed_from {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160) :
    ∀ call, Valid Slice.Gen.deployed call → ∀ obs, (solidCoreFrom a fuel).run c call = some obs →
      Allowed call obs := fun call hv obs hs => by
  obtain ⟨obs', hs', hal⟩ := terminates_valid hc a ha call hv
  have e : (solidCoreFrom a fuel).run c call = some obs := hs
  rw [e] at hs'
  cases hs'
  exact hal

/-- An empty revert, which the allowed statuses reject. -/
theorem not_allowed_emptyRevert (call : Call) :
    ¬ Allowed call SolidCore.Verify.Generic.Instances.Transfer.emptyRevert := by
  intro h
  rcases h with h | h | h
  · cases h
  · have := congrArg List.length h
    simp [SolidCore.Verify.Generic.Instances.Transfer.emptyRevert, Slice.errorData] at this
  · have := congrArg List.length h
    simp [SolidCore.Verify.Generic.Instances.Transfer.emptyRevert, Slice.errorData] at this

/-! ## Every real caller, no hash premise in the valid calls -/

/-- **The postcondition from `a`**: the source's sequenced updates, and the separated target
postcondition wherever the call's footprint premise holds. -/
def PostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  SeqPostAt a call obs ∧ (ScopeAt a call → TargetPostAt a call obs)

def spec : SolidCore.Verify.Generic.Spec where
  Contexts ctx := ctx.Ok
  entries := entries
  Valid _ := Valid Slice.Gen.deployed
  Allowed _ := Allowed
  Post ctx := PostAt ctx.caller
  gas _ _ := 8199112
  assumptions := []

/-- **Coverage from every real caller**: every context with a caller below `2 ^ 160` other than the
contract, and in each one a valid call of `transfer`, with no hash premise. -/
theorem covered : spec.Covered := by
  refine ⟨⟨_, SolidCore.Verify.Generic.Context.default_ok⟩, fun _ h => h, ?_, ?_, ?_⟩
  · intro ctx hctx e he
    simp only [spec, entries, List.mem_singleton] at he
    subst he
    have hv := valid_self ctx.caller hctx.1
    exact ⟨_, hv, SolidCore.Spec.UniswapV2.ERC20.Certified.selector_of _
      (SolidCore.Spec.UniswapV2.ERC20.Certified.valid_sub _ hv)⟩
  · obtain ⟨call, obs, hv, hn⟩ := Slice.nonVacuous_target
    exact ⟨SolidCore.Verify.Generic.Context.default, call, obs,
      SolidCore.Verify.Generic.Context.default_ok, hv.1, fun h => hn (h.2 hv.2)⟩
  · exact ⟨SolidCore.Verify.Generic.Context.default, Slice.call0,
      SolidCore.Verify.Generic.Instances.Transfer.emptyRevert,
      SolidCore.Verify.Generic.Context.default_ok, Slice.valid_call0.1, rfl, not_allowed_emptyRevert Slice.call0⟩

/-- **transfer's certificate from every real caller.** -/
def certificate : SolidCore.Verify.Generic.Certificate src spec bytes where
  code := SolidCore.Spec.UniswapV2.ERC20.Certified.code
  bound := rfl
  checked := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  translation := by
    rintro - ctx hctx c hc
    rw [SolidCore.Verify.Generic.Instances.Transfer.checked_eq] at hc
    exact translation_from hc ctx hctx
  specProof := by
    rintro - ctx hctx c hc
    rw [SolidCore.Verify.Generic.Instances.Transfer.checked_eq] at hc
    exact ⟨allowed_from hc ctx.caller hctx.1, fun call hv obs hs =>
      ⟨meets_seq hc ctx.caller hctx.1 call hv obs hs,
        fun hsc => targetPostAt_of_seq hctx.1 (meets_seq hc ctx.caller hctx.1 call hv obs hs) hsc⟩⟩
  covered := covered

/-- **UniswapV2ERC20.transfer meets the generic expected theorem from every real caller.** -/
theorem expected : SolidCore.Verify.Generic.Expected src spec bytes := certificate.expected

/-! ## `certified_from` as stated -/

/-- 0x2000's own footprint premise, by the kernel's Keccak-256 (from `Slice.scope_call0`). -/
theorem scopedSep_self_default :
    ScopedSep (transferFootprint balanceSlot SolidCore.Verify.Generic.Context.default.caller
      SolidCore.Verify.Generic.Context.default.caller) := by
  have h := Slice.scope_call0 Slice.σ0 1 0 rfl (by decide) (by decide)
  refine TrustedBase.KeccakSeparated.mono h fun x hx => ?_
  simp only [transferFootprint, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl <;> exact Or.inl rfl

def specScoped : SolidCore.Verify.Generic.Spec where
  Contexts ctx := ctx.Ok ∧ ScopedSep (transferFootprint balanceSlot ctx.caller ctx.caller)
  entries := entries
  Valid ctx := ValidInAt ctx.caller
  Allowed _ := Allowed
  Post ctx := TargetPostAt ctx.caller
  gas _ _ := 8199112
  assumptions := []

theorem coveredScoped : specScoped.Covered := by
  refine ⟨⟨_, SolidCore.Verify.Generic.Context.default_ok, scopedSep_self_default⟩,
    fun _ h => h.1, ?_, ?_, ?_⟩
  · intro ctx hctx e he
    simp only [specScoped, entries, List.mem_singleton] at he
    subst he
    obtain ⟨call, hv⟩ := validInAt_inhabited ctx.caller hctx.1.1 hctx.2
    exact ⟨call, hv, SolidCore.Spec.UniswapV2.ERC20.Certified.selector_of _
      (SolidCore.Spec.UniswapV2.ERC20.Certified.valid_sub _ hv.1)⟩
  · obtain ⟨call, obs, hv, hn⟩ := Slice.nonVacuous_target
    exact ⟨SolidCore.Verify.Generic.Context.default, call, obs,
      ⟨SolidCore.Verify.Generic.Context.default_ok, scopedSep_self_default⟩, hv, hn⟩
  · exact ⟨SolidCore.Verify.Generic.Context.default, Slice.call0,
      SolidCore.Verify.Generic.Instances.Transfer.emptyRevert,
      ⟨SolidCore.Verify.Generic.Context.default_ok, scopedSep_self_default⟩, Slice.valid_call0, rfl,
      not_allowed_emptyRevert Slice.call0⟩

/-- **`certified_from`'s certificate**, from `certified_from` itself. -/
def certificateScoped : SolidCore.Verify.Generic.Certificate src specScoped bytes where
  code := SolidCore.Spec.UniswapV2.ERC20.Certified.code
  bound := rfl
  checked := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  translation := by
    rintro - ctx hctx c hc
    rw [SolidCore.Verify.Generic.Instances.Transfer.checked_eq] at hc
    obtain ⟨c', hc', h⟩ := certified_from
    rw [hc'] at hc
    cases hc
    have H := h ctx.caller hctx.1.1 hctx.1.2
    exact
      { inhabited := validInAt_inhabited ctx.caller hctx.1.1 hctx.2
        equiv := H.equiv
        terminates := fun call hv => by
          obtain ⟨obs, hs, -⟩ := H.terminates call hv
          exact ⟨obs, hs, trivial⟩
        resources := H.resources }
  specProof := by
    rintro - ctx hctx c hc
    rw [SolidCore.Verify.Generic.Instances.Transfer.checked_eq] at hc
    obtain ⟨c', hc', h⟩ := certified_from
    rw [hc'] at hc
    cases hc
    have H := h ctx.caller hctx.1.1 hctx.1.2
    refine ⟨fun call hv obs hs => ?_, H.meets⟩
    obtain ⟨obs', hs', hal⟩ := H.terminates call hv
    have e : (solidCoreFrom ctx.caller fuel).run _ call = some obs := hs
    rw [e] at hs'
    cases hs'
    exact hal
  covered := coveredScoped

/-- **`certified_from` as the generic expected theorem**, over every caller whose own footprint
premise holds. -/
theorem expected_scoped : SolidCore.Verify.Generic.Expected src specScoped bytes :=
  certificateScoped.expected

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.expected_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected_scoped

end SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected
