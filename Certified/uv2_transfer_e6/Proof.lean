import uv2_transfer_e6.Statement
import Contracts.UniswapV2.ERC20.Certified.TransferExpected

-- Untrusted proof script: the kernel checks it.

/-!
# The proof of `Certified.uv2_transfer_e6.Final.Statement`

The statement's definitions are the proof modules' by `rfl`; the translation, termination, the
specification and resources come from `CertifiedFrom` and `CertifiedExpected`; the coverage is
proved again for the statement's own entrypoint predicate; the bytes are bound by the kernel:
`bound` checks that the exported code's bytes are `runtimeBytes`, the bytes solar emitted in this
run (`decide +kernel`).
-/

namespace Certified.uv2_transfer_e6.Proof

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec
open SolidCore.Verify.Generic
open SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom
open SolidCore.Spec.UniswapV2.ERC20.Slice (transferCall)
open Certified.uv2_transfer_e6.Final (runtimeBytes src specAny specScoped)

/-- **The E6 binding**: the exported code's bytes are the bytes solar emitted in this run. -/
theorem bound : SolidCore.Spec.UniswapV2.ERC20.Certified.code.data.toList.map (·.toNat) = runtimeBytes := by
  decide +kernel

theorem src_eq : src = SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.src := rfl
theorem deployed_eq : Final.deployed = SolidCore.Spec.UniswapV2.ERC20.Slice.Gen.deployed := rfl
theorem allowed_eq : Final.Allowed = SolidCore.Spec.UniswapV2.ERC20.Slice.Allowed := rfl
theorem seq_eq : Final.SeqPostAt = SeqPostAt := rfl
theorem scope_eq : Final.ScopeAt = ScopeAt := rfl
theorem target_eq : Final.TargetPostAt = TargetPostAt := rfl

theorem checked_eq : src.checked = SolidCore.Verify.VC.UniswapV2ERC20.contract? := rfl

theorem entry_of {ctx : Context} {call : Call}
    (h : SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed call) :
    ∀ e ∈ Final.entries, ∃ c, (SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed c) ∧ e.2 ctx c := by
  intro e he
  simp only [Final.entries, List.mem_singleton] at he
  subst he
  refine ⟨call, h, ?_⟩
  obtain ⟨σ, dst, v, -, -, -, rfl⟩ := h
  exact ⟨σ, dst, v, rfl⟩

theorem nonvac_post : ∃ ctx call obs, specAny.Contexts ctx ∧ specAny.Valid ctx call ∧
    ¬ specAny.Post ctx call obs := by
  obtain ⟨call, obs, hv, hn⟩ := SolidCore.Spec.UniswapV2.ERC20.Slice.nonVacuous_target
  refine ⟨Context.default, call, obs, Context.default_ok, ?_, fun h => hn (h.2 hv.2)⟩
  show SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed call
  rw [deployed_eq]; exact hv.1

theorem coveredAny : specAny.Covered := by
  refine ⟨⟨_, Context.default_ok⟩, fun _ h => h, fun ctx hctx => ?_, nonvac_post, ?_⟩
  · have hv := SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.valid_self ctx.caller hctx.1
    rw [← deployed_eq] at hv
    exact entry_of hv
  · refine ⟨Context.default, SolidCore.Spec.UniswapV2.ERC20.Slice.call0,
      SolidCore.Verify.Generic.Instances.Transfer.emptyRevert, Context.default_ok, ?_, rfl,
      SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.not_allowed_emptyRevert SolidCore.Spec.UniswapV2.ERC20.Slice.call0⟩
    show SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed _
    rw [deployed_eq]; exact SolidCore.Spec.UniswapV2.ERC20.Slice.valid_call0.1

theorem coveredScoped : specScoped.Covered := by
  have hd := SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.scopedSep_self_default
  refine ⟨⟨_, Context.default_ok, hd⟩, fun _ h => h.1, fun ctx hctx => ?_, ?_, ?_⟩
  · obtain ⟨call, hv⟩ := validInAt_inhabited ctx.caller hctx.1.1 hctx.2
    intro e he
    simp only [specScoped, Final.entries, List.mem_singleton] at he
    subst he
    have hv' : SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed call := by
      rw [deployed_eq]; exact hv.1
    refine ⟨call, ⟨hv', hv.2⟩, ?_⟩
    obtain ⟨σ, dst, v, -, -, -, rfl⟩ := hv'
    exact ⟨σ, dst, v, rfl⟩
  · obtain ⟨call, obs, hv, hn⟩ := SolidCore.Spec.UniswapV2.ERC20.Slice.nonVacuous_target
    refine ⟨Context.default, call, obs, ⟨Context.default_ok, hd⟩, ⟨?_, hv.2⟩, hn⟩
    show SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed call
    rw [deployed_eq]; exact hv.1
  · refine ⟨Context.default, SolidCore.Spec.UniswapV2.ERC20.Slice.call0,
      SolidCore.Verify.Generic.Instances.Transfer.emptyRevert, ⟨Context.default_ok, hd⟩, ⟨?_,
      SolidCore.Spec.UniswapV2.ERC20.Slice.valid_call0.2⟩, rfl,
      SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.not_allowed_emptyRevert SolidCore.Spec.UniswapV2.ERC20.Slice.call0⟩
    show SolidCore.Spec.UniswapV2.ERC20.Slice.Valid Final.deployed _
    rw [deployed_eq]; exact SolidCore.Spec.UniswapV2.ERC20.Slice.valid_call0.1

def certAny : Certificate src specAny runtimeBytes where
  code := SolidCore.Spec.UniswapV2.ERC20.Certified.code
  bound := bound
  checked := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  translation := by
    rintro - ctx hctx c hc
    rw [checked_eq] at hc
    exact SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.translation_from hc ctx hctx
  specProof := by
    rintro - ctx hctx c hc
    rw [checked_eq] at hc
    exact ⟨SolidCore.Spec.UniswapV2.ERC20.CertifiedExpected.allowed_from hc ctx.caller hctx.1,
      fun call hv obs hs => ⟨meets_seq hc ctx.caller hctx.1 call hv obs hs,
        fun hsc => targetPostAt_of_seq hctx.1 (meets_seq hc ctx.caller hctx.1 call hv obs hs) hsc⟩⟩
  covered := coveredAny

def certScoped : Certificate src specScoped runtimeBytes where
  code := SolidCore.Spec.UniswapV2.ERC20.Certified.code
  bound := bound
  checked := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  translation := by
    rintro - ctx hctx c hc
    rw [checked_eq] at hc
    obtain ⟨c', hc', h⟩ := certified_from
    rw [hc'] at hc
    cases hc
    have H := h ctx.caller hctx.1.1 hctx.1.2
    have hin := validInAt_inhabited ctx.caller hctx.1.1 hctx.2
    exact
      { inhabited := hin
        equiv := H.equiv
        terminates := fun call hv => by
          obtain ⟨obs, hs, -⟩ := H.terminates call hv
          exact ⟨obs, hs, trivial⟩
        resources := H.resources }
  specProof := by
    rintro - ctx hctx c hc
    rw [checked_eq] at hc
    obtain ⟨c', hc', h⟩ := certified_from
    rw [hc'] at hc
    cases hc
    have H := h ctx.caller hctx.1.1 hctx.1.2
    refine ⟨fun call hv obs hs => ?_, H.meets⟩
    obtain ⟨obs', hs', hal⟩ := H.terminates call hv
    have e : (solidCoreFrom ctx.caller SolidCore.Spec.UniswapV2.ERC20.Slice.fuel).run c call = some obs := hs
    rw [e] at hs'
    cases hs'
    exact hal
  covered := coveredScoped

theorem statement : Certified.uv2_transfer_e6.Final.Statement := ⟨certAny.expected, certScoped.expected⟩

end Certified.uv2_transfer_e6.Proof
