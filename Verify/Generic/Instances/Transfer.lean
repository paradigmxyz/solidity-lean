import Verify.Generic.Certificate
import Contracts.UniswapV2.ERC20.Certified.Transfer

/-!
# UniswapV2ERC20.transfer as an instance of the generic expected theorem

The regression milestone, restated as `Generic.Expected src spec bytes` from its existing
composition (`SolidCore.Spec.UniswapV2.ERC20.Certified.certified`), with no transfer-specific
statement:

* `src`: solc's AST of the pinned port (`Source.UniswapV2ERC20.importedSourceUnit`), the
  contract `UniswapV2ERC20`, the slice's fuel;
* `spec`: covered contexts: the default frame (caller `0x2000`) only, where the postcondition is
  stated; entrypoint `transfer(address,uint256)`, with a valid call in that context whose scoped
  hash premise holds of the real Keccak-256 (`valid_call0`); valid calls `ValidIn` (the premise
  `ScopedSep (transferFootprint 1 caller dst)` is part of each valid call); allowed statuses
  success, `ds-math-sub-underflow` or `ds-math-add-overflow`; postcondition `TargetPost`; gas
  bound 8,199,112; no statement-level assumptions;
* `bytes`: the bytes of the exported code `CtxGas.code`. The driver's fresh-compile binding (E6)
  replaces this with the literal it compiled and the kernel's `decide` of their equality; nothing
  else in the statement changes.
-/

namespace SolidCore.Verify.Generic.Instances.Transfer

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

def src : Source :=
  ⟨SolidCore.Verify.VC.Source.UniswapV2ERC20.importedSourceUnit, "UniswapV2ERC20", fuel⟩

def spec : Spec where
  Contexts ctx := ctx = Context.default
  entries := [("transfer(address,uint256)", fun _ call => SolarTV.Export.UniswapV2ERC20.CtxGas.TransferCall call)]
  Valid _ := ValidIn
  Allowed _ := Allowed
  Post _ := TargetPost
  gas _ _ := 8199112
  assumptions := []

def bytes : List Nat := SolidCore.Spec.UniswapV2.ERC20.Certified.code.data.toList.map (·.toNat)

theorem checked_eq : src.checked = SolidCore.Verify.VC.UniswapV2ERC20.contract? := rfl

/-- An empty revert, which the allowed statuses reject. -/
def emptyRevert : Observable := { success := false, output := [], logs := [], storage := fun _ => 0 }

theorem covered : spec.Covered := by
  refine ⟨⟨_, rfl⟩, by rintro _ rfl; exact Context.default_ok, ?_, ?_, ?_⟩
  · rintro _ rfl e he
    simp only [spec, List.mem_singleton] at he
    subst he
    exact ⟨call0, valid_call0, SolidCore.Spec.UniswapV2.ERC20.Certified.selector_of call0
      (SolidCore.Spec.UniswapV2.ERC20.Certified.valid_sub call0 valid_call0.1)⟩
  · obtain ⟨call, obs, hv, hn⟩ := nonVacuous_target
    exact ⟨_, call, obs, rfl, hv, hn⟩
  · refine ⟨_, call0, emptyRevert, rfl, valid_call0, rfl, ?_⟩
    intro h
    rcases h with h | h | h
    · cases h
    · have := congrArg List.length h
      simp [emptyRevert, errorData] at this
    · have := congrArg List.length h
      simp [emptyRevert, errorData] at this

/-- **transfer's certificate**, from its existing composition. -/
def certificate : Certificate src spec bytes where
  code := SolidCore.Spec.UniswapV2.ERC20.Certified.code
  bound := rfl
  checked := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  translation := by
    rintro - _ rfl c hc
    obtain ⟨c', hc', h⟩ := SolidCore.Spec.UniswapV2.ERC20.Certified.certified
    rw [checked_eq, hc'] at hc
    cases hc
    exact (certifiedAt_default h).translation
  specProof := by
    rintro - _ rfl c hc
    obtain ⟨c', hc', h⟩ := SolidCore.Spec.UniswapV2.ERC20.Certified.certified
    rw [checked_eq, hc'] at hc
    cases hc
    exact (certifiedAt_default h).spec
  covered := covered

/-- **UniswapV2ERC20.transfer meets the generic expected theorem.** -/
theorem expected : Expected src spec bytes := certificate.expected

/-- info: 'SolidCore.Verify.Generic.Instances.Transfer.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected

end SolidCore.Verify.Generic.Instances.Transfer
