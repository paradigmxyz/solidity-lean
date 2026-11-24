import Contracts.UniswapV2.ERC20.Certified.TransferFrom
import Contracts.UniswapV2.ERC20.Slice.ScopeFinite

-- Untrusted proof script: the kernel checks it.

/-!
# UniswapV2ERC20.transfer certified among a finite set of addresses, from one hash premise

`CertifiedFrom.certified_from` states the certified statement for every caller `a` on
`ValidInAt a`: the valid calls together with each call's own hash premise `ScopeAt a`
(`ScopedSep (transferFootprint 1 a dst)`). Here that per-call premise is discharged, for every
call whose caller and recipient are in a finite set `A`, by the one premise
`KeccakSep (erc20Preimages 1 2 A)` of Verify/Spec/HashScopeFinite.lean:

* `ValidFinAt A a`: the slice's valid calls (`Valid deployed`) whose recipient is in `A`, with no
  hash premise;
* `scope_of_keccakSep`, `validInAt_of_keccakSep`: from `KeccakSep (erc20Preimages 1 2 A)` and
  `a ∈ A`, every such call has `ScopeAt a` and is in `ValidInAt a` (the self-transfer included);
* `certifiedAt_mono`: `CertifiedAt` holds on every smaller precondition, with the same
  equivalence, termination, postcondition and gas bound;
* `certified_finite`: **the statement**: from `KeccakSep (erc20Preimages 1 2 A)`, for every
  caller `a ∈ A` below `2 ^ 160` other than the contract, `CertifiedAt a fuel c code
  (ValidFinAt A a) Allowed (TargetPostAt a) 8199112`: `certified_from`'s obligations, unchanged,
  on `A`'s calls;
* `certified_finite_callerAddress`: at the interface's caller 0x2000 (when it is in `A`), the
  slice's `Shapes.Certified` with `TargetPost` on `ValidFin A` (inhabited by the self-transfer);
* `real_certified_ABC`: with `A` the three addresses of `real_erc20_ABC`, the premise holds of the
  real keccak256 by the kernel, so the statement holds for them with **no hash hypothesis**.

**Bounds.** `A` is a finite set; callers are below `2 ^ 160` and not the contract, as in
`certified_from`. Nothing is assumed of keccak256 outside `erc20Preimages 1 2 A`, and no statement
here is about recipients outside `A`. The premise is a hypothesis, never claimed for every `A`: it is
false once `A` has more than `2 ^ 128` elements (pigeonhole on the inner allowance preimages), so
`certified_finite` says something only for small `A`; `real_certified_ABC` is its instance at three
addresses.

**Negative controls.** `validFinAt_outside`: the call to `addrB` is not a valid call of
`{addrA}`; `validIn_outside_rejected` makes this file build only while deriving `ValidInAt addrA` of
`transfer(addrB, 0)` from the premise of `A = {addrA}` is refused.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes
open SolidCore.Spec SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall Allowed fuel RecipientIn
  recipientIn_transferCall)

/-- **The valid calls sent by `a` to a recipient in `A`**: no hash premise. (The caller `a` is the
statement's; the precondition does not depend on it.) -/
def ValidFinAt (A : Finset Nat) (_a : Nat) (call : Call) : Prop :=
  Valid Slice.Gen.deployed call ∧ RecipientIn A call

/-- The valid calls of the interface's caller 0x2000 to a recipient in `A`. -/
abbrev ValidFin (A : Finset Nat) : Call → Prop := ValidFinAt A Generic.callerWord

/-- **The per-call premise of every call among `A`**, from the one premise on `A`. -/
theorem scopeAt_of_keccakSep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A)) {a : Nat}
    (ha : a ∈ A) {call : Call} (hr : RecipientIn A call) : ScopeAt a call :=
  Slice.scopeBy_of_keccakSep h ha hr

/-- **Every valid call sent by `a ∈ A` to a recipient in `A` is in `ValidInAt a`**: the
precondition of `certified_from`, its hash premise discharged. -/
theorem validInAt_of_keccakSep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A)) {a : Nat}
    (ha : a ∈ A) : ∀ call, ValidFinAt A a call → ValidInAt a call :=
  fun _ hv => ⟨hv.1, scopeAt_of_keccakSep h ha hv.2⟩

/-- **`CertifiedAt` on a smaller precondition**: the same four obligations. -/
theorem certifiedAt_mono {a fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {V V' : Call → Prop} {Al P : Call → Observable → Prop} {G : Nat}
    (h : CertifiedAt a fuel c code V Al P G) (hV : ∀ call, V' call → V call) :
    CertifiedAt a fuel c code V' Al P G where
  equiv := fun gas hg call hv => h.equiv gas hg call (hV call hv)
  terminates := fun call hv => h.terminates call (hV call hv)
  meets := fun call hv => h.meets call (hV call hv)
  resources := fun call hv => h.resources call (hV call hv)

/-- **UniswapV2ERC20.transfer is certified among the addresses of `A`, from one hash premise**: if
keccak256 is separated on `erc20Preimages 1 2 A`, then for every caller `a ∈ A` below `2 ^ 160` other
than the contract, on every call of `transfer(dst, v)` sent by `a` with `dst ∈ A` (`dst = a` included),
well-formed calldata, no value and any storage writing the constructor's slot, the exact runtime
bytes run from `a` behave as SolidCore's checked source run by `a` (at every gas, and exactly from
8199112 gas on), which ends with an allowed status and meets `TargetPostAt a`. -/
theorem certified_finite {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A)) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      ∀ a ∈ A, a < 2 ^ 160 → a ≠ selfAddress →
        CertifiedAt a fuel c Certified.code (ValidFinAt A a) Allowed (TargetPostAt a) 8199112 := by
  obtain ⟨c, hc, hcert⟩ := certified_from
  exact ⟨c, hc, fun a ha hlt hne => certifiedAt_mono (hcert a hlt hne) (validInAt_of_keccakSep h ha)⟩

/-- The valid calls of a caller in `A` are inhabited, by the self-transfer of 0. -/
theorem validFinAt_inhabited {A : Finset Nat} {a : Nat} (ha : a ∈ A) (ha' : a < 2 ^ 160) :
    ∃ call, ValidFinAt A a call :=
  ⟨transferCall Slice.σ0 a 0, ⟨Slice.σ0, a, 0, Slice.covers_σ0, ha', by decide, rfl⟩,
    recipientIn_transferCall Slice.σ0 ha ha' (by decide)⟩

/-- **At the interface's caller 0x2000, the slice's `Shapes.Certified`** with `TargetPost` on the
valid calls to a recipient in `A`, when 0x2000 is in `A`. -/
theorem certified_finite_callerAddress {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A))
    (hA : Generic.callerWord ∈ A) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Certified (solidCore fuel) c Certified.code (ValidFin A) Allowed Slice.TargetPost
        (fun _ => 8199112) := by
  obtain ⟨c, hc, hcert⟩ := certified_finite h
  exact ⟨c, hc, (hcert callerAddress hA (by decide) (by decide)).certified
    (validFinAt_inhabited hA (by decide))⟩

/-- **The three addresses of `real_erc20_ABC`, with no hash hypothesis**: for every caller `a` among
them, on every valid call of `transfer(dst, v)` sent by `a` with `dst` among them, the certified
statement holds (the premise `KeccakSep (erc20Preimages 1 2 addrsABC)` by the kernel's keccak256). -/
theorem real_certified_ABC : ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
    ∀ a ∈ addrsABC,
      CertifiedAt a fuel c Certified.code (ValidFinAt addrsABC a) Allowed (TargetPostAt a) 8199112 := by
  obtain ⟨c, hc, hcert⟩ := certified_finite real_erc20_ABC
  refine ⟨c, hc, fun a ha => hcert a ha ?_ ?_⟩ <;>
  · simp only [addrsABC, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> decide

/-! ## Negative controls: a recipient outside `A` -/

/-- **`transfer(addrB, 0)` is not a valid call of `{addrA}`**, whatever the caller. -/
theorem validFinAt_outside (a : Nat) (σ : List (Nat × Nat)) :
    ¬ ValidFinAt {addrA} a (transferCall σ addrB 0) :=
  fun h => Slice.recipientIn_outside σ h.2

/-- `validInAt_of_keccakSep` refuses a recipient outside `A`: from the premise of `A = {addrA}`, the
self-transfer of `addrA` is in `ValidInAt addrA`, and the derivation for `transfer(addrB, 0)` does
not elaborate (its side condition `addrB ∈ {addrA}` is false); `fail_if_success` makes this file build
only while it is refused. -/
theorem validIn_outside_rejected (h : KeccakSep (erc20Preimages 1 2 {addrA})) : True := by
  have _hself : ValidInAt addrA (transferCall Slice.σ0 addrA 0) :=
    validInAt_of_keccakSep h (by decide) _
      ⟨⟨Slice.σ0, addrA, 0, Slice.covers_σ0, by decide, by decide, rfl⟩,
        recipientIn_transferCall Slice.σ0 (by decide) (by decide) (by decide)⟩
  fail_if_success
    have _hB : ValidInAt addrA (transferCall Slice.σ0 addrB 0) :=
      validInAt_of_keccakSep h (by decide) _
        ⟨⟨Slice.σ0, addrB, 0, Slice.covers_σ0, by decide, by decide, rfl⟩,
          recipientIn_transferCall Slice.σ0 (by decide) (by decide) (by decide)⟩
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.scopeAt_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scopeAt_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.validInAt_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInAt_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.certifiedAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedAt_mono

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.certified_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_finite

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.validFinAt_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validFinAt_inhabited

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.certified_finite_callerAddress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_finite_callerAddress

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.real_certified_ABC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_certified_ABC

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.validFinAt_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validFinAt_outside

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite.validIn_outside_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validIn_outside_rejected

end SolidCore.Spec.UniswapV2.ERC20.CertifiedFinite
