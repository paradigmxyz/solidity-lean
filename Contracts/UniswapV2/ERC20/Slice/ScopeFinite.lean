import Contracts.UniswapV2.ERC20.Slice.Post
import Verify.Spec.HashScopeFinite

/-!
# UniswapV2ERC20.transfer: the call's scope from one premise on a finite set of addresses

The slice's valid calls carry, call by call, the scoped hash premise of the call (`Scope`, and
`CertifiedFrom.ScopeAt a` / `ScopeFromAt a` for the caller `a`): keccak256 separated on the
caller's and the recipient's `balanceOf` preimages. Verify/Spec/HashScopeFinite.lean states one
premise for a finite set `A` of addresses, `KeccakSep (erc20Preimages 1 2 A)` (UniswapV2ERC20's
layout: `balanceOf` at slot 1, `allowance` at slot 2). This module discharges every call's premise
from it, for every call whose caller and recipient are in `A`:

* `ScopeBy a call`: the call's premise for the caller `a` (`scopeBy_caller`: at the interface's
  caller it is the slice's `Scope`, by `rfl`; it is also the body of `CertifiedFrom.ScopeAt a`);
* `RecipientIn A call`: the recipient of the call of `transfer` is in `A`;
  `recipientIn_transferCall` gives it for `transferCall σ dst v` with `dst ∈ A`;
* `scopeBy_of_keccakSep`: `KeccakSep (erc20Preimages 1 2 A)`, `a ∈ A` and `RecipientIn A call`
  give `ScopeBy a call`, the self-transfer (`dst = a`) included (`scopeBy_self_of_keccakSep`);
  `scope_of_keccakSep` at the interface's caller;
* `real_scopeBy_ABC`: with `A` the three addresses of `real_erc20_ABC`, the premise holds of the
  real keccak256, so every call among them has its scope with no hypothesis.

**Bounds.** `A` is any finite set of naturals; the call's own validity bounds the recipient
(`dst < 2 ^ 160`). Nothing is assumed of keccak256 outside `erc20Preimages 1 2 A`. The premise is a
hypothesis, never claimed for every `A`: it is false once `A` has more than `2 ^ 128` elements
(pigeonhole on the inner allowance preimages of `A ×ˢ A`), so the statements say something only for
small `A`, such as the three addresses of `real_erc20_ABC`.

**Negative controls.** `recipientIn_outside`: the call to `addrB` is not one of `{addrA}`'s
calls, and `scopeBy_outside_rejected` makes this file build only while the derivation of the
scope of `transfer(addrB, 0)` from the premise of `A = {addrA}` is refused.
`balance_not_mem_singleton`: the premise of `A = {addrA}` names no preimage of `addrB`'s balance.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec TrustedBase

/-- **The scoped premise of a call sent by `a`**: keccak256 separated on the preimages of `a`'s and
the recipient's `balanceOf` slots (the body of `Scope`, `ScopeFromAt a` and
`CertifiedFrom.ScopeAt a`). -/
def ScopeBy (a : Nat) (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    ScopedSep (transferFootprint balanceSlot a dst)

/-- At the interface's caller it is the slice's `Scope`. -/
theorem scopeBy_caller : ScopeBy caller = Scope := rfl

/-- **The recipient of a call of `transfer` is in `A`.** -/
def RecipientIn (A : Finset Nat) (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 → dst ∈ A

/-- The recipient of `transfer(dst, v)` is `dst`: the argument words of the call data. -/
theorem dst_of_transferCall {σ σ' : List (Nat × Nat)} {dst dst' v v' : Nat} (hto : dst < 2 ^ 256)
    (hv : v < 2 ^ 256) (hto' : dst' < 2 ^ 256) (hv' : v' < 2 ^ 256)
    (h : transferCall σ dst v = transferCall σ' dst' v') : dst = dst' := by
  have e1 : callArgs (transferCall σ dst v) = [dst, v] := by
    simp only [callArgs, transferCall]
    exact words_calldata _ (by simp; omega)
  have e2 : callArgs (transferCall σ' dst' v') = [dst', v'] := by
    simp only [callArgs, transferCall]
    exact words_calldata _ (by simp; omega)
  have ha := congrArg callArgs h
  rw [e1, e2] at ha
  simp only [List.cons.injEq] at ha
  exact ha.1

/-- **`transfer(dst, v)` with `dst ∈ A` has its recipient in `A`.** -/
theorem recipientIn_transferCall {A : Finset Nat} (σ : List (Nat × Nat)) {dst v : Nat}
    (hdst : dst ∈ A) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256) :
    RecipientIn A (transferCall σ dst v) := by
  intro σ' dst' v' h hto' hv'
  rw [← dst_of_transferCall (by omega) hv (by omega) hv' h]
  exact hdst

/-- **Every call sent by `a ∈ A` to a recipient in `A` has its scope**, from the one premise
`KeccakSep (erc20Preimages 1 2 A)` (`transfer_sep`). -/
theorem scopeBy_of_keccakSep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A)) {a : Nat}
    (ha : a ∈ A) {call : Call} (hr : RecipientIn A call) : ScopeBy a call :=
  fun σ dst v hc hto hv => transfer_sep h ha (hr σ dst v hc hto hv)

/-- The self-transfer: `transfer(a, v)` sent by `a ∈ A`. -/
theorem scopeBy_self_of_keccakSep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A))
    {a : Nat} (ha : a ∈ A) (ha' : a < 2 ^ 160) (σ : List (Nat × Nat)) {v : Nat} (hv : v < 2 ^ 256) :
    ScopeBy a (transferCall σ a v) :=
  scopeBy_of_keccakSep h ha (recipientIn_transferCall σ ha ha' hv)

/-- **The slice's `Scope`** (the caller 0x2000) of every call to a recipient in `A`, when
0x2000 is in `A`. -/
theorem scope_of_keccakSep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A))
    (hc : caller ∈ A) {call : Call} (hr : RecipientIn A call) : Scope call :=
  scopeBy_of_keccakSep h hc hr

/-- **The three addresses of `real_erc20_ABC`, at the real keccak256**: every call among them has
its scope, with no hypothesis. -/
theorem real_scopeBy_ABC : ∀ a ∈ addrsABC, ∀ call, RecipientIn addrsABC call → ScopeBy a call :=
  fun _ ha _ hr => scopeBy_of_keccakSep real_erc20_ABC ha hr

/-! ## Negative controls: a recipient outside `A` -/

/-- **`transfer(addrB, 0)` is not a call to a recipient in `{addrA}`.** -/
theorem recipientIn_outside (σ : List (Nat × Nat)) :
    ¬ RecipientIn {addrA} (transferCall σ addrB 0) :=
  fun h => absurd (h σ addrB 0 rfl (by decide) (by decide)) (by decide)

set_option maxRecDepth 100000 in
/-- **The premise of `A = {addrA}` names no preimage of `addrB`'s balance**: the balance preimage
`addrB . 1` is not in `erc20Preimages 1 2 {addrA}` (by the kernel, the inner allowance preimage's
keccak256 included). -/
theorem balance_not_mem_singleton : mappingPreimage addrB 1 ∉ erc20Preimages 1 2 {addrA} := by
  simp only [erc20Preimages, balancePreimages, allowancePreimages, Finset.mem_union,
    Finset.image_singleton, Finset.singleton_product_singleton, Finset.mem_singleton, not_or]
  decide +kernel

/-- `scopeBy_of_keccakSep` refuses a recipient outside `A`: from the premise of `A = {addrA}`, the
scope of the self-transfer of `addrA` elaborates, and that of `transfer(addrB, 0)` does not (its side
condition `addrB ∈ {addrA}` is false); `fail_if_success` makes this file build only while it is
refused. -/
theorem scopeBy_outside_rejected (h : KeccakSep (erc20Preimages 1 2 {addrA}))
    (σ : List (Nat × Nat)) : True := by
  have _hself : ScopeBy addrA (transferCall σ addrA 0) :=
    scopeBy_of_keccakSep h (by decide) (recipientIn_transferCall σ (by decide) (by decide) (by decide))
  fail_if_success
    have _hB : ScopeBy addrA (transferCall σ addrB 0) :=
      scopeBy_of_keccakSep h (by decide) (recipientIn_transferCall σ (by decide) (by decide) (by decide))
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.recipientIn_transferCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recipientIn_transferCall

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.scopeBy_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scopeBy_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.scopeBy_self_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scopeBy_self_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.scope_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.real_scopeBy_ABC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_scopeBy_ABC

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.recipientIn_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recipientIn_outside

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.balance_not_mem_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms balance_not_mem_singleton

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.scopeBy_outside_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scopeBy_outside_rejected

end SolidCore.Spec.UniswapV2.ERC20.Slice
