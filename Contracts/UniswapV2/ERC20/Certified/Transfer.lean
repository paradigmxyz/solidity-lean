import Contracts.UniswapV2.ERC20.SourceMir
import Contracts.UniswapV2.ERC20.Slice.Bytes
import uv2_erc20.Gas
import uv2_erc20.ProofsT.Stages
import uv2_erc20.AnyCaller
import Contracts.UniswapV2.ERC20.SourceMirFrom

/-!
# UniswapV2ERC20.transfer: certified, with the bytes matching the source from any caller

The composition of the slice's edges into one `Shapes.Certified` statement (docs/CERTIFICATION_TARGET.md,
first slice), for `transfer(address,uint256)` of the pinned port on the exact runtime bytes
`CtxGas.code`, from the edges already proved and checked in CI:

* E3 `SourceMir.check_ok` / `SourceMir.transfer_stage`: SolidCore's checked source to solar's
  first lowered MIR `stage0` (here through `compiled0XL`, which takes the same check);
* E4 `SolarTV.Milestone.Uv2Erc20T.uv2_erc20_transfer_mir_to_evmir`: `stage0` to the final EVM IR
  `evm11` on the calls of transfer's selector, under every oracle;
* E5 + E8 `CtxGas.check_ok` with the guard stage (`guard_ends`, `guard_run`): the checker with
  contexts and gas accepts the exact bytes against `evm11` (in effect form), which gives the
  equivalence at every gas and the gas bound `G = 8199112` (`CtxGas.G_eq`);
* E7 `Slice.meets_target` and `Slice.terminates`: `TargetPost` and the allowed statuses of every
  SolidCore run of a valid call, through `Slice.certified_of`.

**Caller.** Every edge's semantics fixes the caller to `callerAddress` = `Generic.callerWord` =
0x2000 (`SolarTV.Call` has no caller field), so `certified` is about calls from 0x2000.
`certified_any_caller` adds, for every caller `a < 2 ^ 160` other than the contract, that the exact
bytes run from `a` give SolidCore's run of the call sent by `a` (`ResourcesFrom`): E3 from any
caller (`SourceMirFrom.transfer_stage_from`, the generic check with a symbolic caller), E4 under
every oracle and the gas edge from any caller (`AnyCaller.resources_any_caller`). The
postcondition `TargetPost` is still stated at 0x2000.

**Not yet covered.** The deployer stays `callerAddress`, and `TargetPost` and the allowed statuses
are stated for calls from 0x2000 only. E6 (that `code` is the bytes a fresh solar run emits, by
driver byte equality and a leanchecker replay) is pending: the statement is about `CtxGas.code` as
exported at the pinned solar commit.

**Premise.** The valid calls are `Slice.ValidIn` = `Valid deployed call ∧ Scope call`, where
`Scope call` is the scoped hash premise
`ScopedSep (transferFootprint balanceSlot caller dst)` of the call's recipient `dst` (keccak256
separated on the two balance preimages only). It is part of the statement's precondition, at the
call it is about; nothing else is assumed.

* `certified`: `∃ c, contract? = .ok c ∧ Certified (solidCore fuel) c code ValidIn Allowed
  TargetPost (fun _ => 8199112)`.
* `certified_any_caller`: `certified` and `ResourcesFrom (fun a => (solidCoreFrom a fuel).run c)
  code (genericValid0 fns deployed) (fun _ => 8199112)`.
* `self_max_bytes`, `self_short_bytes`: the two required self-transfer cases run on the exact
  bytes (EthLib), from the gas bound on: balance `2 ^ 256 - 1`, `transfer(caller, 1)` succeeds
  with the storage unchanged and `Transfer(caller, caller, 1)` logged; a self-transfer of 6 from a
  balance of 5 reverts with `Error("ds-math-sub-underflow")` and no change. Neither needs the hash
  premise (they use the compiled shape on `Valid`).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Certified

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice SolidCore.Spec.UniswapV2.ERC20.Slice.Gen
open SolarTV.Export.UniswapV2ERC20.CtxGas

/-- The exact runtime bytes. -/
abbrev code : ByteArray := SolarTV.Export.UniswapV2ERC20.CtxGas.code

/-- A valid call of the slice is a call of E3's generic stage. -/
theorem valid_sub : ∀ call, Valid deployed call →
    genericValid0 SourceMir.fns SourceMir.deployed call := by
  rintro _ ⟨σ, dst, v, hcov, hto, hv, rfl⟩
  refine ⟨σ, ?_, SourceMir.fn_transfer, List.mem_singleton_self _, [dst, v], rfl,
    by intro a ha; simp at ha; rcases ha with rfl | rfl <;> omega, rfl⟩
  intro kv hkv
  simp only [SourceMir.deployed, List.mem_singleton] at hkv
  subst hkv
  exact hcov _ (by simp [deployed])

/-- A call of E3's generic stage has transfer's selector. -/
theorem selector_of : ∀ call, genericValid0 SourceMir.fns SourceMir.deployed call →
    TransferCall call := by
  rintro _ ⟨σ, -, f, hf, args, hlen, hargs, rfl⟩
  simp only [SourceMir.fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact (SolidCore.Refinement.Generic.callFacts SourceMir.fn_transfer.sel (by decide) args hargs σ).selector

set_option maxRecDepth 200000 in
theorem hscope : ∀ call, genericValid0 SourceMir.fns SourceMir.deployed call →
    SolarTV.Milestone.Uv2Erc20T.scope call := by
  intro call h
  simp only [SolarTV.Milestone.Uv2Erc20T.scope]
  have hs := selector_of call h
  simp only [TransferCall] at hs
  rw [hs]
  decide

/-- E4 onto the final EVM IR's effect form (the same runs, `sem_norm`). -/
theorem backend : Stage (mirSem oracle) (evmirSem oracle) SolarTV.Export.UniswapV2ERC20.stage0
    (SolidCore.Refinement.Solar.AssembleCtx.norm prog) SolarTV.Milestone.Uv2Erc20T.scope :=
  fun call h obs hr => (SolidCore.Refinement.Solar.AssembleCtx.sem_norm oracle prog call).trans
    (SolarTV.Milestone.Uv2Erc20T.uv2_erc20_transfer_mir_to_evmir oracle call h obs hr)

set_option maxRecDepth 200000 in
/-- **E3, E4, E5 and E8 composed**: equivalence at every gas, termination and resources of the
exact bytes on E3's calls of transfer, with the gas bound `G`. -/
theorem compiled {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Compiled (solidCore fuel) c code (genericValid0 SourceMir.fns SourceMir.deployed) (fun _ => G) := by
  have hdep := SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy.deploy_eq
  simp only [SourceMir.deploy?, hc] at hdep
  obtain ⟨_, hdd⟩ := Wide.deployedAt_of hdep
  exact compiled0XL hdd (SourceMir.check_ok hc) SourceMir.valid_inhabited backend hscope
    (fun call h => guard_ends oracle call (selector_of call h))
    (fun call h => guard_run oracle call (selector_of call h)) check_ok G_lt

/-- Equivalence on the slice's valid calls with their premise. -/
theorem equiv {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Equiv (solidCore fuel) c code ValidIn :=
  fun gas hg call hv => (compiled hc).equiv.equiv gas hg call (valid_sub call hv.1)

/-- Resources on the slice's valid calls with their premise. -/
theorem resources {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Resources (solidCore fuel) c code ValidIn (fun _ => G) :=
  fun call hv => (compiled hc).resources call (valid_sub call hv.1)

/-- **UniswapV2ERC20.transfer is certified at the caller 0x2000**: on every call of
`transfer(dst, v)` from 0x2000 with well-formed calldata, no value and any storage writing the
constructor's slot, whose scoped hash premise `ScopedSep (transferFootprint 1 0x2000 dst)` holds,
the exact runtime bytes behave as SolidCore's checked source (at every gas, and exactly from
8199112 gas on), which ends with an allowed status and meets the target's postcondition. -/
theorem certified : ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
    Certified (solidCore fuel) c code ValidIn Allowed TargetPost (fun _ => 8199112) := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  have h := certified_of hc (equiv hc) (resources hc)
  rw [show (fun _ : Call => G) = fun _ => 8199112 from funext fun _ => G_eq] at h
  exact ⟨c, hc, h⟩

/-- The oracle of a call from `a` meets E3's premise: its caller is `a` and its Keccak-256 is
EthLib's. -/
theorem fromOk_oracleFrom {a : Nat} (ha : a < 2 ^ 160) : Generic.FromOk a (Shapes.oracleFrom a) :=
  ⟨by
    show ((BitVec.ofNat 160 a).setWidth 256).toNat = a
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)],
   fun x y _ _ => by
    show (Shapes.oracle.keccak _).toNat = _
    rw [Shapes.oracle_ok.1.2]
    exact SolidCore.Refinement.Keccak.ethKeccak_twoWords x y⟩

/-- **E3 from any caller, E4 and E5 composed**: from every account `a` below `2 ^ 160` but the
contract's own, on every call of transfer E3 takes, the exact runtime bytes run from `a` give
SolidCore's run of the call sent by `a`, at every gas from `G` on. -/
theorem resources_any_caller {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    ResourcesFrom (fun a => (solidCoreFrom a fuel).run c) code
      (genericValid0 SourceMir.fns SourceMir.deployed) (fun _ => G) := by
  have hdep := SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy.deploy_eq
  simp only [SourceMir.deploy?, hc] at hdep
  obtain ⟨_, hdd⟩ := Wide.deployedAt_of hdep
  refine SolarTV.Export.UniswapV2ERC20.AnyCaller.resources_any_caller selector_of ?_ ?_
  · intro a ha _ call hv
    exact Option.isSome_iff_exists.mp
      (Generic.definedFrom a ha hdd (SourceMirFrom.checkFrom_ok hc) call hv)
  · intro a ha _ call hv obs h
    exact SourceMirFrom.transfer_stage_from a ha (Shapes.oracleFrom a) (fromOk_oracleFrom ha) hc
      call hv obs h

/-- **UniswapV2ERC20.transfer is certified, with the bytes matching the source from any caller**:
the statement `certified` (at the caller 0x2000, where the postcondition is stated), and, from
every caller `a < 2 ^ 160` other than the contract, on every call of `transfer(dst, v)` with
well-formed calldata, no value and any storage writing the constructor's slot, the exact runtime
bytes run from `a` give SolidCore's run of the call sent by `a`, exactly from 8199112 gas on. -/
theorem certified_any_caller : ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
    Certified (solidCore fuel) c code ValidIn Allowed TargetPost (fun _ => 8199112) ∧
    ResourcesFrom (fun a => (solidCoreFrom a fuel).run c) code
      (genericValid0 SourceMir.fns SourceMir.deployed) (fun _ => 8199112) := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  have h := certified_of hc (equiv hc) (resources hc)
  have hr := resources_any_caller hc
  rw [show (fun _ : Call => G) = fun _ => 8199112 from funext fun _ => G_eq] at h hr
  exact ⟨c, hc, h, hr⟩

/-- The scoped hash premise inside the statement's valid calls, as stated. -/
theorem validIn_iff (call : Call) :
    ValidIn call ↔ Valid deployed call ∧ ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 →
      v < 2 ^ 256 → SolidCore.Spec.ScopedSep (SolidCore.Spec.transferFootprint 1 caller dst) :=
  Iff.rfl

/-- The caller every call of the statement comes from. -/
theorem caller_eq : caller = 0x2000 := rfl

/-! ## The required self-transfer cases, on the exact bytes -/

/-- From the gas bound on, the bytes give SolidCore's result on a valid call (no premise). -/
theorem bytes_eq_source {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {call : Call} (hv : Valid deployed call)
    {gas : Nat} (h1 : 8199112 ≤ gas) (h2 : gas < 2 ^ 256) :
    Final.Target.runWith gas code call = (solidCore fuel).run c call :=
  ((compiled hc).resources call (valid_sub call hv)).2 gas (by rw [G_eq]; exact h1) h2

/-- **Required case, on the bytes**: balance `2 ^ 256 - 1`, `transfer(caller, 1)` succeeds, the
storage is unchanged and `Transfer(caller, caller, 1)` is logged. -/
theorem self_max_bytes (gas : Nat) (h1 : 8199112 ≤ gas) (h2 : gas < 2 ^ 256) :
    slotValue σmax (balKey caller) = 2 ^ 256 - 1 ∧
    Final.Target.runWith gas code (transferCall σmax caller 1) =
      some ⟨true, be32 1, [transferLog caller caller 1], slotValue σmax⟩ := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  obtain ⟨hb, hrun⟩ := self_max hc
  exact ⟨hb, (bytes_eq_source hc ⟨σmax, caller, 1, covers_pair _ _, by decide, by decide, rfl⟩ h1 h2).trans hrun⟩

/-- **Required case, on the bytes**: a self-transfer of 6 from a balance of 5 reverts with
`Error("ds-math-sub-underflow")`, no log and no change. -/
theorem self_short_bytes (gas : Nat) (h1 : 8199112 ≤ gas) (h2 : gas < 2 ^ 256) :
    Final.Target.runWith gas code (transferCall σshort caller 6) =
      some ⟨false, errorData subMsg, [], slotValue σshort⟩ := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  exact (bytes_eq_source hc ⟨σshort, caller, 6, covers_pair _ _, by decide, by decide, rfl⟩ h1 h2).trans
    (self_short hc)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Certified.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Certified.self_max_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_max_bytes

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Certified.self_short_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_short_bytes

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Certified.certified_any_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_any_caller

end SolidCore.Spec.UniswapV2.ERC20.Certified
