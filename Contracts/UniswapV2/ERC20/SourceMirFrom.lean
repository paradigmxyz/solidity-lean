import Contracts.UniswapV2.ERC20.SourceMirFromCheck
import Contracts.UniswapV2.ERC20.SourceMirDeploy
import Verify.ShapeCtx

/-!
# UniswapV2ERC20.transfer from every caller: SolidCore's checked source to solar's first lowered MIR (E3)

`SourceMir.transfer_stage` fixes the caller (SolidCore's `callerAddress`, 0x2000). This module states
E3 for **every caller** `a < 2 ^ 160`, proved once by the generic checker with the caller a symbolic
word (`Generic.checkSym`, `Generic.stageFrom`), not per address:

* `checkFrom_eq` (`kernel_rfl`): the kernel evaluates `Generic.checkSym` of stage0 for `[fn_transfer]`
  to `true`. The source side erases `msg.sender` to `WExpr.caller`, knowing only that it fits in 160
  bits; the MIR side reads `CALLER` as the same word (`EnvFlags.allSym`).
* `transfer_stage_from`: for every `a < 2 ^ 160` and every oracle `o` with `FromOk a o` (its caller is `a`
  and its Keccak-256 of two words is SolidCore's slot hash, i.e. Keccak-256), the stage
  `Stage (solidCoreFrom a fuel) (moduleSem o) c stage0 (genericValid0 fns deployed)`: on every valid call,
  sent by `a`, solar's first lowered MIR shows what SolidCore's checked source shows (status, return
  data, revert data, storage, logs).
* `fromOk_inhabited`: for every `a < 2 ^ 160` an oracle meets `FromOk a` (EthLib's Keccak-256 with caller
  `a`), so no case of the statement is vacuous.
* `transfer_source_mir_any_caller`: the closed statement. `transfer_stage_callerAddress`: its instance at
  `callerAddress` is the fixed-caller stage of `SourceMir` (`solidCoreFrom callerAddress = solidCore`).

`Source.runFrom a` is SolidCore's run of a call sent by `a` to the contract as `callerAddress` deployed
it (the constructor's caller is unchanged; transfer's constructor storage is `deployed`). No hash
separation premise: both sides compute the same mapping slots, so none is assumed.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.SourceMir

/-- **E3 for transfer, from every caller.** -/
theorem transfer_stage_from (a : Nat) (ha : a < 2 ^ 160) (o : SolarTV.Machine.Oracle) (ho : FromOk a o)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCoreFrom a SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed) := by
  have hdep := SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy.deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨_, hdd⟩ := Wide.deployedAt_of hdep
  exact stageFrom a ha o ho hdd (checkFrom_ok hc)

/-- The oracle of caller `a`: EthLib's Keccak-256, and `a` as `CALLER`. -/
def oracleFrom (a : Nat) : SolarTV.Machine.Oracle :=
  { Solar.Assemble.ethOracle ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩ with
    caller := BitVec.ofNat 160 a }

/-- For every caller the premise is satisfiable. -/
theorem fromOk_inhabited (a : Nat) (ha : a < 2 ^ 160) : FromOk a (oracleFrom a) :=
  ⟨by
    have : a < 1461501637330902918203684832716283019655932542976 := ha
    simp [oracleFrom]; omega,
   fun x y _ _ => SolidCore.Refinement.Keccak.ethKeccak_twoWords x y⟩

/-- **The edge, closed, for every caller**: the checked contract exists and E3 holds of it from every
caller `a < 2 ^ 160` under every oracle with `FromOk a`; for every such caller the premise is met, and
the valid calls are inhabited. -/
theorem transfer_source_mir_any_caller :
    (∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      ∀ a, a < 2 ^ 160 → ∀ o, FromOk a o →
        SolarTV.Stage (solidCoreFrom a SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
          SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed)) ∧
    (∀ a, a < 2 ^ 160 → ∃ o, FromOk a o) ∧ (∃ call, genericValid0 fns deployed call) := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  exact ⟨⟨c, hc, fun a ha o h => transfer_stage_from a ha o h hc⟩,
    fun a ha => ⟨oracleFrom a, fromOk_inhabited a ha⟩, genericValid0_inhabited fn_transfer [] deployed⟩

/-- At `callerAddress` the statement is the fixed-caller stage (on the oracles with that caller). -/
theorem transfer_stage_callerAddress (o : SolarTV.Machine.Oracle) (ho : FromOk callerAddress o)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed) := by
  exact transfer_stage_from callerAddress (by decide) o ho hc

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.transfer_source_mir_any_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_source_mir_any_caller

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.transfer_stage_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_stage_from

end SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom
