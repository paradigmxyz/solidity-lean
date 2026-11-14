import Contracts.UniswapV2.ERC20.SourceMirCheck
import Contracts.UniswapV2.ERC20.SourceMirDeploy
import Verify.ShapeCtx

/-!
# UniswapV2ERC20.transfer: SolidCore's checked source to solar's first lowered MIR (E3)

The source-to-MIR edge (E3) of the first slice of docs/CERTIFICATION_TARGET.md, for
`transfer(address,uint256)` and the private `_transfer` it calls (SafeMath's checked `sub` and
`add` in `unchecked` blocks, the two `balanceOf` writes, sequential, and the `Transfer` event),
proved by the generic source checker alone: no per-contract glue and no hand-written model.

* The source is SolidCore's checked `UniswapV2ERC20` (`SolidCore.Verify.VC.UniswapV2ERC20.contract?`,
  the kernel's type check of the generated `Contracts/UniswapV2/ERC20/Source.lean`). The frontend
  that generated that file from the port is TRUSTED (edge E1).
* The MIR is `SolarTV.Export.UniswapV2ERC20.stage0`: solar's first lowered MIR of the same port
  (`-Ogas --evm-version osaka`), exported fresh at build time by
  `scripts/verify/uniswap_v2_erc20_stages.sh` (`-Zemit-lean-stages`, bytecode unchanged by the flag).
* `check_eq` (`kernel_rfl`): the kernel evaluates `Generic.check` of stage0 for `[fn_transfer]`,
  with the caller and two-word Keccak-256 flags, to `true`, from the source text up, with the
  selector, event-topic and Keccak-256 tables each entry of which the kernel checks once.
* `deploy_eq` (`kernel_rfl`): the constructor leaves exactly `deployed` (slot 3,
  `DOMAIN_SEPARATOR`) and no logs.
* `transfer_stage`: `Stage (solidCore fuel) (moduleSem o) c stage0 (genericValid0 fns deployed)`
  under every oracle `o` with `SourceEnvOk o`, from `Generic.stageAtEnv`.

`SourceEnvOk o` is the only premise. It asks that the oracle's caller be SolidCore's caller
`callerWord` (0x2000, the caller of every run of `solidCore`) and that its Keccak-256 of the 64
bytes of two words be SolidCore's slot hash of the same bytes, which is Keccak-256 itself. It is
not a hash-separation premise: both sides compute the same mapping slots, so no injectivity is
assumed. It is satisfiable: EthLib's own oracle meets it (`sourceEnvOk_inhabited`), so the
stage is not vacuous, and `valid_inhabited` gives a valid call.

Valid calls (`genericValid0 fns deployed`): `transfer(to, value)` on any argument words below
`2 ^ 256` (a `to` word above `2 ^ 160` reverts on both sides), no value, from any storage, given as
a list of entries, that lists the `DOMAIN_SEPARATOR` slot. The caller is `callerWord`: SolidCore's
semantics and `SolarTV.Call` fix it, so "any caller" is not stated here (see RESULT.md).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMir

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes

/-- **E3 for transfer**: on every valid call, solar's first lowered MIR shows what SolidCore's
checked source shows (status, return data, revert data, storage and logs), under every oracle
with SolidCore's caller and Keccak-256. -/
theorem transfer_stage (o : SolarTV.Machine.Oracle) (henv : SourceEnvOk o)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed) := by
  have hdep := SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy.deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨_, hdd⟩ := Wide.deployedAt_of hdep
  exact stageAtEnv o henv hdd (check_ok hc)

/-- The premise is satisfiable: EthLib's oracle has SolidCore's caller and Keccak-256. -/
theorem sourceEnvOk_inhabited : ∃ o, SourceEnvOk o :=
  ⟨Solar.Assemble.ethOracle ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩,
    sourceEnvOk_of (Solar.Assemble.ethOracle_ok _)⟩

/-- The valid calls are inhabited. -/
theorem valid_inhabited : ∃ call, genericValid0 fns deployed call :=
  genericValid0_inhabited fn_transfer [] deployed

/-- **The edge, closed**: the checked contract exists and E3 holds of it, the premise is
satisfiable and the valid calls are inhabited. -/
theorem transfer_source_mir :
    (∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      ∀ o, SourceEnvOk o →
        SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
          SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed)) ∧
    (∃ o, SourceEnvOk o) ∧ (∃ call, genericValid0 fns deployed call) := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  exact ⟨⟨c, hc, fun o h => transfer_stage o h hc⟩, sourceEnvOk_inhabited, valid_inhabited⟩

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.SourceMir.transfer_source_mir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_source_mir

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.SourceMir.transfer_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_stage

end SolidCore.Spec.UniswapV2.ERC20.SourceMir

