import Contracts.Token.Lowering
import SolidCore.Refinement.Generic.StageIn

/-!
# solar-verify's Token: the source stage in every world

`stageIn` is `Contracts/Token/Lowering.lean`'s `stage` with SolidCore run in any world `W` (any call
oracle, any other accounts' code; SolidCore/Refinement/SourceOracle.lean), from the same kernel
check: Token makes no external call, so its stage holds in every world, the open ones that
`holds_of_runs` quantifies over included, with no hypothesis on the world.
-/

namespace SolidCore.Refinement.Solar.VerifyTokenSource

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Verify.VC.Token
open SolarTV.Export.Token (stage0)

/-- **The source stage of solar-verify's Token in every world.** -/
theorem stageIn (W : World) (o : SolarTV.Machine.Oracle) (henv : SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {fn : Fn}
    (h : checkOn stage0 fn = some true) :
    Stage (solidCoreIn W fuel) (SolarTV.MIR.Lowered.moduleSem o) c stage0
      (SolidCore.Verify.VC.stageScope fn [(2, 4096)]) := by
  obtain ⟨d, hd⟩ := deployed hc
  exact Generic.stageInAtEnv W o henv hd (check_of hc h)

/-- `transfer`'s stage in every world, from the kernel's check. -/
theorem stageIn_transfer (W : World) (o : SolarTV.Machine.Oracle) (henv : SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCoreIn W fuel) (SolarTV.MIR.Lowered.moduleSem o) c stage0
      (SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)]) :=
  stageIn W o henv hc check_transfer_eq

/-- info: 'SolidCore.Refinement.Solar.VerifyTokenSource.stageIn_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageIn_transfer

end SolidCore.Refinement.Solar.VerifyTokenSource
