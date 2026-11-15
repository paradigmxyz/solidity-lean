import Contracts.UniswapV2.ERC20.NoCall

/-!
# UniswapV2ERC20's runtime has a 0xfa byte, so `AssembleNoCall.calleesRun_of_noFaByte` does not apply.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly

theorem runtime_not_noFaByte : noFaByte code = false := by decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.runtime_not_noFaByte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runtime_not_noFaByte

end SolidCore.Spec.UniswapV2.ERC20.NoCall
