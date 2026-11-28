import Contracts.UniswapV2.ERC20.NoCall

/-!
# UniswapV2ERC20's runtime sends no message other than by STATICCALL
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly

theorem runtime_only_staticcall :
    (decoded code).all (fun x => !([0xf0, 0xf1, 0xf2, 0xf4, 0xf5].map SolarTV.Assembly.Instr.op).contains x.2) = true := by
  decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.runtime_only_staticcall' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runtime_only_staticcall

end SolidCore.Spec.UniswapV2.ERC20.NoCall
