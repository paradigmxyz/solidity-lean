import Contracts.UniswapV2.ERC20.NoCall

/-!
# What UniswapV2ERC20's runtime decode holds that `callFree` refuses

A STATICCALL (`runtime_has_staticcall`) and no other message-sending instruction (`runtime_only_staticcall`:
no CALL, CALLCODE, DELEGATECALL, CREATE or CREATE2), at the counters `refusedAt_eq` lists: the
STATICCALL at 903 and RETURNDATASIZE, RETURNDATACOPY, RETURNDATASIZE at 1158, 1161, 1162. These
counters are of solar 38b5232's output (Runtime.lean's header has its digest): bytes from another
compiler fail this theorem by evaluation, not silently.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly

theorem runtime_has_staticcall : (decoded code).any (fun x => x.2 == .op 0xfa) = true := by
  decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.runtime_has_staticcall' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runtime_has_staticcall

end SolidCore.Spec.UniswapV2.ERC20.NoCall
