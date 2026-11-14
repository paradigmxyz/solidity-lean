import Contracts.UniswapV2.ERC20.NoCall

/-!
# Where UniswapV2ERC20's runtime fails the call-free check

`refusedAt_eq`: the counters of the instructions `callFree` refuses, the STATICCALL at 903 (permit's call
to ECRECOVER) and RETURNDATASIZE, RETURNDATACOPY, RETURNDATASIZE at 1158, 1161, 1162. They are of
solar 38b5232's output (Runtime.lean's header has its digest): bytes from another compiler fail this
theorem by evaluation, not silently.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

/-- The counters of the refused instructions. -/
theorem refusedAt_eq : refusedAt code = [903, 1158, 1161, 1162] := by decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.refusedAt_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms refusedAt_eq

end SolidCore.Spec.UniswapV2.ERC20.NoCall
