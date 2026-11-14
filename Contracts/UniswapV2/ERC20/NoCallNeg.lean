import Contracts.UniswapV2.ERC20.NoCallControl

/-!
# Negative control of the scrubbed bytes

Scrubbing the three return-data reads but leaving permit's STATICCALL at 903 fails the call-free
check: the STATICCALL alone is enough for the refusal.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall

theorem staticcall_kept_not_callFree : callFree (scrubWith [1158, 1161, 1162] code) = false := by
  decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.staticcall_kept_not_callFree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_kept_not_callFree

end SolidCore.Spec.UniswapV2.ERC20.NoCall
