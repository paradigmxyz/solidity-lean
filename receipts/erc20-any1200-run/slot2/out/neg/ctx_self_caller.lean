import erc20_any.Final
open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Verify.Generic Certified.erc20_any.Final
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot)
set_option maxRecDepth 100000

example : Expected src { specAny with Contexts := fun ctx => ctx.caller < 2 ^ 160 } runtimeBytes := Certified.erc20_any.Proof.any
