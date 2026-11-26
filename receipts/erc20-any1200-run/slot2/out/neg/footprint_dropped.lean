import erc20_any.Final
open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Verify.Generic Certified.erc20_any.Final
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot)
set_option maxRecDepth 100000

example : Expected src { specScoped with Valid := fun _ call => Valid deployed call } runtimeBytes := Certified.erc20_any.Proof.scopedExpected
