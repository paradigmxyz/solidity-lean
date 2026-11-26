import erc20_any.Final
open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Verify.Generic Certified.erc20_any.Final
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot)
set_option maxRecDepth 100000

example : SolidCore.Spec.UniswapV2.ERC20.Certified.code.data.toList.map (·.toNat) = runtimeBytes.dropLast ++ [runtimeBytes.getLast! ^^^ 1] := by decide +kernel
