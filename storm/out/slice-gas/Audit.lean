import uv2_erc20.Gas
import Verify.ShapeCtxGasFrom
open SolarTV.Export.UniswapV2ERC20.CtxGas
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.gas_edge
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.resources
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.resources_at
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.G_eq
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.check_ok
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.guard_run
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.guard_ends
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.rejects_jump
#print axioms SolarTV.Export.UniswapV2ERC20.CtxGas.rejects_sstore
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXLFrom
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXL
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXL
#print axioms SolidCore.Refinement.Shapes.gasEdge_ofXL
#print axioms SolidCore.Refinement.Shapes.resourcesFrom_ofXL
#print axioms SolidCore.Refinement.Shapes.ResourcesFrom.resources
#print axioms SolidCore.Refinement.Shapes.compiled0XL
#print axioms SolidCore.Refinement.Final.Target.runWithFrom_callerAddress
#check @SolarTV.Export.UniswapV2ERC20.CtxGas.gas_edge
#check @SolarTV.Export.UniswapV2ERC20.CtxGas.resources
#print SolidCore.Refinement.Shapes.ResourcesFrom
