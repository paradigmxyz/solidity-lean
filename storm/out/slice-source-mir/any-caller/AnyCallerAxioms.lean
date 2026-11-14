import Contracts.UniswapV2.ERC20.SourceMirFrom
import Contracts.UniswapV2.ERC20.SourceMirFromNeg
import Contracts.UniswapV2.ERC20.SourceMirPinned
import Contracts.UniswapV2.ERC20.SourceMir
#print axioms SolidCore.Refinement.Generic.stageFrom
#print axioms SolidCore.Refinement.Generic.stageDeployedFrom
#print axioms SolidCore.Refinement.Generic.source_run_from
#print axioms SolidCore.Refinement.solidCoreFrom_callerAddress
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.checkFrom_eq
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.checkFrom_ok
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.transfer_stage_from
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.fromOk_inhabited
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.transfer_source_mir_any_caller
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom.transfer_stage_callerAddress
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFromNeg.refuses_PinnedCaller
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirFromNeg.refuses_NoDebit
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMirPinned.pinned_fixed_accepts
#print axioms SolidCore.Spec.UniswapV2.ERC20.SourceMir.transfer_source_mir
