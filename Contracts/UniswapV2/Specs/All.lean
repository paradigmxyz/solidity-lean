import Contracts.UniswapV2.Specs.ERC20
import Contracts.UniswapV2.Specs.Pair
import Contracts.UniswapV2.Specs.Factory
import Contracts.UniswapV2.Specs.Examples

/-!
# Uniswap V2 port: every function specification

The statements of docs/specs/UNISWAPV2_SPECS.md, collected. Statements only: nothing here is
proved, and no edge of docs/CERTIFICATION_TARGET.md is claimed by them.
-/

namespace SolidCore.Spec.UniswapV2.Specs

/-- Every statement of the review list, as one conjunction (unproved). -/
def AllSpecs : Prop :=
  ERC20.TransferSpec ∧ ERC20.ApproveSpec ∧ ERC20.TransferFromSpec ∧ ERC20.PermitSpec ∧
  Pair.InitializeSpec ∧ Pair.GetReservesSpec ∧ Pair.SyncSpec ∧ Pair.SkimSpec ∧ Pair.MintSpec ∧
  Pair.BurnSpec ∧ Pair.SwapSpec ∧
  Factory.CreatePairSpec ∧ Factory.SetFeeToSpec ∧ Factory.SetFeeToSetterSpec

end SolidCore.Spec.UniswapV2.Specs
