import Contracts.UniswapV2.Specs.Pair
import Contracts.UniswapV2.Specs.Factory

/-!
# Uniswap V2 specifications: the constants and the models on concrete calls

Checks, by evaluation, that the selectors and topics the statements compute from signatures are the
ones the deployed contracts use, and that the sequential models give the expected result on a few
concrete calls (none of this proves anything about SolidCore's or the bytecode's runs).
-/

namespace SolidCore.Spec.UniswapV2.Specs.Examples

open SolidCore.Spec.UniswapV2.Specs ERC20 Pair

/-! ## Selectors and topics -/

#guard selectorOf "transfer(address,uint256)" == 0xa9059cbb
#guard selectorOf "balanceOf(address)" == 0x70a08231
#guard selectorOf "swap(uint256,uint256,address,bytes)" == 0x022c0d9f
#guard selectorOf "skim(address)" == 0xbc25cf77
#guard selectorOf "sync()" == 0xfff6cae9
#guard transferTopic == 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
#guard approvalTopic == 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925
#guard permitTypehash == 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9
#guard selectorOf "feeTo()" == 0x017e7e58
#guard selectorOf "uniswapV2Call(address,uint256,uint256,bytes)" == 0x10d1e85c
#guard selectorOf "initialize(address,address)" == 0x485cc955
#guard syncTopic == 0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1
#guard mintTopic == 0x4c209b5fc8ad50758f13e2e1088ba56a560dff690a1c6fef26394f4c03821c4f
#guard burnTopic == 0xdccd412f0b1252819cb1fd330b93224ca42612892bb3f4f789976e6d81936496
#guard swapTopic == 0xd78ad95fa46c994b6551d0da85fc275fe613ce37657fb8d5e3d130840159d822
#guard Factory.pairCreatedTopic == 0x0d3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9

/-! ## Concrete calls -/

/-- A frame: caller 0x2000, pair at 0x1000, no value. -/
def env : Env := ⟨0x2000, 0x1000, 1000, 1, 0⟩

/-- A world answering the `i`-th request with `as[i]` (anything else fails). -/
def worldOf (as : List Ans) : World := ⟨fun i _ => as.getD i ⟨false, []⟩, fun _ => true, fun _ _ _ _ => 0⟩

/-- A word answer. -/
def wordAns (w : Nat) : Ans := ⟨true, be32 w⟩

/-- A pair with factory 0xF, tokens 0xA and 0xB, reserves `(r0, r1)`, total supply `t`, unlocked. -/
def pairSt (r0 r1 t : Nat) : Store := fun k =>
  if k = unlockedSlot then 1 else if k = factorySlot then 0xF else if k = token0Slot then 0xA
  else if k = token1Slot then 0xB else if k = reservesSlot then packReserves r0 r1 0
  else if k = totalSupplySlot then t else 0

/-! First mint: balances 4000 and 9000, fee off: `√36000000 − 1000 = 5000`. -/
#guard let r := mintResult env (worldOf [wordAns 4000, wordAns 9000, wordAns 0]) (pairSt 0 0 0) 0xC
  r.success && r.output == be32 5000 && r.logs.length == 4

/-! A locked pair reverts with `UniswapV2: LOCKED`. -/
#guard let r := mintResult env (worldOf []) (fun k => if k = unlockedSlot then 0 else 0) 0xC
  !r.success && r.output == err "UniswapV2: LOCKED"

/-! Swap 100 of token1 out of reserves (1000, 1000), paying 100 of token0 in: the fee-adjusted
product falls below `1000² · r0 r1`, so `UniswapV2: K`. -/
#guard let r := swapResult env (worldOf [⟨true, []⟩, wordAns 1100, wordAns 900]) (pairSt 1000 1000 1000) 0 100 0xC []
  !r.success && r.output == err "UniswapV2: K"

/-! The same swap paying 112 in passes the K check and syncs the reserves to (1112, 900). -/
#guard let r := swapResult env (worldOf [⟨true, []⟩, wordAns 1112, wordAns 900]) (pairSt 1000 1000 1000) 0 100 0xC []
  r.success && r.storage reservesSlot == packReserves 1112 900 1000 && r.calls.length == 3

/-! Swapping to token0 itself reverts with `UniswapV2: INVALID_TO`. -/
#guard let r := swapResult env (worldOf []) (pairSt 1000 1000 1000) 0 100 0xA []
  !r.success && r.output == err "UniswapV2: INVALID_TO"

/-! Burn with no LP tokens held by the pair: both amounts are 0, so
`UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED`. -/
#guard let r := burnResult env (worldOf [wordAns 1000, wordAns 1000, wordAns 0]) (pairSt 1000 1000 1000) 0xC
  !r.success && r.output == err "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED"

/-! setFeeTo from someone other than `feeToSetter` is `FORBIDDEN`. -/
#guard let r := Factory.setFeeToResult env (fun k => if k = Factory.feeToSetterSlot then 0x3000 else 0) 0x4000
  !r.success && r.output == err "UniswapV2: FORBIDDEN"

end SolidCore.Spec.UniswapV2.Specs.Examples
