import Contracts.UniswapV2.ERC20.Certified.Transfer
open SolidCore.Spec.UniswapV2.ERC20 in
#check @Certified.certified
#print SolidCore.Spec.UniswapV2.ERC20.Slice.ValidIn
#print SolidCore.Spec.UniswapV2.ERC20.Slice.Scope
#print SolidCore.Spec.ScopedSep
#check @SolidCore.Spec.UniswapV2.ERC20.Certified.self_max_bytes
#check @SolidCore.Spec.UniswapV2.ERC20.Certified.self_short_bytes
#print axioms SolidCore.Spec.UniswapV2.ERC20.Certified.certified
#print axioms SolidCore.Spec.UniswapV2.ERC20.Certified.self_max_bytes
#print axioms SolidCore.Spec.UniswapV2.ERC20.Certified.self_short_bytes
#print axioms SolidCore.Spec.UniswapV2.ERC20.Certified.compiled
