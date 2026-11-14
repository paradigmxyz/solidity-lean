import Verify.Spec.HashScopeCheck
import Verify.Spec.TreeMapNested
import Contracts.UniswapV2.ERC20.Slice.Post

namespace Certified.hs_refuted.Final
def Statement : Prop := SolidCore.Spec.NestedSlotsSeparated [1, 4] [2] → (1 : Nat) + 1 = 2 ∧ True
end Certified.hs_refuted.Final
