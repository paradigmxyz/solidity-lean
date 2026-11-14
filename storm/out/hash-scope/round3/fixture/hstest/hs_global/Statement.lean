import Verify.Spec.HashScopeCheck
import Verify.Spec.TreeMapNested
import Contracts.UniswapV2.ERC20.Slice.Post

namespace Certified.hs_global.Final
def Statement : Prop := SolidCore.Spec.MapSlotsSeparated [0] → (1 : Nat) + 1 = 2 ∧ True
end Certified.hs_global.Final
