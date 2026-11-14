import Verify.Spec.HashScopeCheck
import Verify.Spec.TreeMapNested
import Contracts.UniswapV2.ERC20.Slice.Post

namespace Certified.hs_scoped.Final
open SolidCore.Spec.UniswapV2.ERC20.Slice
/-- A published-statement-shaped Prop over the slice's per-call premise. -/
def Statement : Prop := ∀ call, Scope call ∧ True ↔ Scope call
end Certified.hs_scoped.Final
