import SolidCore.Spine.L03_Effect.Interface

namespace SolidCore
namespace Spine
namespace L04_Layout

abbrev Stmt := L03_Effect.Stmt
abbrev Result := L03_Effect.Result

structure LayoutFacts where
  localsBound : True := by trivial
  storageBound : True := by trivial

def fromEffect (stmt : L03_Effect.Stmt) : Stmt := stmt
def eval := L03_Effect.eval

theorem fromEffect_eval (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L03_Effect.Stmt) :
    eval fuel context runtime (fromEffect stmt) =
      L03_Effect.eval fuel context runtime stmt := by
  rfl

end L04_Layout
end Spine
end SolidCore
