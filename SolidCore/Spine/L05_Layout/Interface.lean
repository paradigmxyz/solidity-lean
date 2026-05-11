import SolidCore.Spine.L04_Effect.Interface

namespace SolidCore
namespace Spine
namespace L05_Layout

abbrev Stmt := L04_Effect.Stmt
abbrev Result := L04_Effect.Result

structure LayoutFacts where
  localsBound : True := by trivial
  storageBound : True := by trivial

def fromEffect (stmt : L04_Effect.Stmt) : Stmt := stmt
def eval := L04_Effect.eval

theorem fromEffect_eval (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L04_Effect.Stmt) :
    eval fuel context runtime (fromEffect stmt) =
      L04_Effect.eval fuel context runtime stmt := by
  rfl

end L05_Layout
end Spine
end SolidCore
