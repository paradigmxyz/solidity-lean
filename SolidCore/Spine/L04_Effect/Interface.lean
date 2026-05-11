import SolidCore.Spine.L03_Control.Interface

namespace SolidCore
namespace Spine
namespace L04_Effect

abbrev Stmt := L03_Control.Stmt
abbrev Result := L03_Control.Result

def fromControl (stmt : L03_Control.Stmt) : Stmt := stmt
def eval := L03_Control.eval

theorem fromControl_eval (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L03_Control.Stmt) :
    eval fuel context runtime (fromControl stmt) =
      L03_Control.eval fuel context runtime stmt := by
  rfl

end L04_Effect
end Spine
end SolidCore
