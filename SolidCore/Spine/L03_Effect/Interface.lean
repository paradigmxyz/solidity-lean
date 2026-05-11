import SolidCore.Spine.L02_Control.Interface

namespace SolidCore
namespace Spine
namespace L03_Effect

abbrev Stmt := L02_Control.Stmt
abbrev Result := L02_Control.Result

def fromControl (stmt : L02_Control.Stmt) : Stmt := stmt
def eval := L02_Control.eval

theorem fromControl_eval (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L02_Control.Stmt) :
    eval fuel context runtime (fromControl stmt) =
      L02_Control.eval fuel context runtime stmt := by
  rfl

end L03_Effect
end Spine
end SolidCore
