import SolidCore.Spine.L03_Effect.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P03_ControlToEffect

def compile := L03_Effect.fromControl

theorem compile_sound (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L02_Control.Stmt) :
    L03_Effect.eval fuel context runtime (compile stmt) =
      L02_Control.eval fuel context runtime stmt :=
  L03_Effect.fromControl_eval fuel context runtime stmt

end P03_ControlToEffect
end Passes
end Spine
end SolidCore
