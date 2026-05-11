import SolidCore.Spine.L04_Effect.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_ControlToEffect

def compile := L04_Effect.fromControl

theorem compile_sound (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L03_Control.Stmt) :
    L04_Effect.eval fuel context runtime (compile stmt) =
      L03_Control.eval fuel context runtime stmt :=
  L04_Effect.fromControl_eval fuel context runtime stmt

end P04_ControlToEffect
end Passes
end Spine
end SolidCore
