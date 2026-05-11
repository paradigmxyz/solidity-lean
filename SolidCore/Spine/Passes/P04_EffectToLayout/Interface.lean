import SolidCore.Spine.L04_Layout.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_EffectToLayout

def compile := L04_Layout.fromEffect

theorem compile_sound (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L03_Effect.Stmt) :
    L04_Layout.eval fuel context runtime (compile stmt) =
      L03_Effect.eval fuel context runtime stmt :=
  L04_Layout.fromEffect_eval fuel context runtime stmt

end P04_EffectToLayout
end Passes
end Spine
end SolidCore
