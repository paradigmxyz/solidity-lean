import SolidCore.Spine.L05_Layout.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_EffectToLayout

def compile := L05_Layout.fromEffect

theorem compile_sound (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) (stmt : L04_Effect.Stmt) :
    L05_Layout.eval fuel context runtime (compile stmt) =
      L04_Effect.eval fuel context runtime stmt :=
  L05_Layout.fromEffect_eval fuel context runtime stmt

end P05_EffectToLayout
end Passes
end Spine
end SolidCore
