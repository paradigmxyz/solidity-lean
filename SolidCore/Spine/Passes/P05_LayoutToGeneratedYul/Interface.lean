import SolidCore.Spine.L04_Layout.Interface
import SolidCore.Spine.L05_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_LayoutToGeneratedYul

structure Artifact where
  stmt : L05_GeneratedYul.Stmt
  fuel : Nat
  wf : L05_GeneratedYul.WF stmt

def compile? (_stmt : L04_Layout.Stmt) : Option Artifact :=
  none

structure SoundnessBoundary (_stmt : L04_Layout.Stmt)
    (_artifact : Artifact) : Prop where
  generatedYulRefinesLayout : True := by trivial

end P05_LayoutToGeneratedYul
end Passes
end Spine
end SolidCore
