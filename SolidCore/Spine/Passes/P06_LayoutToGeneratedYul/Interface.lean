import SolidCore.Spine.L05_Layout.Interface
import SolidCore.Spine.L06_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_LayoutToGeneratedYul

structure Artifact where
  stmt : L06_GeneratedYul.Stmt
  fuel : Nat
  wf : L06_GeneratedYul.WF stmt

def compile? (_stmt : L05_Layout.Stmt) : Option Artifact :=
  none

structure SoundnessBoundary (_stmt : L05_Layout.Stmt)
    (_artifact : Artifact) : Prop where
  generatedYulRefinesLayout : True := by trivial

end P06_LayoutToGeneratedYul
end Passes
end Spine
end SolidCore
