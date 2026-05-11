import SolidCore.Spine.L03_AbstractYul.Interface
import SolidCore.Spine.L04_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_AbstractYulToGeneratedYul

structure Artifact where
  stmt : L04_GeneratedYul.Stmt
  fuel : Nat
  wf : L04_GeneratedYul.WF stmt

def compile? (_stmt : L03_AbstractYul.Stmt) : Option Artifact :=
  none

structure SoundnessBoundary (_stmt : L03_AbstractYul.Stmt)
    (_artifact : Artifact) : Prop where
  generatedYulRefinesAbstractYul : True := by trivial

end P04_AbstractYulToGeneratedYul
end Passes
end Spine
end SolidCore
