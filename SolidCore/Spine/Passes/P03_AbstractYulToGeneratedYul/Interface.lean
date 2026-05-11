import SolidCore.Spine.L02_AbstractYul.Interface
import SolidCore.Spine.L03_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P03_AbstractYulToGeneratedYul

structure Artifact where
  stmt : L03_GeneratedYul.Stmt
  fuel : Nat
  wf : L03_GeneratedYul.WF stmt

def compile? (_stmt : L02_AbstractYul.Stmt) : Option Artifact :=
  none

structure SoundnessBoundary (_stmt : L02_AbstractYul.Stmt)
    (_artifact : Artifact) : Prop where
  generatedYulRefinesAbstractYul : True := by trivial

end P03_AbstractYulToGeneratedYul
end Passes
end Spine
end SolidCore
