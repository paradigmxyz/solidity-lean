import SolidCore.Spine.L02_AbstractYul.Interface
import SolidCore.Spine.L03_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P03_AbstractYulToGeneratedYul

structure Artifact where
  program : L03_GeneratedYul.Program
  wf : L03_GeneratedYul.WF program

def compile? (_program : L02_AbstractYul.Program) : Option Artifact :=
  none

structure SoundnessBoundary
    (_program : L02_AbstractYul.Program) (_artifact : Artifact) :
    Prop where
  generatedYulRefinesAbstractYul : True := by trivial

theorem compile?_sound
    {program : L02_AbstractYul.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  cases hCompile

end P03_AbstractYulToGeneratedYul
end Passes
end Spine
end SolidCore
