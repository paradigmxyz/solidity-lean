import SolidCore.Spine.L03_GeneratedYul.Interface
import SolidCore.Spine.L04_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_GeneratedYulToStackCfg

structure Artifact where
  program : L04_StackCfg.Program
  wf : L04_StackCfg.WF program

def compile? (_program : L03_GeneratedYul.Program) : Option Artifact :=
  none

structure SoundnessBoundary
    (_program : L03_GeneratedYul.Program) (_artifact : Artifact) :
    Prop where
  cfgRefinesGeneratedYul : True := by trivial

theorem compile?_sound
    {program : L03_GeneratedYul.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  cases hCompile

end P04_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
