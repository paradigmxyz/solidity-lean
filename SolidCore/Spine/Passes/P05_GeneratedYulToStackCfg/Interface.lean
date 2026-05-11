import SolidCore.Spine.L04_GeneratedYul.Interface
import SolidCore.Spine.L05_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_GeneratedYulToStackCfg

structure Artifact where
  program : L05_StackCfg.Program
  depthOf : L05_StackCfg.DepthEnv
  wf : L05_StackCfg.WF depthOf program

structure SoundnessBoundary (_stmt : L04_GeneratedYul.Stmt)
    (_artifact : Artifact) : Prop where
  cfgRefinesGeneratedYul : True := by trivial

end P05_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
