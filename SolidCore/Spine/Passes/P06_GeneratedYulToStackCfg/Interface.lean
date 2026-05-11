import SolidCore.Spine.L05_GeneratedYul.Interface
import SolidCore.Spine.L06_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_GeneratedYulToStackCfg

structure Artifact where
  program : L06_StackCfg.Program
  depthOf : L06_StackCfg.DepthEnv
  wf : L06_StackCfg.WF depthOf program

structure SoundnessBoundary (_stmt : L05_GeneratedYul.Stmt)
    (_artifact : Artifact) : Prop where
  cfgRefinesGeneratedYul : True := by trivial

end P06_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
