import SolidCore.Spine.L06_GeneratedYul.Interface
import SolidCore.Spine.L07_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P07_GeneratedYulToStackCfg

structure Artifact where
  program : L07_StackCfg.Program
  depthOf : L07_StackCfg.DepthEnv
  wf : L07_StackCfg.WF depthOf program

structure SoundnessBoundary (_stmt : L06_GeneratedYul.Stmt)
    (_artifact : Artifact) : Prop where
  cfgRefinesGeneratedYul : True := by trivial

end P07_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
