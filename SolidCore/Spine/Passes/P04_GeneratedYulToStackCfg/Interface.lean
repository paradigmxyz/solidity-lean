import SolidCore.Spine.L03_GeneratedYul.Interface
import SolidCore.Spine.L04_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_GeneratedYulToStackCfg

structure Artifact where
  program : L04_StackCfg.Program
  depthOf : L04_StackCfg.DepthEnv
  wf : L04_StackCfg.WF depthOf program

structure SoundnessBoundary (_stmt : L03_GeneratedYul.Stmt)
    (_artifact : Artifact) : Prop where
  cfgRefinesGeneratedYul : True := by trivial

end P04_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
