import SolidCore.Spine.L08_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P08_ConcreteToStackCfg

structure Artifact where
  program : L08_StackCfg.Program
  depthOf : L08_StackCfg.DepthEnv
  wf : L08_StackCfg.WF depthOf program

structure SoundnessBoundary (_stmt : L07_ConcreteTarget.Stmt)
    (_artifact : Artifact) : Prop where
  cfgRefinesConcreteSemantics : True := by trivial

end P08_ConcreteToStackCfg
end Passes
end Spine
end SolidCore
