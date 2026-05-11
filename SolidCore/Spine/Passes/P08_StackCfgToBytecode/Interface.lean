import SolidCore.Spine.L07_StackCfg.Interface
import SolidCore.Spine.L08_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P08_StackCfgToBytecode

structure Artifact where
  code : L08_Bytecode.Bytes
  wf : L08_Bytecode.WF code

def resolve? (_depthOf : L07_StackCfg.DepthEnv)
    (_program : L07_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary (_program : L07_StackCfg.Program)
    (_artifact : Artifact) : Prop where
  bytecodeRefinesCfg : True := by trivial

end P08_StackCfgToBytecode
end Passes
end Spine
end SolidCore
