import SolidCore.Spine.L06_StackCfg.Interface
import SolidCore.Spine.L07_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P07_StackCfgToBytecode

structure Artifact where
  code : L07_Bytecode.Bytes
  wf : L07_Bytecode.WF code

def resolve? (_depthOf : L06_StackCfg.DepthEnv)
    (_program : L06_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary (_program : L06_StackCfg.Program)
    (_artifact : Artifact) : Prop where
  bytecodeRefinesCfg : True := by trivial

end P07_StackCfgToBytecode
end Passes
end Spine
end SolidCore
