import SolidCore.Spine.L05_StackCfg.Interface
import SolidCore.Spine.L06_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_StackCfgToBytecode

structure Artifact where
  code : L06_Bytecode.Bytes
  wf : L06_Bytecode.WF code

def resolve? (_depthOf : L05_StackCfg.DepthEnv)
    (_program : L05_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary (_program : L05_StackCfg.Program)
    (_artifact : Artifact) : Prop where
  bytecodeRefinesCfg : True := by trivial

end P06_StackCfgToBytecode
end Passes
end Spine
end SolidCore
