import SolidCore.Spine.L04_StackCfg.Interface
import SolidCore.Spine.L05_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_StackCfgToBytecode

structure Artifact where
  code : L05_Bytecode.Bytes
  wf : L05_Bytecode.WF code

def resolve? (_depthOf : L04_StackCfg.DepthEnv)
    (_program : L04_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary (_program : L04_StackCfg.Program)
    (_artifact : Artifact) : Prop where
  bytecodeRefinesCfg : True := by trivial

end P05_StackCfgToBytecode
end Passes
end Spine
end SolidCore
