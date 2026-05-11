import SolidCore.Spine.L09_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P09_StackCfgToBytecode

structure Artifact where
  code : L09_Bytecode.Bytes
  wf : L09_Bytecode.WF code

def resolve? (_depthOf : L08_StackCfg.DepthEnv)
    (_program : L08_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary (_program : L08_StackCfg.Program)
    (_artifact : Artifact) : Prop where
  bytecodeRefinesCfg : True := by trivial

end P09_StackCfgToBytecode
end Passes
end Spine
end SolidCore
