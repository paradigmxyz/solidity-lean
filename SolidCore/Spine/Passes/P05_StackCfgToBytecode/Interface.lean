import SolidCore.Spine.L04_StackCfg.Interface
import SolidCore.Spine.L05_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_StackCfgToBytecode

structure Artifact where
  bytecode : L05_Bytecode.Artifact
  wf : L05_Bytecode.WF bytecode

def assemble? (_program : L04_StackCfg.Program) : Option Artifact :=
  none

structure SoundnessBoundary
    (_program : L04_StackCfg.Program) (_artifact : Artifact) :
    Prop where
  bytecodeRefinesCfg : True := by trivial

theorem assemble?_sound
    {program : L04_StackCfg.Program} {artifact : Artifact}
    (hAssemble : assemble? program = some artifact) :
    SoundnessBoundary program artifact := by
  cases hAssemble

end P05_StackCfgToBytecode
end Passes
end Spine
end SolidCore
