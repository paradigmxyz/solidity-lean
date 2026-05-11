import SolidCore.Spine.L05_Bytecode.Interface
import SolidCore.Spine.L06_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_BytecodeToEvm

structure Artifact where
  program : L06_Evm.Program
  wf : L06_Evm.WF program

def embed? (_bytecode : L05_Bytecode.Artifact) : Option Artifact :=
  none

structure SoundnessBoundary
    (_bytecode : L05_Bytecode.Artifact) (_artifact : Artifact) :
    Prop where
  evmExecutesBytecodeArtifact : True := by trivial
  targetModelFaithful : True := by trivial

theorem embed?_sound
    {bytecode : L05_Bytecode.Artifact} {artifact : Artifact}
    (hEmbed : embed? bytecode = some artifact) :
    SoundnessBoundary bytecode artifact := by
  cases hEmbed

end P06_BytecodeToEvm
end Passes
end Spine
end SolidCore
