import SolidCore.Spine.L05_Bytecode.Interface
import SolidCore.Spine.L06_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_BytecodeToEvm

structure SoundnessBoundary (code : L05_Bytecode.Bytes) : Prop where
  bytecodeWf : L05_Bytecode.WF code
  targetModelReadOnly : True := by trivial

end P06_BytecodeToEvm
end Passes
end Spine
end SolidCore
