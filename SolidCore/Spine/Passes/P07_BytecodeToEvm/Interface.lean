import SolidCore.Spine.L06_Bytecode.Interface
import SolidCore.Spine.L07_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P07_BytecodeToEvm

structure SoundnessBoundary (code : L06_Bytecode.Bytes) : Prop where
  bytecodeWf : L06_Bytecode.WF code
  targetModelReadOnly : True := by trivial

end P07_BytecodeToEvm
end Passes
end Spine
end SolidCore
