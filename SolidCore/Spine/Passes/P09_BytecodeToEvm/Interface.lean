import SolidCore.Spine.L08_Bytecode.Interface
import SolidCore.Spine.L09_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P09_BytecodeToEvm

structure SoundnessBoundary (code : L08_Bytecode.Bytes) : Prop where
  bytecodeWf : L08_Bytecode.WF code
  targetModelReadOnly : True := by trivial

end P09_BytecodeToEvm
end Passes
end Spine
end SolidCore
