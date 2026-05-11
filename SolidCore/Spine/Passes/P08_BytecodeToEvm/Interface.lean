import SolidCore.Spine.L07_Bytecode.Interface
import SolidCore.Spine.L08_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P08_BytecodeToEvm

structure SoundnessBoundary (code : L07_Bytecode.Bytes) : Prop where
  bytecodeWf : L07_Bytecode.WF code
  targetModelReadOnly : True := by trivial

end P08_BytecodeToEvm
end Passes
end Spine
end SolidCore
