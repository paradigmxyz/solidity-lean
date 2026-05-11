import SolidCore.Spine.L10_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P10_BytecodeToEvm

structure SoundnessBoundary (code : L09_Bytecode.Bytes) : Prop where
  bytecodeWf : L09_Bytecode.WF code
  targetModelReadOnly : True := by trivial

end P10_BytecodeToEvm
end Passes
end Spine
end SolidCore
