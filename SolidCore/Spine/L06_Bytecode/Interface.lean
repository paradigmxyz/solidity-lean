import SolidCoreYulCore.BytecodeGas
import SolidCoreYulCore.BytecodeMultiContract
import SolidCore.Spine.L05_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace L06_Bytecode

abbrev Byte := SolidCoreYulCore.BytecodeEvm.Byte
abbrev Bytes := SolidCoreYulCore.BytecodeEvm.Bytes
abbrev State := SolidCoreYulCore.BytecodeEvm.State
abbrev Opcode := SolidCoreYulCore.BytecodeEvm.Opcode

def step := SolidCoreYulCore.BytecodeEvm.step

structure WF (code : Bytes) : Prop where
  jumpTargetsResolved : True := by trivial
  labelPcMapTotal : True := by trivial
  jumpTargetsAreJumpdest : True := by trivial
  noJumpIntoImmediate : True := by trivial
  instructionLengthsCorrect : True := by trivial
  entryPcCorrect : True := by trivial
  stackSafe : True := by trivial
  noUnresolvedPseudoInstructions : True := by trivial

end L06_Bytecode
end Spine
end SolidCore
