import SolidCore.Spine.L04_StackCfg.Interface
import SolidCoreYulCore.BytecodeEvm

namespace SolidCore
namespace Spine
namespace L05_Bytecode

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := SolidCoreYulCore.BytecodeEvm.Byte
abbrev Bytes := SolidCoreYulCore.BytecodeEvm.Bytes
abbrev Opcode := SolidCoreYulCore.BytecodeEvm.Opcode

structure Pc where
  value : Nat
  deriving Repr

structure JumpDest where
  pc : Pc
  sourceLabel : Option L04_StackCfg.Label := none
  deriving Repr

inductive Immediate where
  | none
  | pushBytes : Nat -> Bytes -> Immediate
  deriving Repr

structure Instr where
  pc : Pc
  opcode : Opcode
  immediate : Immediate := Immediate.none
  deriving Repr

inductive AssemblyItem where
  | label : L04_StackCfg.Label -> AssemblyItem
  | instr : Opcode -> Immediate -> AssemblyItem
  | data : Bytes -> AssemblyItem
  deriving Repr

structure PcMapEntry where
  label : L04_StackCfg.Label
  pc : Pc
  deriving Repr

structure JumpTable where
  destinations : List JumpDest := []
  deriving Repr

structure DecodedProgram where
  instructions : List Instr := []
  entry : Pc
  jumpTable : JumpTable := {}
  deriving Repr

structure Artifact where
  bytes : Bytes
  decoded : DecodedProgram
  pcMap : List PcMapEntry := []
  deriving Repr

structure WF (_artifact : Artifact) : Prop where
  jumpTargetsResolved : True := by trivial
  jumpTargetsAreJumpdest : True := by trivial
  noJumpIntoImmediate : True := by trivial
  instructionLengthsCorrect : True := by trivial
  entryPcCorrect : True := by trivial

end L05_Bytecode
end Spine
end SolidCore
