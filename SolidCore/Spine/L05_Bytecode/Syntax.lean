import SolidCore.Spine.L04_StackCfg.Syntax
import SolidCoreYulCore.BytecodeEvm

namespace SolidCore
namespace Spine
namespace L05_Bytecode
namespace Syntax

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := SolidCoreYulCore.BytecodeEvm.Byte
abbrev Bytes := SolidCoreYulCore.BytecodeEvm.Bytes
abbrev Opcode := SolidCoreYulCore.BytecodeEvm.Opcode

structure Pc where
  value : Nat
  deriving Repr

structure JumpDest where
  pc : Pc
  sourceLabel : Option L04_StackCfg.Syntax.Label := none
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
  | label : L04_StackCfg.Syntax.Label -> AssemblyItem
  | instr : Opcode -> Immediate -> AssemblyItem
  | data : Bytes -> AssemblyItem
  deriving Repr

structure PcMapEntry where
  label : L04_StackCfg.Syntax.Label
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

end Syntax
end L05_Bytecode
end Spine
end SolidCore
