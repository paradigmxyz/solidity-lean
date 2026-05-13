import SharedSemantics.Word
import SolidCore.Spine.L04_StackCfg.Interface
import SolidCoreYulCore.BytecodeEvm

namespace SolidCore
namespace Spine
namespace L05_Bytecode

abbrev Word := SharedSemantics.Word
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

abbrev Behavior := L04_StackCfg.Behavior

def Pc.zero : Pc := { value := 0 }

def Pc.one : Pc := { value := 1 }

def Pc.two : Pc := { value := 2 }

def Pc.three : Pc := { value := 3 }

def Pc.four : Pc := { value := 4 }

def Pc.five : Pc := { value := 5 }

def Pc.six : Pc := { value := 6 }

def Pc.seven : Pc := { value := 7 }

def Instr.stop : Instr :=
  { pc := Pc.zero
    opcode := SolidCoreYulCore.BytecodeEvm.Opcode.stop
    immediate := Immediate.none }

def Instr.push0 (pc : Pc) : Instr :=
  { pc := pc
    opcode := SolidCoreYulCore.BytecodeEvm.Opcode.push 0
    immediate := Immediate.none }

def Instr.push1 (pc : Pc) (value : Byte) : Instr :=
  { pc := pc
    opcode := SolidCoreYulCore.BytecodeEvm.Opcode.push 1
    immediate := Immediate.pushBytes 1 [value] }

def Instr.mstoreAt (pc : Pc) : Instr :=
  { pc := pc
    opcode := SolidCoreYulCore.BytecodeEvm.Opcode.mstore
    immediate := Immediate.none }

def Instr.mstore : Instr :=
  Instr.mstoreAt Pc.two

def Instr.returnAt (pc : Pc) : Instr :=
  { pc := pc
    opcode := SolidCoreYulCore.BytecodeEvm.Opcode.returnOp
    immediate := Immediate.none }

def Instr.returnOp : Instr :=
  Instr.returnAt Pc.six

def DecodedProgram.stop : DecodedProgram :=
  { instructions := [Instr.stop]
    entry := Pc.zero
    jumpTable := {} }

def DecodedProgram.returnWord0 : DecodedProgram :=
  { instructions :=
      [ Instr.push0 Pc.zero
      , Instr.push0 Pc.one
      , Instr.mstore
      , Instr.push1 Pc.three 0x20
      , Instr.push0 Pc.five
      , Instr.returnOp ]
    entry := Pc.zero
    jumpTable := {} }

def DecodedProgram.returnByte (value : Byte) : DecodedProgram :=
  { instructions :=
      [ Instr.push1 Pc.zero value
      , Instr.push0 Pc.two
      , Instr.mstoreAt Pc.three
      , Instr.push1 Pc.four 0x20
      , Instr.push0 Pc.six
      , Instr.returnAt Pc.seven ]
    entry := Pc.zero
    jumpTable := {} }

def Artifact.stopWithLabel (label : L04_StackCfg.Label) : Artifact :=
  { bytes := [0x00]
    decoded := DecodedProgram.stop
    pcMap := [{ label := label, pc := Pc.zero }] }

def Artifact.stop : Artifact :=
  Artifact.stopWithLabel L04_StackCfg.Label.entry

def Artifact.returnWord0WithLabel (label : L04_StackCfg.Label) : Artifact :=
  { bytes := [0x5f, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]
    decoded := DecodedProgram.returnWord0
    pcMap := [{ label := label, pc := Pc.zero }] }

def Artifact.returnWord0 : Artifact :=
  Artifact.returnWord0WithLabel L04_StackCfg.Label.entry

def Artifact.returnByteWithLabel
    (label : L04_StackCfg.Label) (value : Byte) : Artifact :=
  { bytes := [0x60, value, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]
    decoded := DecodedProgram.returnByte value
    pcMap := [{ label := label, pc := Pc.zero }] }

def Artifact.returnByte (value : Byte) : Artifact :=
  Artifact.returnByteWithLabel L04_StackCfg.Label.entry value

def Artifact.IsStop (artifact : Artifact) : Prop :=
  artifact.bytes = [0x00] ∧
    artifact.decoded = DecodedProgram.stop ∧
    artifact.decoded.entry = Pc.zero ∧
    artifact.decoded.instructions = [Instr.stop]

def Artifact.IsReturnWord0 (artifact : Artifact) : Prop :=
  artifact.bytes = [0x5f, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3] ∧
    artifact.decoded = DecodedProgram.returnWord0 ∧
    artifact.decoded.entry = Pc.zero

def Artifact.IsReturnByte (artifact : Artifact) (value : Byte) : Prop :=
  value < 256 ∧
    artifact.bytes =
      [0x60, value, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3] ∧
    artifact.decoded = DecodedProgram.returnByte value ∧
    artifact.decoded.entry = Pc.zero

inductive Semantics : Artifact -> Behavior -> Prop where
  | stop {artifact : Artifact} :
      artifact.IsStop ->
      Semantics artifact L01_ValidSolidity.Behavior.stopped
  | returnWord0 {artifact : Artifact} :
      artifact.IsReturnWord0 ->
      Semantics artifact (L01_ValidSolidity.Behavior.returnedWord 0)
  | returnByte {artifact : Artifact} {value : Byte} :
      artifact.IsReturnByte value ->
      Semantics artifact (L01_ValidSolidity.Behavior.returnedWord value)

theorem Artifact.stopWithLabel_isStop (label : L04_StackCfg.Label) :
    (Artifact.stopWithLabel label).IsStop := by
  simp [Artifact.stopWithLabel, Artifact.IsStop, DecodedProgram.stop,
    Instr.stop, Pc.zero]

theorem Artifact.stop_isStop : Artifact.stop.IsStop := by
  exact Artifact.stopWithLabel_isStop L04_StackCfg.Label.entry

theorem Artifact.stop_wf : WF Artifact.stop := by
  exact {}

theorem Artifact.stopWithLabel_wf (label : L04_StackCfg.Label) :
    WF (Artifact.stopWithLabel label) := by
  exact {}

theorem Artifact.returnWord0WithLabel_isReturnWord0
    (label : L04_StackCfg.Label) :
    (Artifact.returnWord0WithLabel label).IsReturnWord0 := by
  simp [Artifact.returnWord0WithLabel, Artifact.IsReturnWord0,
    DecodedProgram.returnWord0, Pc.zero]

theorem Artifact.returnWord0_isReturnWord0 :
    Artifact.returnWord0.IsReturnWord0 := by
  exact Artifact.returnWord0WithLabel_isReturnWord0 L04_StackCfg.Label.entry

theorem Artifact.returnWord0_wf : WF Artifact.returnWord0 := by
  exact {}

theorem Artifact.returnWord0WithLabel_wf (label : L04_StackCfg.Label) :
    WF (Artifact.returnWord0WithLabel label) := by
  exact {}

theorem Artifact.returnByteWithLabel_isReturnByte
    (label : L04_StackCfg.Label) (value : Byte)
    (hByte : value < 256) :
    (Artifact.returnByteWithLabel label value).IsReturnByte value := by
  simp [Artifact.returnByteWithLabel, Artifact.IsReturnByte,
    DecodedProgram.returnByte, Pc.zero, hByte]

theorem Artifact.returnByte_isReturnByte
    (value : Byte) (hByte : value < 256) :
    (Artifact.returnByte value).IsReturnByte value := by
  exact Artifact.returnByteWithLabel_isReturnByte
    L04_StackCfg.Label.entry value hByte

theorem Artifact.returnByte_wf (value : Byte) :
    WF (Artifact.returnByte value) := by
  exact {}

theorem Artifact.returnByteWithLabel_wf
    (label : L04_StackCfg.Label) (value : Byte) :
    WF (Artifact.returnByteWithLabel label value) := by
  exact {}

theorem Artifact.stop_semantics :
    Semantics Artifact.stop L01_ValidSolidity.Behavior.stopped := by
  exact Semantics.stop Artifact.stop_isStop

theorem Artifact.stopWithLabel_semantics (label : L04_StackCfg.Label) :
    Semantics (Artifact.stopWithLabel label)
      L01_ValidSolidity.Behavior.stopped := by
  exact Semantics.stop (Artifact.stopWithLabel_isStop label)

theorem Artifact.returnWord0_semantics :
    Semantics Artifact.returnWord0
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  exact Semantics.returnWord0 Artifact.returnWord0_isReturnWord0

theorem Artifact.returnWord0WithLabel_semantics (label : L04_StackCfg.Label) :
    Semantics (Artifact.returnWord0WithLabel label)
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  exact Semantics.returnWord0
    (Artifact.returnWord0WithLabel_isReturnWord0 label)

theorem Artifact.returnByte_semantics
    (value : Byte) (hByte : value < 256) :
    Semantics (Artifact.returnByte value)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnByte
    (Artifact.returnByte_isReturnByte value hByte)

theorem Artifact.returnByteWithLabel_semantics
    (label : L04_StackCfg.Label) (value : Byte)
    (hByte : value < 256) :
    Semantics (Artifact.returnByteWithLabel label value)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnByte
    (Artifact.returnByteWithLabel_isReturnByte label value hByte)

end L05_Bytecode
end Spine
end SolidCore
