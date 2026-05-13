import SharedSemantics.External
import SolidCore.Spine.L05_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace L06_Evm

abbrev Word := SharedSemantics.Word
abbrev Byte := SharedSemantics.External.Byte
abbrev Bytes := SharedSemantics.External.Bytes
abbrev Pc := L05_Bytecode.Pc
abbrev CallKind := SharedSemantics.External.ExternalCallKind
abbrev CreateKind := SharedSemantics.External.ExternalCreateKind
abbrev CallRequest := SharedSemantics.External.EvmCallRequest
abbrev CreateRequest := SharedSemantics.External.EvmCreateRequest
abbrev ExternalAction := SharedSemantics.External.EvmAction
abbrev ExternalResult := SharedSemantics.External.EvmResult
abbrev ExternalTrace := SharedSemantics.External.EvmTrace
abbrev ExternalWorld := SharedSemantics.External.EvmExternal

/--
L06 is the proof-facing EVM boundary. It does not run the exact metered EVM.
Instead, it names the same shared external boundary that source-level Solidity,
Yul, CFG, and bytecode-facing statements should preserve.

The exact metered bytecode interpreter lives one layer lower, in L07.
-/
structure Program where
  bytecode : L05_Bytecode.Artifact
  deriving Repr

structure WF (program : Program) : Prop where
  bytecodeWF : L05_Bytecode.WF program.bytecode

abbrev Behavior := L05_Bytecode.Behavior

structure Outcome where
  behavior : Behavior
  externalTrace : ExternalTrace := []
  deriving Repr

def Outcome.pure (behavior : Behavior) : Outcome :=
  { behavior := behavior
    externalTrace := [] }

def Program.ofBytecode (bytecode : L05_Bytecode.Artifact) : Program :=
  { bytecode := bytecode }

def Program.stop : Program :=
  Program.ofBytecode L05_Bytecode.Artifact.stop

def Program.returnWord0 : Program :=
  Program.ofBytecode L05_Bytecode.Artifact.returnWord0

def Program.returnByte (value : Byte) : Program :=
  Program.ofBytecode (L05_Bytecode.Artifact.returnByte value)

theorem Program.stop_wf : WF Program.stop := by
  exact { bytecodeWF := L05_Bytecode.Artifact.stop_wf }

theorem Program.returnWord0_wf : WF Program.returnWord0 := by
  exact { bytecodeWF := L05_Bytecode.Artifact.returnWord0_wf }

theorem Program.returnByte_wf (value : Byte) : WF (Program.returnByte value) := by
  exact { bytecodeWF := L05_Bytecode.Artifact.returnByte_wf value }

inductive SemanticsWithExternal :
    ExternalWorld → Program → Outcome → Prop where
  | stop {external : ExternalWorld} {program : Program} :
      program.bytecode.IsStop →
      SemanticsWithExternal external program
        (Outcome.pure L01_ValidSolidity.Behavior.stopped)
  | returnWord0 {external : ExternalWorld} {program : Program} :
      program.bytecode.IsReturnWord0 →
      SemanticsWithExternal external program
        (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord 0))
  | returnByte {external : ExternalWorld} {program : Program} {value : Byte} :
      program.bytecode.IsReturnByte value →
      SemanticsWithExternal external program
        (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord value))

abbrev Semantics (program : Program) (outcome : Outcome) : Prop :=
  SemanticsWithExternal SharedSemantics.External.EvmExternal.empty
    program outcome

theorem Program.stop_semantics :
    Semantics Program.stop
      (Outcome.pure L01_ValidSolidity.Behavior.stopped) := by
  exact SemanticsWithExternal.stop L05_Bytecode.Artifact.stop_isStop

theorem Program.returnWord0_semantics :
    Semantics Program.returnWord0
      (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord 0)) := by
  exact SemanticsWithExternal.returnWord0
    L05_Bytecode.Artifact.returnWord0_isReturnWord0

theorem Program.returnByte_semantics
    (value : Byte) (hByte : value < 256) :
    Semantics (Program.returnByte value)
      (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord value)) := by
  exact SemanticsWithExternal.returnByte
    (L05_Bytecode.Artifact.returnByte_isReturnByte value hByte)

theorem Program.ofBytecode_preserves_l05
    {external : ExternalWorld} {bytecode : L05_Bytecode.Artifact}
    {behavior : Behavior}
    (hSemantics : L05_Bytecode.Semantics bytecode behavior) :
    SemanticsWithExternal external (Program.ofBytecode bytecode)
      (Outcome.pure behavior) := by
  cases hSemantics with
  | stop hStop =>
      exact SemanticsWithExternal.stop hStop
  | returnWord0 hReturn =>
      exact SemanticsWithExternal.returnWord0 hReturn
  | returnByte hReturn =>
      exact SemanticsWithExternal.returnByte hReturn

theorem Program.ofBytecode_reflects_l05
    {external : ExternalWorld} {bytecode : L05_Bytecode.Artifact}
    {outcome : Outcome}
    (hSemantics :
      SemanticsWithExternal external (Program.ofBytecode bytecode) outcome) :
    L05_Bytecode.Semantics bytecode outcome.behavior ∧
      outcome.externalTrace = [] := by
  cases hSemantics with
  | stop hStop =>
      exact ⟨L05_Bytecode.Semantics.stop hStop, rfl⟩
  | returnWord0 hReturn =>
      exact ⟨L05_Bytecode.Semantics.returnWord0 hReturn, rfl⟩
  | returnByte hReturn =>
      exact ⟨L05_Bytecode.Semantics.returnByte hReturn, rfl⟩

theorem Program.ofBytecode_stop_semantics
    {external : ExternalWorld} {bytecode : L05_Bytecode.Artifact}
    (hStop : bytecode.IsStop) :
    SemanticsWithExternal external (Program.ofBytecode bytecode)
      (Outcome.pure L01_ValidSolidity.Behavior.stopped) := by
  exact SemanticsWithExternal.stop hStop

theorem Program.ofBytecode_returnWord0_semantics
    {external : ExternalWorld} {bytecode : L05_Bytecode.Artifact}
    (hReturn : bytecode.IsReturnWord0) :
    SemanticsWithExternal external (Program.ofBytecode bytecode)
      (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord 0)) := by
  exact SemanticsWithExternal.returnWord0 hReturn

theorem Program.ofBytecode_returnByte_semantics
    {external : ExternalWorld} {bytecode : L05_Bytecode.Artifact}
    {value : Byte}
    (hReturn : bytecode.IsReturnByte value) :
    SemanticsWithExternal external (Program.ofBytecode bytecode)
      (Outcome.pure (L01_ValidSolidity.Behavior.returnedWord value)) := by
  exact SemanticsWithExternal.returnByte hReturn

end L06_Evm
end Spine
end SolidCore
