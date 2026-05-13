import SolidCore.Spine.L05_Bytecode.Interface
import SolidCore.Spine.L06_Evm.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_BytecodeToEvm

/--
P06 is the L05 bytecode-to-L06 external-boundary pass. It deliberately stops at
the shared `External` boundary; exact metered bytecode execution is L07.
-/
structure Artifact where
  program : L06_Evm.Program
  external : L06_Evm.ExternalWorld := SharedSemantics.External.EvmExternal.empty
  wf : L06_Evm.WF program

def embed? (bytecode : L05_Bytecode.Artifact) : Option Artifact :=
  some
    { program := L06_Evm.Program.ofBytecode bytecode
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := by exact {} } }

structure EquivalenceBoundary
    (_bytecode : L05_Bytecode.Artifact) (_artifact : Artifact) :
    Prop where
  programEmbedsBytecode :
    _artifact.program = L06_Evm.Program.ofBytecode _bytecode
  usesSharedExternal :
    _artifact.external = SharedSemantics.External.EvmExternal.empty
  preservesBehavior :
    ∀ {behavior : L01_ValidSolidity.Behavior},
    L05_Bytecode.Semantics _bytecode behavior →
      L06_Evm.SemanticsWithExternal _artifact.external _artifact.program
        (L06_Evm.Outcome.pure behavior)
  reflectsBehavior :
    ∀ {outcome : L06_Evm.Outcome},
    L06_Evm.SemanticsWithExternal _artifact.external
      _artifact.program outcome →
      L05_Bytecode.Semantics _bytecode outcome.behavior ∧
        outcome.externalTrace = []

abbrev SoundnessBoundary := EquivalenceBoundary

theorem embed?_equivalent
    {bytecode : L05_Bytecode.Artifact} {artifact : Artifact}
    (hEmbed : embed? bytecode = some artifact) :
    EquivalenceBoundary bytecode artifact := by
  simp [embed?] at hEmbed
  cases hEmbed
  exact
    { programEmbedsBytecode := rfl
      usesSharedExternal := rfl
      preservesBehavior := by
        intro behavior hSemantics
        exact L06_Evm.Program.ofBytecode_preserves_l05 hSemantics
      reflectsBehavior := by
        intro outcome hSemantics
        exact L06_Evm.Program.ofBytecode_reflects_l05 hSemantics }

theorem embed?_sound
    {bytecode : L05_Bytecode.Artifact} {artifact : Artifact}
    (hEmbed : embed? bytecode = some artifact) :
    SoundnessBoundary bytecode artifact :=
  embed?_equivalent hEmbed

theorem embed?_stop_semantics :
    ∃ artifact,
      embed? L05_Bytecode.Artifact.stop = some artifact ∧
      L06_Evm.SemanticsWithExternal artifact.external artifact.program
        (L06_Evm.Outcome.pure L01_ValidSolidity.Behavior.stopped) := by
  let artifact : Artifact :=
    { program := L06_Evm.Program.ofBytecode L05_Bytecode.Artifact.stop
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := L05_Bytecode.Artifact.stop_wf } }
  exact
    ⟨artifact, rfl,
      L06_Evm.Program.ofBytecode_stop_semantics
        L05_Bytecode.Artifact.stop_isStop⟩

theorem embed?_returnWord0_semantics :
    ∃ artifact,
      embed? L05_Bytecode.Artifact.returnWord0 = some artifact ∧
      L06_Evm.SemanticsWithExternal artifact.external artifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord 0)) := by
  let artifact : Artifact :=
    { program := L06_Evm.Program.ofBytecode
        L05_Bytecode.Artifact.returnWord0
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := L05_Bytecode.Artifact.returnWord0_wf } }
  exact
    ⟨artifact, rfl,
      L06_Evm.Program.ofBytecode_returnWord0_semantics
        L05_Bytecode.Artifact.returnWord0_isReturnWord0⟩

theorem embed?_returnByte_semantics
    (value : L05_Bytecode.Byte) (hByte : value < 256) :
    ∃ artifact,
      embed? (L05_Bytecode.Artifact.returnByte value) = some artifact ∧
      L06_Evm.SemanticsWithExternal artifact.external artifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) := by
  let artifact : Artifact :=
    { program := L06_Evm.Program.ofBytecode
        (L05_Bytecode.Artifact.returnByte value)
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := L05_Bytecode.Artifact.returnByte_wf value } }
  exact
    ⟨artifact, rfl,
      L06_Evm.Program.ofBytecode_returnByte_semantics
        (L05_Bytecode.Artifact.returnByte_isReturnByte value hByte)⟩

end P06_BytecodeToEvm
end Passes
end Spine
end SolidCore
