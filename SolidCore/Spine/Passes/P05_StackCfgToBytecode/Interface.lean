import SolidCore.Spine.L04_StackCfg.Interface
import SolidCore.Spine.L05_Bytecode.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_StackCfgToBytecode

structure Artifact where
  bytecode : L05_Bytecode.Artifact
  wf : L05_Bytecode.WF bytecode

def returnWordValue? : L04_StackCfg.Program -> Option L04_StackCfg.Word
  | { entry := entry
      blocks :=
        [ { label := label
            signature := signature
            body := [L04_StackCfg.Instr.push (L04_StackCfg.Atom.word value)]
            term := term } ]
      functions := [] } =>
      if entry = L04_StackCfg.Label.entry then
        if label = L04_StackCfg.Label.entry then
          if signature = L04_StackCfg.StackSignature.returningWith 1 then
            if term = L04_StackCfg.Term.returnOp then
              some value
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

theorem returnWordValue?_eq_some
    {program : L04_StackCfg.Program} {value : L04_StackCfg.Word}
    (hReturn : returnWordValue? program = some value) :
    program = L04_StackCfg.Program.returnWord value := by
  cases program with
  | mk entry blocks functions =>
      cases blocks with
      | nil =>
          simp [returnWordValue?] at hReturn
      | cons block rest =>
          cases rest with
          | cons _ _ =>
              simp [returnWordValue?] at hReturn
          | nil =>
              cases functions with
              | cons _ _ =>
                  simp [returnWordValue?] at hReturn
              | nil =>
                  cases block with
                  | mk label signature body term =>
                      cases body with
                      | nil =>
                          simp [returnWordValue?] at hReturn
                      | cons instr tail =>
                          cases tail with
                          | cons second rest =>
                              simp [returnWordValue?] at hReturn
                          | nil =>
                              cases instr with
                              | push atom =>
                                  cases atom with
                                  | word found =>
                                      simp [returnWordValue?] at hReturn
                                      rcases hReturn with
                                        ⟨hEntry, hLabel, hSignature, hTerm,
                                          hFound⟩
                                      cases hFound
                                      subst entry
                                      subst label
                                      subst signature
                                      subst term
                                      rfl
                                  | label label =>
                                      simp [returnWordValue?] at hReturn
                                  | function function =>
                                      simp [returnWordValue?] at hReturn
                              | dup index =>
                                  simp [returnWordValue?] at hReturn
                              | swap index =>
                                  simp [returnWordValue?] at hReturn
                              | pop =>
                                  simp [returnWordValue?] at hReturn
                              | op op =>
                                  simp [returnWordValue?] at hReturn
                              | env op =>
                                  simp [returnWordValue?] at hReturn
                              | pseudo instr =>
                                  simp [returnWordValue?] at hReturn

def returnCode? : L04_StackCfg.Program -> Option (List L04_StackCfg.Instr)
  | { entry := entry
      blocks :=
        [ { label := label
            signature := signature
            body := code
            term := term } ]
      functions := [] } =>
      if entry = L04_StackCfg.Label.entry then
        if label = L04_StackCfg.Label.entry then
          if signature = L04_StackCfg.StackSignature.returningWith code.length then
            if term = L04_StackCfg.Term.returnOp then
              some code
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

theorem returnCode?_eq_some
    {program : L04_StackCfg.Program} {code : List L04_StackCfg.Instr}
    (hReturn : returnCode? program = some code) :
    program = L04_StackCfg.Program.returnCode code := by
  cases program with
  | mk entry blocks functions =>
      cases blocks with
      | nil =>
          simp [returnCode?] at hReturn
      | cons block rest =>
          cases rest with
          | cons _ _ =>
              simp [returnCode?] at hReturn
          | nil =>
              cases functions with
              | cons _ _ =>
                  simp [returnCode?] at hReturn
              | nil =>
                  cases block with
                  | mk label signature body term =>
                      simp [returnCode?] at hReturn
                      rcases hReturn with
                        ⟨hEntry, hLabel, hSignature, hTerm, hBody⟩
                      cases hBody
                      subst entry
                      subst label
                      subst signature
                      subst term
                      rfl

def returnCodeValue? (program : L04_StackCfg.Program) :
    Option L04_StackCfg.Word := do
  let code ← returnCode? program
  match L04_StackCfg.execInstrs [] code with
  | some (value :: _) => some value
  | _ => none

theorem returnCodeValue?_eq_some
    {program : L04_StackCfg.Program} {value : L04_StackCfg.Word}
    (hReturn : returnCodeValue? program = some value) :
    ∃ code stack,
      program = L04_StackCfg.Program.returnCode code ∧
        L04_StackCfg.execInstrs [] code = some (value :: stack) := by
  unfold returnCodeValue? at hReturn
  cases hCode : returnCode? program with
  | none =>
      simp [hCode] at hReturn
  | some code =>
      simp [hCode] at hReturn
      cases hExec : L04_StackCfg.execInstrs [] code with
      | none =>
          simp [hExec] at hReturn
      | some stack =>
          cases stack with
          | nil =>
              simp [hExec] at hReturn
          | cons returned rest =>
              simp [hExec] at hReturn
              cases hReturn
              exact ⟨code, rest, returnCode?_eq_some hCode, hExec⟩

def assemble? (program : L04_StackCfg.Program) : Option Artifact :=
  if program = L04_StackCfg.Program.stop then
    some
      { bytecode := L05_Bytecode.Artifact.stop
        wf := L05_Bytecode.Artifact.stop_wf }
  else if program = L04_StackCfg.Program.returnWord0 then
    some
      { bytecode := L05_Bytecode.Artifact.returnWord0
        wf := L05_Bytecode.Artifact.returnWord0_wf }
  else
    match returnCodeValue? program with
    | some value =>
        if value < 256 then
          some
            { bytecode := L05_Bytecode.Artifact.returnByte value
              wf := L05_Bytecode.Artifact.returnByte_wf value }
        else
          none
    | none => none

structure SoundnessBoundary
    (_program : L04_StackCfg.Program) (_artifact : Artifact) :
    Prop where
  preservesBehavior :
    ∀ {behavior : L01_ValidSolidity.Behavior},
    L04_StackCfg.Semantics _program
        behavior ->
      L05_Bytecode.Semantics _artifact.bytecode behavior

theorem returnWord_isReturnWord_value_eq
    {actual expected : L04_StackCfg.Word}
    (hReturn :
      (L04_StackCfg.Program.returnWord actual).IsReturnWord expected) :
    actual = expected := by
  simp [L04_StackCfg.Program.IsReturnWord,
    L04_StackCfg.Program.returnWord, L04_StackCfg.Program.returnCode,
    L04_StackCfg.Block.returnWord, L04_StackCfg.Block.returnCode] at hReturn
  exact hReturn

theorem returnWord_isReturnWord0_value_eq
    {actual : L04_StackCfg.Word}
    (hReturn :
      (L04_StackCfg.Program.returnWord actual).IsReturnWord0) :
    actual = 0 := by
  have hEq :=
    returnWord_isReturnWord_value_eq
      (actual := actual) (expected := 0) hReturn
  exact hEq

theorem returnWord_isReturnWord3_value_eq
    {actual : L04_StackCfg.Word}
    (hReturn :
      (L04_StackCfg.Program.returnWord actual).IsReturnWord3) :
    actual = 3 := by
  have hEq :=
    returnWord_isReturnWord_value_eq
      (actual := actual) (expected := 3) hReturn
  exact hEq

theorem returnByte_sound (value : L04_StackCfg.Word)
    (hByte : value < 256) :
    SoundnessBoundary (L04_StackCfg.Program.returnWord value)
      { bytecode := L05_Bytecode.Artifact.returnByte value
        wf := L05_Bytecode.Artifact.returnByte_wf value } := by
  exact
    { preservesBehavior := by
        intro behavior hSource
        cases hSource with
        | reachesStop hStop _ =>
            simp [L04_StackCfg.Program.IsStop,
              L04_StackCfg.Program.returnWord,
              L04_StackCfg.Program.returnCode,
              L04_StackCfg.Block.stop,
              L04_StackCfg.Block.returnCode] at hStop
        | reachesReturnWord0 hReturn _ =>
            have hValue := returnWord_isReturnWord0_value_eq hReturn
            subst value
            exact L05_Bytecode.Artifact.returnByte_semantics 0 hByte
        | reachesReturnWord3 hReturn _ =>
            have hValue := returnWord_isReturnWord3_value_eq hReturn
            subst value
            exact L05_Bytecode.Artifact.returnByte_semantics 3 hByte
        | reachesReturnWord hReturn _ =>
            have hValue :=
              returnWord_isReturnWord_value_eq
                (actual := value) hReturn
            cases hValue
            exact L05_Bytecode.Artifact.returnByte_semantics value hByte
        | reachesReturnCode hReturn hExec =>
            rename_i code returned stack
            have hCode :
                code =
                  [L04_StackCfg.Instr.push
                    (L04_StackCfg.Atom.word value)] :=
              L04_StackCfg.Program.returnCode_isReturnCode_code_eq
                (actual :=
                  [L04_StackCfg.Instr.push
                    (L04_StackCfg.Atom.word value)])
                (expected := code)
                (by
                  simpa [L04_StackCfg.Program.returnWord,
                    L04_StackCfg.Block.returnWord] using hReturn)
            subst code
            simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] at hExec
            rcases hExec with ⟨hValue, _⟩
            cases hValue
            exact L05_Bytecode.Artifact.returnByte_semantics value hByte }

theorem returnCodeByte_sound
    (code : List L04_StackCfg.Instr)
    (value : L04_StackCfg.Word) (stack : List L04_StackCfg.Word)
    (hExecKnown : L04_StackCfg.execInstrs [] code = some (value :: stack))
    (hByte : value < 256) :
    SoundnessBoundary (L04_StackCfg.Program.returnCode code)
      { bytecode := L05_Bytecode.Artifact.returnByte value
        wf := L05_Bytecode.Artifact.returnByte_wf value } := by
  exact
    { preservesBehavior := by
        intro behavior hSource
        cases hSource with
        | reachesStop hStop _ =>
            simp [L04_StackCfg.Program.IsStop,
              L04_StackCfg.Program.returnCode,
              L04_StackCfg.Block.stop,
              L04_StackCfg.Block.returnCode] at hStop
        | reachesReturnWord0 hReturn _ =>
            rcases hReturn with ⟨_, hCode, _⟩
            simp [L04_StackCfg.Program.returnCode,
              L04_StackCfg.Block.returnWord,
              L04_StackCfg.Block.returnCode] at hCode
            rw [hCode.2] at hExecKnown
            simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] at hExecKnown
            rcases hExecKnown with ⟨hValue, _⟩
            subst value
            exact L05_Bytecode.Artifact.returnByte_semantics 0 hByte
        | reachesReturnWord3 hReturn _ =>
            rcases hReturn with ⟨_, hCode, _⟩
            simp [L04_StackCfg.Program.returnCode,
              L04_StackCfg.Block.returnWord,
              L04_StackCfg.Block.returnCode] at hCode
            rw [hCode.2] at hExecKnown
            simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] at hExecKnown
            rcases hExecKnown with ⟨hValue, _⟩
            subst value
            exact L05_Bytecode.Artifact.returnByte_semantics 3 hByte
        | reachesReturnWord hReturn _ =>
            rcases hReturn with ⟨_, hCode, _⟩
            simp [L04_StackCfg.Program.returnCode,
              L04_StackCfg.Block.returnWord,
              L04_StackCfg.Block.returnCode] at hCode
            rw [hCode.2] at hExecKnown
            simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] at hExecKnown
            rcases hExecKnown with ⟨hValue, _⟩
            subst value
            exact L05_Bytecode.Artifact.returnByte_semantics _ hByte
        | reachesReturnCode hReturn hExec =>
            rename_i sourceCode returned sourceStack
            have hCode :
                sourceCode = code :=
              L04_StackCfg.Program.returnCode_isReturnCode_code_eq
                (actual := code) (expected := sourceCode) hReturn
            subst sourceCode
            rw [hExecKnown] at hExec
            cases hExec
            exact L05_Bytecode.Artifact.returnByte_semantics value hByte }

theorem assemble?_sound
    {program : L04_StackCfg.Program} {artifact : Artifact}
    (hAssemble : assemble? program = some artifact) :
    SoundnessBoundary program artifact := by
  by_cases hProgram : program = L04_StackCfg.Program.stop
  · simp [assemble?, hProgram] at hAssemble
    cases hAssemble
    subst program
    exact
      { preservesBehavior := by
          intro behavior hSource
          cases hSource with
          | reachesStop _ _ =>
              exact L05_Bytecode.Artifact.stop_semantics
          | reachesReturnWord0 hReturn _ =>
              simp [L04_StackCfg.Program.IsReturnWord0,
                L04_StackCfg.Program.IsReturnWord,
                L04_StackCfg.Program.stop,
                L04_StackCfg.Block.returnWord] at hReturn
              cases hReturn
          | reachesReturnWord3 hReturn _ =>
              simp [L04_StackCfg.Program.IsReturnWord3,
                L04_StackCfg.Program.IsReturnWord,
                L04_StackCfg.Program.stop,
                L04_StackCfg.Block.returnWord] at hReturn
              cases hReturn
          | reachesReturnWord hReturn _ =>
              simp [L04_StackCfg.Program.IsReturnWord,
                L04_StackCfg.Program.stop] at hReturn
              cases hReturn
          | reachesReturnCode hReturn _ =>
              simp [L04_StackCfg.Program.IsReturnCode,
                L04_StackCfg.Program.stop, L04_StackCfg.Block.stop,
                L04_StackCfg.Block.returnCode] at hReturn
              }
  · by_cases hReturn :
      program = L04_StackCfg.Program.returnWord0
    · simp [assemble?, hReturn] at hAssemble
      cases hAssemble
      subst program
      exact
        { preservesBehavior := by
            intro behavior hSource
            cases hSource with
            | reachesStop hStop _ =>
                simp [L04_StackCfg.Program.IsStop,
                  L04_StackCfg.Program.returnWord0,
                  L04_StackCfg.Program.returnWord,
                  L04_StackCfg.Program.returnCode,
                  L04_StackCfg.Block.stop,
                  L04_StackCfg.Block.returnCode] at hStop
            | reachesReturnWord0 _ _ =>
                exact L05_Bytecode.Artifact.returnWord0_semantics
            | reachesReturnWord3 hReturn _ =>
                simp [L04_StackCfg.Program.IsReturnWord3,
                  L04_StackCfg.Program.IsReturnWord,
                  L04_StackCfg.Program.returnWord0,
                  L04_StackCfg.Program.returnWord,
                  L04_StackCfg.Program.returnCode,
                  L04_StackCfg.Block.returnWord,
                  L04_StackCfg.Block.returnCode] at hReturn
            | reachesReturnWord hReturn _ =>
                simp [L04_StackCfg.Program.IsReturnWord,
                  L04_StackCfg.Program.returnWord0,
                  L04_StackCfg.Program.returnWord,
                  L04_StackCfg.Program.returnCode,
                  L04_StackCfg.Block.returnWord,
                  L04_StackCfg.Block.returnCode] at hReturn
                cases hReturn
                exact L05_Bytecode.Artifact.returnWord0_semantics
            | reachesReturnCode hReturn hExec =>
                rename_i code value stack
                have hCode :
                    code =
                      [L04_StackCfg.Instr.push
                        (L04_StackCfg.Atom.word 0)] :=
                  L04_StackCfg.Program.returnCode_isReturnCode_code_eq
                    (actual :=
                      [L04_StackCfg.Instr.push
                        (L04_StackCfg.Atom.word 0)])
                    (expected := code)
                    (by
                      simpa [L04_StackCfg.Program.returnWord0,
                        L04_StackCfg.Program.returnWord,
                        L04_StackCfg.Block.returnWord] using hReturn)
                subst code
                simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] at hExec
                rcases hExec with ⟨hValue, _⟩
                cases hValue
                exact L05_Bytecode.Artifact.returnWord0_semantics }
    · simp [assemble?, hProgram, hReturn] at hAssemble
      cases hReturnValue : returnCodeValue? program with
      | none =>
          simp [hReturnValue] at hAssemble
      | some value =>
          simp [hReturnValue] at hAssemble
          by_cases hByte : value < 256
          · simp [hByte] at hAssemble
            cases hAssemble
            rcases returnCodeValue?_eq_some hReturnValue with
              ⟨code, stack, hProgramEq, hExecKnown⟩
            subst program
            exact returnCodeByte_sound code value stack hExecKnown hByte
          · simp [hByte] at hAssemble

theorem assemble?_complete_for_stop
    {program : L04_StackCfg.Program}
    (hStop : program.IsStop) :
    ∃ artifact, assemble? program = some artifact := by
  rcases hStop with ⟨hEntry, hBlocks, hFunctions⟩
  have hProgram : program = L04_StackCfg.Program.stop := by
    cases program with
    | mk entry blocks functions =>
        cases hEntry
        cases hBlocks
        cases hFunctions
        rfl
  subst program
  exact
    ⟨{ bytecode := L05_Bytecode.Artifact.stop
       wf := L05_Bytecode.Artifact.stop_wf },
      by simp [assemble?]⟩

theorem assemble?_complete_for_returnWord0
    {program : L04_StackCfg.Program}
    (hReturn : program.IsReturnWord0) :
    ∃ artifact, assemble? program = some artifact := by
  rcases hReturn with ⟨hEntry, hBlocks, hFunctions⟩
  have hProgram : program = L04_StackCfg.Program.returnWord0 := by
    cases program with
    | mk entry blocks functions =>
        cases hEntry
        cases hBlocks
        cases hFunctions
        rfl
  subst program
  have hReturnNotStop :
      L04_StackCfg.Program.returnWord0 ≠ L04_StackCfg.Program.stop := by
    intro h
    cases h
  exact
    ⟨{ bytecode := L05_Bytecode.Artifact.returnWord0
       wf := L05_Bytecode.Artifact.returnWord0_wf },
      by simp [assemble?, hReturnNotStop]⟩

theorem returnWordValue?_returnWord (value : L04_StackCfg.Word) :
    returnWordValue? (L04_StackCfg.Program.returnWord value) = some value := by
  simp [returnWordValue?, L04_StackCfg.Program.returnWord,
    L04_StackCfg.Program.returnCode, L04_StackCfg.Block.returnCode,
    L04_StackCfg.Label.entry,
    L04_StackCfg.StackSignature.returningWith]

theorem returnCodeValue?_returnWord (value : L04_StackCfg.Word) :
    returnCodeValue? (L04_StackCfg.Program.returnWord value) = some value := by
  simp [returnCodeValue?, returnCode?,
    L04_StackCfg.Program.returnWord, L04_StackCfg.Program.returnCode,
    L04_StackCfg.Block.returnCode, L04_StackCfg.Label.entry,
    L04_StackCfg.StackSignature.returningWith,
    L04_StackCfg.execInstrs, L04_StackCfg.execInstr]

theorem returnCodeValue?_returnCode
    {code : List L04_StackCfg.Instr} {value : L04_StackCfg.Word}
    {stack : List L04_StackCfg.Word}
    (hExec : L04_StackCfg.execInstrs [] code = some (value :: stack)) :
    returnCodeValue? (L04_StackCfg.Program.returnCode code) =
      some value := by
  simp [returnCodeValue?, returnCode?,
    L04_StackCfg.Program.returnCode, L04_StackCfg.Block.returnCode,
    L04_StackCfg.Label.entry,
    L04_StackCfg.StackSignature.returningWith, hExec]

theorem assemble?_complete_for_returnByte
    {program : L04_StackCfg.Program} {value : L04_StackCfg.Word}
    (hReturn : program.IsReturnWord value)
    (hByte : value < 256) :
    ∃ artifact, assemble? program = some artifact := by
  rcases hReturn with ⟨hEntry, hBlocks, hFunctions⟩
  have hProgram : program = L04_StackCfg.Program.returnWord value := by
    cases program with
    | mk entry blocks functions =>
        cases hEntry
        cases hBlocks
        cases hFunctions
        rfl
  subst program
  have hReturnNotStop :
      L04_StackCfg.Program.returnWord value ≠ L04_StackCfg.Program.stop := by
    intro h
    cases h
  by_cases hReturn0 :
      L04_StackCfg.Program.returnWord value =
        L04_StackCfg.Program.returnWord0
  · exact
      ⟨{ bytecode := L05_Bytecode.Artifact.returnWord0
         wf := L05_Bytecode.Artifact.returnWord0_wf },
        by
          have hReturnWord0NotStop :
              L04_StackCfg.Program.returnWord0 ≠
                L04_StackCfg.Program.stop := by
            intro h
            cases h
          simp [assemble?, hReturn0, hReturnWord0NotStop]⟩
  · exact
      ⟨{ bytecode := L05_Bytecode.Artifact.returnByte value
         wf := L05_Bytecode.Artifact.returnByte_wf value },
        by
          simp [assemble?, hReturnNotStop, hReturn0,
            returnCodeValue?_returnWord value, hByte]⟩

theorem assemble?_complete_for_returnCodeByte
    {program : L04_StackCfg.Program} {code : List L04_StackCfg.Instr}
    {value : L04_StackCfg.Word} {stack : List L04_StackCfg.Word}
    (hReturn : program.IsReturnCode code)
    (hExec : L04_StackCfg.execInstrs [] code = some (value :: stack))
    (hByte : value < 256) :
    ∃ artifact, assemble? program = some artifact := by
  rcases hReturn with ⟨hEntry, hBlocks, hFunctions⟩
  have hProgram : program = L04_StackCfg.Program.returnCode code := by
    cases program with
    | mk entry blocks functions =>
        cases hEntry
        cases hBlocks
        cases hFunctions
        rfl
  subst program
  have hReturnNotStop :
      L04_StackCfg.Program.returnCode code ≠
        L04_StackCfg.Program.stop := by
    intro h
    cases h
  by_cases hReturn0 :
      L04_StackCfg.Program.returnCode code =
        L04_StackCfg.Program.returnWord0
  · exact
      ⟨{ bytecode := L05_Bytecode.Artifact.returnWord0
         wf := L05_Bytecode.Artifact.returnWord0_wf },
        by
          have hReturnWord0NotStop :
              L04_StackCfg.Program.returnWord0 ≠
                L04_StackCfg.Program.stop := by
            intro h
            cases h
          simp [assemble?, hReturn0, hReturnWord0NotStop]⟩
  · exact
      ⟨{ bytecode := L05_Bytecode.Artifact.returnByte value
         wf := L05_Bytecode.Artifact.returnByte_wf value },
        by
          simp [assemble?, hReturnNotStop, hReturn0,
            returnCodeValue?_returnCode hExec, hByte]⟩

end P05_StackCfgToBytecode
end Passes
end Spine
end SolidCore
