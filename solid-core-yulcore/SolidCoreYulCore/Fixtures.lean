import SolidCoreYulCore.Relations

namespace SolidCoreYulCore
namespace Fixtures

def hashByLength : ConcreteYul.HashOracle :=
  { keccak256 := fun bytes => bytes.length }

def storeThenReturn : ConcreteYul.Stmt :=
  ConcreteYul.Stmt.seq
    (ConcreteYul.Stmt.expr
      (ConcreteYul.Expr.builtin Evm.Builtin.sstore [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 7]))
    (ConcreteYul.Stmt.seq
      (ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.mstore
          [ConcreteYul.Expr.word 0, ConcreteYul.Expr.builtin Evm.Builtin.sload [ConcreteYul.Expr.word 0]]))
      (ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.returnOp [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 32])))

set_option maxRecDepth 2000 in
theorem storeThenReturn_fixture :
    ConcreteYul.evalStmtFuel hashByLength 12 ConcreteYul.Config.empty storeThenReturn =
      some
        { flow := ConcreteYul.Flow.halted
          config :=
            { ConcreteYul.Config.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 7)])]
                  memory := ConcreteYul.writeWord [] 0 7
                  memorySize := 32
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := ConcreteYul.wordToBytes32 7 } } } } := by
  rfl

def keccakStorageStore : ConcreteYul.Stmt :=
  ConcreteYul.Stmt.seq
    (ConcreteYul.Stmt.expr
      (ConcreteYul.Expr.builtin Evm.Builtin.mstore [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 42]))
    (ConcreteYul.Stmt.expr
      (ConcreteYul.Expr.builtin Evm.Builtin.sstore
        [ ConcreteYul.Expr.builtin Evm.Builtin.keccak256Op [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 32]
        , ConcreteYul.Expr.word 9 ]))

set_option maxRecDepth 2000 in
theorem keccakStorageStore_fixture :
    ConcreteYul.evalStmtFuel hashByLength 10 ConcreteYul.Config.empty keccakStorageStore =
      some
        { flow := ConcreteYul.Flow.normal
          config :=
            { ConcreteYul.Config.empty with
              state :=
                { ConcreteYul.State.empty with
                  memory := ConcreteYul.writeWord [] 0 42
                  memorySize := 32
                  storage := [(0, [(32, 9)])] } } } := by
  rfl

def objectDataCopy : ConcreteYul.Stmt :=
  ConcreteYul.Stmt.expr
    (ConcreteYul.Expr.builtin Evm.Builtin.datacopyOp
      [ConcreteYul.Expr.word 0, ConcreteYul.Expr.dataOffset 1, ConcreteYul.Expr.dataSize 1])

def objectDataConfig : ConcreteYul.Config :=
  { ConcreteYul.Config.empty with object := { data := [(1, [1, 2, 3, 4])] } }

theorem objectDataCopy_fixture :
    ConcreteYul.evalStmtFuel hashByLength 4 objectDataConfig objectDataCopy =
      some
        { flow := ConcreteYul.Flow.normal
          config :=
            { objectDataConfig with
              state := { ConcreteYul.State.empty with memory := [1, 2, 3, 4], memorySize := 32 } } } := by
  rfl

def objectDataCopyProgram : ConcreteYul.Program :=
  { object := { data := [(1, [1, 2, 3, 4])] }
    body := objectDataCopy }

theorem objectDataCopyProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 4 objectDataCopyProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              object := { data := [(1, [1, 2, 3, 4])] }
              state :=
                { ConcreteYul.State.empty with
                  memory := [1, 2, 3, 4]
                  memorySize := 32 } } } := by
  rfl

theorem objectDataCopyProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withObjectDataBuiltins
      FullYul.StaticContext.empty objectDataCopyProgram := by
  refine ⟨4, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [objectDataCopyProgram, objectDataCopy,
      Relations.embedConcreteStmt, Relations.embedConcreteStmtFuel,
      Relations.embedConcreteExpr, Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr FullYul.CompilerProfile.ObjectDataBuiltin.datacopyOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
      | trivial
  · simp [objectDataCopyProgram, objectDataCopy,
      Relations.embedConcreteStmt, Relations.embedConcreteStmtFuel,
      Relations.embedConcreteExpr, Relations.embedConcreteExprs,
      FullYul.checkStmtFuel, FullYul.checkStmtExpr, FullYul.checkExprs,
      FullYul.checkExpr, Evm.Builtin.signature?]

noncomputable def objectDataCopyProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withObjectDataBuiltins
      FullYul.StaticContext.empty objectDataCopyProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withObjectDataBuiltins
    FullYul.StaticContext.empty objectDataCopyProgram_accepted

noncomputable def objectDataCopyProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithObjectDataProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty objectDataCopyProgram :=
  Relations.CurrentSolidCoreWithObjectDataProgramSemanticBoundaryEvidence.ofAcceptedAt
    objectDataCopyProgram_coverageEvidence

def currentSolidCoreStorageFullYul : FullYul.Stmt :=
  FullYul.Stmt.seq
    (FullYul.Stmt.expr
      (FullYul.Expr.builtin Evm.Builtin.sstore
        [ FullYul.Expr.value (FullYul.Value.word 0)
        , FullYul.Expr.value (FullYul.Value.word 7) ]))
    (FullYul.Stmt.let1 1
      (some
        (FullYul.Expr.builtin Evm.Builtin.sload
          [FullYul.Expr.value (FullYul.Value.word 0)])))

theorem currentSolidCoreStorageFullYul_compilerEmittable :
    FullYul.CompilerEmittableStmt
      FullYul.CompilerProfile.currentSolidCore
      currentSolidCoreStorageFullYul := by
  repeat constructor

theorem currentSolidCoreStorageFullYul_static_checked :
    FullYul.checkStmtFuel 6 FullYul.StaticContext.empty false false
      currentSolidCoreStorageFullYul =
        some { vars := [1], funcs := [] } := by
  rfl

def currentSolidCoreLoopFullYul : FullYul.Stmt :=
  FullYul.Stmt.forLoop
    FullYul.Stmt.skip
    (FullYul.Expr.value (FullYul.Value.word 0))
    FullYul.Stmt.skip
    FullYul.Stmt.skip

theorem currentSolidCoreLoopFullYul_compilerEmittable :
    FullYul.CompilerEmittableStmt
      FullYul.CompilerProfile.currentSolidCore
      currentSolidCoreLoopFullYul := by
  repeat constructor

theorem currentSolidCoreLoopFullYul_static_checked :
    FullYul.checkStmtFuel 6 FullYul.StaticContext.empty false false
      currentSolidCoreLoopFullYul = some FullYul.StaticContext.empty := by
  rfl

def switchStoreProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.switch (ConcreteYul.Expr.word 2)
        [ (1,
            ConcreteYul.Stmt.expr
              (ConcreteYul.Expr.builtin Evm.Builtin.sstore
                [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 1]))
        , (2,
            ConcreteYul.Stmt.expr
              (ConcreteYul.Expr.builtin Evm.Builtin.sstore
                [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 9])) ]
        (some
          (ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 99]))) }

theorem switchStoreProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 switchStoreProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 9)])] } } } := by
  rfl

theorem switchStoreProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty switchStoreProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [switchStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, Relations.embedConcreteSwitchCasesFuel,
      FullYul.CompilerProfile.currentSolidCore]
    repeat
      first
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
      | trivial
  · simp [switchStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, Relations.embedConcreteSwitchCasesFuel,
      FullYul.checkStmtFuel, FullYul.checkStmtExpr, FullYul.checkExprs,
      FullYul.checkExpr, FullYul.checkSwitchCasesFuel,
      FullYul.switchHasBranch, FullYul.switchCaseLabelsUnique,
      FullYul.containsSwitchLabel, Relations.embedWordValue,
      norm, wordModulus, Evm.Builtin.signature?]

noncomputable def switchStoreProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty switchStoreProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore
    FullYul.StaticContext.empty switchStoreProgram_accepted

noncomputable def switchStoreProgram_semanticBoundary :
    Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty switchStoreProgram :=
  Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence.ofAcceptedAt
    switchStoreProgram_coverageEvidence

def popLoadProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.seq
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.sstore
            [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 7]))
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.popOp
            [ConcreteYul.Expr.builtin Evm.Builtin.sload
              [ConcreteYul.Expr.word 0]])) }

theorem popLoadProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 popLoadProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 7)])] } } } := by
  rfl

theorem popLoadProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty popLoadProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [popLoadProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.CompilerProfile.currentSolidCore]
    repeat
      first
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.popOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sload
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
      | trivial
  · simp [popLoadProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      FullYul.predeclareStmtFunctionSigs?, Evm.Builtin.signature?]

noncomputable def popLoadProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty popLoadProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore
    FullYul.StaticContext.empty popLoadProgram_accepted

noncomputable def popLoadProgram_semanticBoundary :
    Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty popLoadProgram :=
  Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence.ofAcceptedAt
    popLoadProgram_coverageEvidence

def signextendClzStoreProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.sstore
          [ ConcreteYul.Expr.builtin Evm.Builtin.clzOp
              [ConcreteYul.Expr.word 0]
          , ConcreteYul.Expr.builtin Evm.Builtin.signextendOp
              [ConcreteYul.Expr.word 31, ConcreteYul.Expr.word 5] ]) }

set_option maxRecDepth 2000 in
theorem signextendClzStoreProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 signextendClzStoreProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(256, 5)])] } } } := by
  rfl

theorem signextendClzStoreProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty signextendClzStoreProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [signextendClzStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.clzOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.signextendOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [signextendClzStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def signextendClzStoreProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty signextendClzStoreProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore
    FullYul.StaticContext.empty signextendClzStoreProgram_accepted

noncomputable def signextendClzStoreProgram_semanticBoundary :
    Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty signextendClzStoreProgram :=
  Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence.ofAcceptedAt
    signextendClzStoreProgram_coverageEvidence

def contextWordStoreProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.sstore
          [ ConcreteYul.Expr.word 0
          , ConcreteYul.Expr.builtin Evm.Builtin.add
              [ ConcreteYul.Expr.builtin Evm.Builtin.difficultyOp []
              , ConcreteYul.Expr.builtin Evm.Builtin.prevrandaoOp [] ] ]) }

def contextWordStoreConfig : ConcreteYul.RuntimeConfig :=
  { ConcreteYul.RuntimeConfig.empty with
    state :=
      { ConcreteYul.State.empty with
        difficulty := 11
        prevrandao := 22 } }

set_option maxRecDepth 2000 in
theorem contextWordStoreProgram_runs :
    ConcreteYul.evalRuntimeStmtFuel hashByLength 6 contextWordStoreConfig
      contextWordStoreProgram.body =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { contextWordStoreConfig with
              state :=
                { ConcreteYul.State.empty with
                  difficulty := 11
                  prevrandao := 22
                  storage := [(0, [(0, 33)])] } } } := by
  rfl

theorem contextWordStoreProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withContextBuiltins
      FullYul.StaticContext.empty contextWordStoreProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [contextWordStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.add
      | exact Or.inr FullYul.CompilerProfile.ContextWordBuiltin.difficultyOp
      | exact Or.inr FullYul.CompilerProfile.ContextWordBuiltin.prevrandaoOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [contextWordStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def contextWordStoreProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withContextBuiltins
      FullYul.StaticContext.empty contextWordStoreProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withContextBuiltins
    FullYul.StaticContext.empty contextWordStoreProgram_accepted

noncomputable def contextWordStoreProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithContextProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty contextWordStoreProgram :=
  Relations.CurrentSolidCoreWithContextProgramSemanticBoundaryEvidence.ofAcceptedAt
    contextWordStoreProgram_coverageEvidence

def emptyReturnProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.returnOp
          [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0]) }

theorem emptyReturnProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 3 emptyReturnProgram =
      some
        { flow := ConcreteYul.CompleteFlow.halted
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  halt? := some
                    { kind := Evm.HaltKind.returned, returndata := [] } } } } := by
  rfl

theorem emptyReturnProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty emptyReturnProgram := by
  refine ⟨3, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [emptyReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    constructor
    · constructor
      · exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.returnOp
      · repeat constructor
  · simp [emptyReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def emptyReturnProgram_semanticBoundary :
    Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty emptyReturnProgram :=
  Relations.CurrentSolidCoreProgramSemanticBoundaryEvidence.ofAcceptedAt
    (Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
      FullYul.CompilerProfile.currentSolidCore
      FullYul.StaticContext.empty emptyReturnProgram_accepted)

def memoryStoreReturnProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.seq
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.mstore
            [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 7]))
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.returnOp
            [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 32])) }

set_option maxRecDepth 2000 in
theorem memoryStoreReturnProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 20 memoryStoreReturnProgram =
      some
        { flow := ConcreteYul.CompleteFlow.halted
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  memory :=
                    ConcreteYul.writeWord [] 0 7
                  memorySize := 32
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := ConcreteYul.wordToBytes32 7 } } } } := by
  rfl

theorem memoryStoreReturnProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withMemoryBuiltins
      FullYul.StaticContext.empty memoryStoreReturnProgram := by
  refine ⟨20, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [memoryStoreReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr FullYul.CompilerProfile.MemoryBuiltin.mstore
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.returnOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [memoryStoreReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      FullYul.predeclareStmtFunctionSigs?, Evm.Builtin.signature?]

noncomputable def memoryStoreReturnProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withMemoryBuiltins
      FullYul.StaticContext.empty memoryStoreReturnProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withMemoryBuiltins
    FullYul.StaticContext.empty memoryStoreReturnProgram_accepted

noncomputable def memoryStoreReturnProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithMemoryProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty memoryStoreReturnProgram :=
  Relations.CurrentSolidCoreWithMemoryProgramSemanticBoundaryEvidence.ofAcceptedAt
    memoryStoreReturnProgram_coverageEvidence

def keccakEmptyStoreProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.sstore
          [ ConcreteYul.Expr.builtin Evm.Builtin.keccak256Op
              [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0]
          , ConcreteYul.Expr.word 9 ]) }

theorem keccakEmptyStoreProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 keccakEmptyStoreProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 9)])] } } } := by
  rfl

theorem keccakEmptyStoreProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withMemoryHashBuiltins
      FullYul.StaticContext.empty keccakEmptyStoreProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [keccakEmptyStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr FullYul.CompilerProfile.MemoryHashBuiltin.keccak256Op
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [keccakEmptyStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def keccakEmptyStoreProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withMemoryHashBuiltins
      FullYul.StaticContext.empty keccakEmptyStoreProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withMemoryHashBuiltins
    FullYul.StaticContext.empty keccakEmptyStoreProgram_accepted

noncomputable def keccakEmptyStoreProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithMemoryHashProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty keccakEmptyStoreProgram :=
  Relations.CurrentSolidCoreWithMemoryHashProgramSemanticBoundaryEvidence.ofAcceptedAt
    keccakEmptyStoreProgram_coverageEvidence

def calldataCopyReturnProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.seq
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.calldatacopyOp
            [ ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 4 ]))
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.returnOp
            [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 4])) }

theorem calldataCopyReturnProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 calldataCopyReturnProgram =
      some
        { flow := ConcreteYul.CompleteFlow.halted
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  memory := [0, 0, 0, 0]
                  memorySize := 32
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := [0, 0, 0, 0] } } } } := by
  rfl

theorem calldataCopyReturnProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
      FullYul.StaticContext.empty calldataCopyReturnProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [calldataCopyReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr FullYul.CompilerProfile.BufferBuiltin.calldatacopyOp
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.returnOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [calldataCopyReturnProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      FullYul.predeclareStmtFunctionSigs?, Evm.Builtin.signature?]

noncomputable def calldataCopyReturnProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
      FullYul.StaticContext.empty calldataCopyReturnProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
    FullYul.StaticContext.empty calldataCopyReturnProgram_accepted

noncomputable def calldataCopyReturnProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithBufferProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty calldataCopyReturnProgram :=
  Relations.CurrentSolidCoreWithBufferProgramSemanticBoundaryEvidence.ofAcceptedAt
    calldataCopyReturnProgram_coverageEvidence

def calldataLoadStoreProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.sstore
          [ ConcreteYul.Expr.word 0
          , ConcreteYul.Expr.builtin Evm.Builtin.calldataloadOp
              [ConcreteYul.Expr.word 0] ]) }

theorem calldataLoadStoreProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 6 calldataLoadStoreProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 0)])] } } } := by
  rfl

theorem calldataLoadStoreProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
      FullYul.StaticContext.empty calldataLoadStoreProgram := by
  refine ⟨6, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [calldataLoadStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact Or.inr FullYul.CompilerProfile.BufferBuiltin.calldataloadOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [calldataLoadStoreProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def calldataLoadStoreProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
      FullYul.StaticContext.empty calldataLoadStoreProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withBufferBuiltins
    FullYul.StaticContext.empty calldataLoadStoreProgram_accepted

noncomputable def calldataLoadStoreProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithBufferProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty calldataLoadStoreProgram :=
  Relations.CurrentSolidCoreWithBufferProgramSemanticBoundaryEvidence.ofAcceptedAt
    calldataLoadStoreProgram_coverageEvidence

def memoryguardProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.let1 1
        (some
          (ConcreteYul.Expr.builtin Evm.Builtin.memoryguardOp
            [ConcreteYul.Expr.word 64])) }

theorem memoryguardProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 4 memoryguardProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              env := [(1, 64)] } } := by
  rfl

theorem memoryguardProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withCompilerAnnotations
      FullYul.StaticContext.empty memoryguardProgram := by
  refine ⟨4, { vars := [1], funcs := [] }, ?_⟩
  constructor
  · simp [memoryguardProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    constructor
    · constructor
      · exact Or.inr
          FullYul.CompilerProfile.CompilerAnnotationBuiltin.memoryguardOp
      · repeat constructor
  · simp [memoryguardProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkExpr, FullYul.checkExprs, FullYul.addVarName?,
      FullYul.addScopedName?, FullYul.containsName,
      FullYul.containsFunctionName, FullYul.StaticContext.empty,
      Evm.Builtin.signature?]

noncomputable def memoryguardProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withCompilerAnnotations
      FullYul.StaticContext.empty memoryguardProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withCompilerAnnotations
    FullYul.StaticContext.empty memoryguardProgram_accepted

noncomputable def memoryguardProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithCompilerAnnotationsProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty memoryguardProgram :=
  Relations.CurrentSolidCoreWithCompilerAnnotationsProgramSemanticBoundaryEvidence.ofAcceptedAt
    memoryguardProgram_coverageEvidence

def compilerArtifactProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.seq
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.setimmutableOp
            [ ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 1
            , ConcreteYul.Expr.word 7 ]))
        (ConcreteYul.Stmt.seq
          (ConcreteYul.Stmt.let1 1
            (some
              (ConcreteYul.Expr.builtin Evm.Builtin.loadimmutableOp
                [ConcreteYul.Expr.word 1])))
          (ConcreteYul.Stmt.let1 2
            (some
              (ConcreteYul.Expr.builtin Evm.Builtin.linkersymbolOp
                [ConcreteYul.Expr.word 2])))) }

def compilerArtifactConfig : ConcreteYul.RuntimeConfig :=
  { ConcreteYul.RuntimeConfig.empty with
    state := { ConcreteYul.State.empty with linkerSymbols := [(2, 99)] } }

theorem compilerArtifactProgram_runs :
    ConcreteYul.evalRuntimeStmtFuel hashByLength 8 compilerArtifactConfig
        compilerArtifactProgram.body =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { compilerArtifactConfig with
              env := [(2, 99), (1, 7)]
              state :=
                { ConcreteYul.State.empty with
                  immutables := [(1, 7)]
                  linkerSymbols := [(2, 99)] } } } := by
  rfl

theorem compilerArtifactProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
      FullYul.StaticContext.empty compilerArtifactProgram := by
  refine ⟨8, { vars := [2, 1], funcs := [] }, ?_⟩
  constructor
  · simp [compilerArtifactProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr
          FullYul.CompilerProfile.CompilerArtifactBuiltin.setimmutableOp
      | exact Or.inr
          FullYul.CompilerProfile.CompilerArtifactBuiltin.loadimmutableOp
      | exact Or.inr
          FullYul.CompilerProfile.CompilerArtifactBuiltin.linkersymbolOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
      | trivial
  · simp [compilerArtifactProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      FullYul.addVarName?, FullYul.addScopedName?,
      FullYul.predeclareStmtFunctionSigs?, FullYul.containsName,
      FullYul.containsFunctionName, FullYul.StaticContext.empty,
      Evm.Builtin.signature?]

noncomputable def compilerArtifactProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
      FullYul.StaticContext.empty compilerArtifactProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
    FullYul.StaticContext.empty compilerArtifactProgram_accepted

noncomputable def compilerArtifactProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithCompilerArtifactProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty compilerArtifactProgram :=
  Relations.CurrentSolidCoreWithCompilerArtifactProgramSemanticBoundaryEvidence.ofAcceptedAt
    compilerArtifactProgram_coverageEvidence

def verbatimProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.letMany [0, 1]
        (some
          [ConcreteYul.Expr.builtin (Evm.Builtin.verbatimOp 1 2)
            [ConcreteYul.Expr.word 5]]) }

theorem verbatimProgram_runs :
    ConcreteYul.runProgramFuel ConcreteYul.sampleVerbatimHash 4
      verbatimProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              env := [(1, 9), (0, 7)]
              state :=
                { ConcreteYul.State.empty with
                  externalActions :=
                    [{ builtin := Evm.Builtin.verbatimOp 1 2
                       args := [5] }] } } } := by
  rfl

theorem verbatimProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withVerbatimBuiltins
      FullYul.StaticContext.empty verbatimProgram := by
  refine ⟨4, { vars := [1, 0], funcs := [] }, ?_⟩
  constructor
  · simp [verbatimProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    repeat
      first
      | exact Or.inr
          (FullYul.CompilerProfile.VerbatimBuiltin.verbatimOp 1 2)
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
      | trivial
  · simp [verbatimProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkExprsAsYulValues, FullYul.checkExprs,
      FullYul.checkExpr, FullYul.addVarNames?, FullYul.addVarName?,
      FullYul.addScopedName?, FullYul.containsName,
      FullYul.containsFunctionName,
      FullYul.StaticContext.empty, Evm.Builtin.signature?]

noncomputable def verbatimProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withVerbatimBuiltins
      FullYul.StaticContext.empty verbatimProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withVerbatimBuiltins
    FullYul.StaticContext.empty verbatimProgram_accepted

noncomputable def verbatimProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithVerbatimProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty verbatimProgram :=
  Relations.CurrentSolidCoreWithVerbatimProgramSemanticBoundaryEvidence.ofAcceptedAt
    verbatimProgram_coverageEvidence

def externalCallProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.let1 1
        (some
          (ConcreteYul.Expr.builtin Evm.Builtin.callOp
            [ ConcreteYul.Expr.word 100
            , ConcreteYul.Expr.word 2
            , ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.word 0 ])) }

theorem externalCallProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 4 externalCallProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              env := [(1, 1)]
              state :=
                { ConcreteYul.State.empty with
                  externalActions :=
                    [{ builtin := Evm.Builtin.callOp
                       args := [100, 2, 0, 0, 0, 0, 0] }] } } } := by
  rfl

theorem externalCallProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withExternalCalls
      FullYul.StaticContext.empty externalCallProgram := by
  refine ⟨4, { vars := [1], funcs := [] }, ?_⟩
  constructor
  · simp [externalCallProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    constructor
    · constructor
      · exact Or.inr FullYul.CompilerProfile.ExternalCallBuiltin.callOp
      · repeat constructor
  · simp [externalCallProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel, FullYul.checkExpr,
      FullYul.checkExprs, FullYul.addVarName?, FullYul.addScopedName?,
      FullYul.containsName, FullYul.containsFunctionName,
      FullYul.StaticContext.empty, Evm.Builtin.signature?]

noncomputable def externalCallProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withExternalCalls
      FullYul.StaticContext.empty externalCallProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withExternalCalls
    FullYul.StaticContext.empty externalCallProgram_accepted

noncomputable def externalCallProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithExternalCallsProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty externalCallProgram :=
  Relations.CurrentSolidCoreWithExternalCallsProgramSemanticBoundaryEvidence.ofAcceptedAt
    externalCallProgram_coverageEvidence

def selfdestructProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.selfdestructOp
          [ConcreteYul.Expr.word 2]) }

theorem selfdestructProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 3 selfdestructProgram =
      some
        { flow := ConcreteYul.CompleteFlow.halted
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  externalActions :=
                    [{ builtin := Evm.Builtin.selfdestructOp, args := [2] }]
                  halt? := some
                    { kind := Evm.HaltKind.stop, returndata := [] } } } } := by
  rfl

theorem selfdestructProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidCore.withExternalCalls
      FullYul.StaticContext.empty selfdestructProgram := by
  refine ⟨3, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [selfdestructProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs]
    constructor
    · constructor
      · exact Or.inr
          FullYul.CompilerProfile.ExternalCallBuiltin.selfdestructOp
      · repeat constructor
  · simp [selfdestructProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def selfdestructProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidCore.withExternalCalls
      FullYul.StaticContext.empty selfdestructProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidCore.withExternalCalls
    FullYul.StaticContext.empty selfdestructProgram_accepted

noncomputable def selfdestructProgram_semanticBoundary :
    Relations.CurrentSolidCoreWithExternalCallsProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty selfdestructProgram :=
  Relations.CurrentSolidCoreWithExternalCallsProgramSemanticBoundaryEvidence.ofAcceptedAt
    selfdestructProgram_coverageEvidence

def solidityAggregateMixedProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.seq
        (ConcreteYul.Stmt.expr
          (ConcreteYul.Expr.builtin Evm.Builtin.mstore
            [ ConcreteYul.Expr.word 0
            , ConcreteYul.Expr.builtin Evm.Builtin.timestampOp [] ]))
        (ConcreteYul.Stmt.seq
          (ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.builtin Evm.Builtin.keccak256Op
                  [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 32]
              , ConcreteYul.Expr.builtin Evm.Builtin.calldataloadOp
                  [ConcreteYul.Expr.word 0] ]))
          (ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.log0Op
              [ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0]))) }

theorem solidityAggregateMixedProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 12
        solidityAggregateMixedProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(32, 0)])]
                  memory := ConcreteYul.wordToBytes32 0
                  memorySize := 32
                  logs := [(0, [], [])] } } } := by
  rfl

theorem solidityAggregateMixedProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidityEmittable
      FullYul.StaticContext.empty solidityAggregateMixedProgram := by
  refine ⟨12, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [solidityAggregateMixedProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs,
      FullYul.CompilerProfile.currentSolidityEmittable,
      FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
      FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
    repeat
      first
      | exact Or.inr FullYul.CompilerProfile.ExternalCallBuiltin.log0Op
      | exact Or.inr FullYul.CompilerProfile.ContextWordBuiltin.timestampOp
      | exact Or.inr FullYul.CompilerProfile.BufferBuiltin.calldataloadOp
      | exact Or.inr FullYul.CompilerProfile.MemoryHashBuiltin.keccak256Op
      | exact Or.inr FullYul.CompilerProfile.MemoryBuiltin.mstore
      | exact Or.inl FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [solidityAggregateMixedProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      FullYul.predeclareStmtFunctionSigs?, Evm.Builtin.signature?]

noncomputable def solidityAggregateMixedProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidityEmittable
      FullYul.StaticContext.empty solidityAggregateMixedProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidityEmittable
    FullYul.StaticContext.empty solidityAggregateMixedProgram_accepted

noncomputable def solidityAggregateMixedProgram_semanticBoundary :
    Relations.CurrentSolidityEmittableNoVerbatimProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty solidityAggregateMixedProgram :=
  Relations.CurrentSolidityEmittableNoVerbatimProgramSemanticBoundaryEvidence.ofAcceptedAt
    solidityAggregateMixedProgram_coverageEvidence

namespace SolidityEmittableBuiltinOK

theorem mcopyOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.mcopyOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.MemoryCopyBuiltin.mcopyOp

theorem returndataloadOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.returndataloadOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.ReturnDataBuiltin.returndataloadOp

theorem returndatasizeOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.returndatasizeOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.ReturnDataBuiltin.returndatasizeOp

theorem returndatacopyOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.returndatacopyOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.ReturnDataBuiltin.returndatacopyOp

theorem codecopyOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.codecopyOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.CodeBuiltin.codecopyOp

theorem codesizeOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.codesizeOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left; left; left; left
  right
  exact FullYul.CompilerProfile.CodeBuiltin.codesizeOp

theorem blockhashOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.blockhashOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.blockhashOp

theorem balanceOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.balanceOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.balanceOp

theorem extcodesizeOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.extcodesizeOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.extcodesizeOp

theorem extcodehashOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.extcodehashOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.extcodehashOp

theorem extcodecopyOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.extcodecopyOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.extcodecopyOp

theorem blobhashOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.blobhashOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left; left
  right
  exact FullYul.CompilerProfile.ExternalQueryBuiltin.blobhashOp

theorem tloadOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.tloadOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left
  right
  exact FullYul.CompilerProfile.TransientStorageBuiltin.tloadOp

theorem tstoreOp :
    FullYul.CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.tstoreOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittable,
    FullYul.CompilerProfile.currentSolidityEmittableNoVerbatim,
    FullYul.CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
  left; left; left
  right
  exact FullYul.CompilerProfile.TransientStorageBuiltin.tstoreOp

end SolidityEmittableBuiltinOK

def solidityExpandedBuiltinProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.block
        [ ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.tstoreOp
              [ ConcreteYul.Expr.word 1
              , ConcreteYul.Expr.builtin Evm.Builtin.returndatasizeOp [] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.mcopyOp
              [ ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0
              , ConcreteYul.Expr.word 0 ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.returndatacopyOp
              [ ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0
              , ConcreteYul.Expr.word 0 ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.codecopyOp
              [ ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0
              , ConcreteYul.Expr.word 0 ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.extcodecopyOp
              [ ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0
              , ConcreteYul.Expr.word 0, ConcreteYul.Expr.word 0 ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 10
              , ConcreteYul.Expr.builtin Evm.Builtin.balanceOp
                  [ConcreteYul.Expr.word 0] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 11
              , ConcreteYul.Expr.builtin Evm.Builtin.tloadOp
                  [ConcreteYul.Expr.word 1] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 12
              , ConcreteYul.Expr.builtin Evm.Builtin.returndataloadOp
                  [ConcreteYul.Expr.word 0] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 13
              , ConcreteYul.Expr.builtin Evm.Builtin.codesizeOp [] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 14
              , ConcreteYul.Expr.builtin Evm.Builtin.blockhashOp
                  [ConcreteYul.Expr.word 0] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 15
              , ConcreteYul.Expr.builtin Evm.Builtin.extcodesizeOp
                  [ConcreteYul.Expr.word 0] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 16
              , ConcreteYul.Expr.builtin Evm.Builtin.extcodehashOp
                  [ConcreteYul.Expr.word 0] ])
        , ConcreteYul.Stmt.expr
            (ConcreteYul.Expr.builtin Evm.Builtin.sstore
              [ ConcreteYul.Expr.word 17
              , ConcreteYul.Expr.builtin Evm.Builtin.blobhashOp
                  [ConcreteYul.Expr.word 0] ]) ] }

theorem solidityExpandedBuiltinProgram_runs_some :
    (ConcreteYul.runProgramFuel hashByLength 40
      solidityExpandedBuiltinProgram).isSome = true := by
  rfl

theorem solidityExpandedBuiltinProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidityEmittable
      FullYul.StaticContext.empty solidityExpandedBuiltinProgram := by
  refine ⟨40, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [solidityExpandedBuiltinProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel]
    repeat
      first
      | exact SolidityEmittableBuiltinOK.mcopyOp
      | exact SolidityEmittableBuiltinOK.returndataloadOp
      | exact SolidityEmittableBuiltinOK.returndatasizeOp
      | exact SolidityEmittableBuiltinOK.returndatacopyOp
      | exact SolidityEmittableBuiltinOK.codecopyOp
      | exact SolidityEmittableBuiltinOK.codesizeOp
      | exact SolidityEmittableBuiltinOK.blockhashOp
      | exact SolidityEmittableBuiltinOK.balanceOp
      | exact SolidityEmittableBuiltinOK.extcodesizeOp
      | exact SolidityEmittableBuiltinOK.extcodehashOp
      | exact SolidityEmittableBuiltinOK.extcodecopyOp
      | exact SolidityEmittableBuiltinOK.blobhashOp
      | exact SolidityEmittableBuiltinOK.tloadOp
      | exact SolidityEmittableBuiltinOK.tstoreOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | exact FullYul.CompilerProfile.CurrentSolidCoreValue.word _
      | constructor
  · simp [solidityExpandedBuiltinProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      Relations.embedConcreteStmtsFuel, FullYul.checkBlockFuel,
      FullYul.predeclareBlockFunctionSigs?, FullYul.checkStmtExpr,
      FullYul.checkExprs, FullYul.checkExpr,
      FullYul.predeclareStmtFunctionSigs?, Evm.Builtin.signature?]

noncomputable def solidityExpandedBuiltinProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidityEmittable
      FullYul.StaticContext.empty solidityExpandedBuiltinProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidityEmittable
    FullYul.StaticContext.empty solidityExpandedBuiltinProgram_accepted

noncomputable def solidityExpandedBuiltinProgram_semanticBoundary :
    Relations.CurrentSolidityEmittableProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty solidityExpandedBuiltinProgram :=
  Relations.CurrentSolidityEmittableProgramSemanticBoundaryEvidence.ofAcceptedAt
    solidityExpandedBuiltinProgram_coverageEvidence

namespace SolidityLoweringEnvironmentBuiltinOK

theorem gasOp :
    FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
      Evm.Builtin.gasOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment]
  exact Or.inr FullYul.CompilerProfile.LoweringEnvironmentBuiltin.gasOp

theorem pcOp :
    FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
      Evm.Builtin.pcOp := by
  simp [FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment]
  exact Or.inr FullYul.CompilerProfile.LoweringEnvironmentBuiltin.pcOp

end SolidityLoweringEnvironmentBuiltinOK

def solidityLoweringEnvironmentProgram : ConcreteYul.Program :=
  { body :=
      ConcreteYul.Stmt.expr
        (ConcreteYul.Expr.builtin Evm.Builtin.sstore
          [ ConcreteYul.Expr.builtin Evm.Builtin.gasOp []
          , ConcreteYul.Expr.builtin Evm.Builtin.pcOp [] ]) }

theorem solidityLoweringEnvironmentProgram_runs :
    ConcreteYul.runProgramFuel hashByLength 4
        solidityLoweringEnvironmentProgram =
      some
        { flow := ConcreteYul.CompleteFlow.normal
          config :=
            { ConcreteYul.RuntimeConfig.empty with
              state :=
                { ConcreteYul.State.empty with
                  storage := [(0, [(0, 0)])] } } } := by
  rfl

theorem solidityLoweringEnvironmentProgram_accepted :
    Relations.CompilerAcceptedProgramAt
      FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment
      FullYul.StaticContext.empty solidityLoweringEnvironmentProgram := by
  refine ⟨4, FullYul.StaticContext.empty, ?_⟩
  constructor
  · simp [solidityLoweringEnvironmentProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel]
    repeat
      first
      | exact SolidityLoweringEnvironmentBuiltinOK.gasOp
      | exact SolidityLoweringEnvironmentBuiltinOK.pcOp
      | exact FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
      | constructor
  · simp [solidityLoweringEnvironmentProgram, Relations.embedConcreteStmt,
      Relations.embedConcreteStmtFuel, Relations.embedConcreteExpr,
      Relations.embedConcreteExprs, FullYul.checkStmtFuel,
      FullYul.checkStmtExpr, FullYul.checkExprs, FullYul.checkExpr,
      Evm.Builtin.signature?]

noncomputable def solidityLoweringEnvironmentProgram_coverageEvidence :
    Relations.CompilerAcceptedProgramAtCoverageEvidence
      FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment
      FullYul.StaticContext.empty solidityLoweringEnvironmentProgram :=
  Relations.CompilerAcceptedProgramAtCoverageEvidence.of_compilerAcceptedAt
    FullYul.CompilerProfile.currentSolidityEmittableWithLoweringEnvironment
    FullYul.StaticContext.empty
    solidityLoweringEnvironmentProgram_accepted

noncomputable def solidityLoweringEnvironmentProgram_semanticBoundary :
    Relations.CurrentSolidityEmittableWithLoweringEnvironmentProgramSemanticBoundaryEvidence
      FullYul.StaticContext.empty solidityLoweringEnvironmentProgram :=
  Relations.CurrentSolidityEmittableWithLoweringEnvironmentProgramSemanticBoundaryEvidence.ofAcceptedAt
    solidityLoweringEnvironmentProgram_coverageEvidence

end Fixtures
end SolidCoreYulCore
