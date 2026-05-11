import SolidCoreYulCore.FullYul

namespace SolidCoreYulCore
namespace SymYul

abbrev Value := FullYul.Value
abbrev Expr := FullYul.Expr
abbrev Stmt := FullYul.Stmt
abbrev Env := FullYul.Env
abbrev EvmState := FullYul.EvmState
abbrev FunctionEnv := FullYul.FunctionEnv
abbrev YulObject := FullYul.YulObject

def declareFunction (funcs : FunctionEnv) (name : FullYul.Name)
    (fn : FullYul.FunctionDef) : FunctionEnv :=
  match FullYul.lookupFunction? funcs name with
  | some _ => funcs
  | none => (name, fn) :: funcs

def collectStmtFunctionDefs : Stmt -> FunctionEnv -> FunctionEnv
  | FullYul.Stmt.funDef name params returns body, funcs =>
      declareFunction funcs name { params := params, returns := returns, body := body }
  | FullYul.Stmt.seq first second, funcs =>
      collectStmtFunctionDefs second (collectStmtFunctionDefs first funcs)
  | _, funcs => funcs

def collectBlockFunctionDefs : List Stmt -> FunctionEnv -> FunctionEnv
  | [], funcs => funcs
  | stmt :: rest, funcs =>
      collectBlockFunctionDefs rest (collectStmtFunctionDefs stmt funcs)

inductive Constraint where
  | eq : Value -> Value -> Constraint
  | ne : Value -> Value -> Constraint
  | iszero : Value -> Constraint
  | nonzero : Value -> Constraint
  deriving DecidableEq, Repr

structure ConcreteModel where
  hash : FullYul.SymbolicBytes -> Word := fun _ => 0
  dataOffset : FullYul.DataLabel -> Word := fun _ => 0
  memoryWord : Word -> Word := fun _ => 0
  memoryWordAt : Nat -> Word -> Word := fun _ _ => 0
  calldataWord : Word -> Word := fun _ => 0
  returndataWord : Word -> Word := fun _ => 0
  returndataWordAt : Nat -> Word -> Word := fun _ _ => 0
  storageWord : Word -> Word -> Word := fun _ _ => 0
  transientWord : Word -> Word -> Word := fun _ _ => 0
  callSuccess : Nat -> Word := fun _ => 1
  unaryBuiltin : Evm.Builtin -> Word -> Word := fun _ _ => 0
  binaryBuiltin : Evm.Builtin -> Word -> Word -> Word := fun _ _ _ => 0
  ternaryBuiltin : Evm.Builtin -> Word -> Word -> Word -> Word :=
    fun _ _ _ _ => 0

def ConcreteModel.zero : ConcreteModel := {}

def ConcreteModel.withCalldata0 (value : Word) : ConcreteModel :=
  { ConcreteModel.zero with
    calldataWord := fun offset =>
      if norm offset = 0 then norm value else 0 }

def interpValue (model : ConcreteModel) : Value -> Word
  | FullYul.Value.word value => norm value
  | FullYul.Value.symbolicHash bytes => norm (model.hash bytes)
  | FullYul.Value.dataOffset label => norm (model.dataOffset label)
  | FullYul.Value.memoryWord offset => norm (model.memoryWord offset)
  | FullYul.Value.memoryWordAt version offset =>
      norm (model.memoryWordAt version offset)
  | FullYul.Value.calldataWord offset => norm (model.calldataWord offset)
  | FullYul.Value.returndataWord offset => norm (model.returndataWord offset)
  | FullYul.Value.returndataWordAt id offset =>
      norm (model.returndataWordAt id offset)
  | FullYul.Value.storageWord address key =>
      norm (model.storageWord (norm address) (interpValue model key))
  | FullYul.Value.transientWord address key =>
      norm (model.transientWord (norm address) (interpValue model key))
  | FullYul.Value.callSuccess id => norm (model.callSuccess id)
  | FullYul.Value.unaryBuiltin builtin arg =>
      norm (model.unaryBuiltin builtin (interpValue model arg))
  | FullYul.Value.binaryBuiltin builtin lhs rhs =>
      norm
        (model.binaryBuiltin builtin (interpValue model lhs)
          (interpValue model rhs))
  | FullYul.Value.ternaryBuiltin builtin first second third =>
      norm
        (model.ternaryBuiltin builtin (interpValue model first)
          (interpValue model second) (interpValue model third))

def holdsConstraint (model : ConcreteModel) : Constraint -> Prop
  | Constraint.eq lhs rhs =>
      norm (interpValue model lhs) = norm (interpValue model rhs)
  | Constraint.ne lhs rhs =>
      norm (interpValue model lhs) ≠ norm (interpValue model rhs)
  | Constraint.iszero value => norm (interpValue model value) = 0
  | Constraint.nonzero value => norm (interpValue model value) ≠ 0

def satisfies (model : ConcreteModel) (pc : List Constraint) : Prop :=
  ∀ constraint, constraint ∈ pc -> holdsConstraint model constraint

def guidedBool (model : ConcreteModel) (value : Value) : Bool :=
  if norm (interpValue model value) = 0 then false else true

structure Config where
  pc : List Constraint := []
  env : Env := []
  evm : EvmState := FullYul.EvmState.empty
  funcs : FunctionEnv := []
  object? : Option YulObject := none
  deriving Repr

def Config.empty : Config := {}

structure Result where
  flow : FullYul.Flow
  config : Config
  deriving Repr

def normalResult (config : Config) : Result :=
  { flow := FullYul.Flow.normal, config := config }

def resultAfterExpr (config : Config) : Result :=
  match config.evm.halt? with
  | some _ => { flow := FullYul.Flow.halted, config := config }
  | none => normalResult config

def knownEq? : Value -> Value -> Option Bool
  | FullYul.Value.word lhs, FullYul.Value.word rhs =>
      some (decide (norm lhs = norm rhs))
  | FullYul.Value.symbolicHash lhs, FullYul.Value.symbolicHash rhs =>
      some (decide (lhs = rhs))
  | lhs, rhs => if lhs = rhs then some true else none

def KnownEqSoundForModel (model : ConcreteModel) : Prop :=
  ∀ {lhs rhs : Value},
    knownEq? lhs rhs = some false ->
      norm (interpValue model lhs) ≠ norm (interpValue model rhs)

def HashInjectiveForModel (model : ConcreteModel) : Prop :=
  ∀ {lhs rhs : FullYul.SymbolicBytes},
    norm (model.hash lhs) = norm (model.hash rhs) -> lhs = rhs

def knownZero? : Value -> Option Bool
  | FullYul.Value.word value => some (decide (norm value = 0))
  | _ => none

def constraintsConflict (candidate : Constraint) : List Constraint -> Bool
  | [] => false
  | current :: rest =>
      let conflicts :=
        match candidate, current with
        | Constraint.eq lhs rhs, Constraint.ne lhs' rhs' =>
            (decide (lhs = lhs') && decide (rhs = rhs')) ||
              (decide (lhs = rhs') && decide (rhs = lhs'))
        | Constraint.ne lhs rhs, Constraint.eq lhs' rhs' =>
            (decide (lhs = lhs') && decide (rhs = rhs')) ||
              (decide (lhs = rhs') && decide (rhs = lhs'))
        | Constraint.iszero value, Constraint.nonzero value' =>
            decide (value = value')
        | Constraint.nonzero value, Constraint.iszero value' =>
            decide (value = value')
        | _, _ => false
      conflicts || constraintsConflict candidate rest

def addConstraint? (constraint : Constraint) (config : Config) :
    Option Config :=
  let known :=
    match constraint with
    | Constraint.eq lhs rhs => knownEq? lhs rhs
    | Constraint.ne lhs rhs => (knownEq? lhs rhs).map not
    | Constraint.iszero value => knownZero? value
    | Constraint.nonzero value => (knownZero? value).map not
  match known with
  | some true => some config
  | some false => none
  | none =>
      if constraintsConflict constraint config.pc then none
      else some { config with pc := constraint :: config.pc }

def addConstraints? : List Constraint -> Config -> Option Config
  | [], config => some config
  | constraint :: constraints, config =>
      match addConstraint? constraint config with
      | some config' => addConstraints? constraints config'
      | none => none

theorem knownEq?_true_holds {model : ConcreteModel} {lhs rhs : Value}
    (h : knownEq? lhs rhs = some true) :
    norm (interpValue model lhs) = norm (interpValue model rhs) := by
  cases lhs <;> cases rhs <;> simp [knownEq?, interpValue, norm] at h ⊢
  · exact h
  all_goals
    first
    | subst_vars; rfl
    | rcases h with ⟨h₁, h₂⟩
      cases h₁
      cases h₂
      rfl
    | rcases h with ⟨h₁, h₂, h₃⟩
      cases h₁
      cases h₂
      cases h₃
      rfl
    | rcases h with ⟨h₁, h₂, h₃, h₄⟩
      cases h₁
      cases h₂
      cases h₃
      cases h₄
      rfl

theorem knownEq?_false_holds
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {lhs rhs : Value}
    (h : knownEq? lhs rhs = some false) :
    norm (interpValue model lhs) ≠ norm (interpValue model rhs) :=
  hSound h

theorem knownEqSoundForModel_of_hash_injective
    {model : ConcreteModel}
    (hHash : HashInjectiveForModel model) :
    KnownEqSoundForModel model := by
  intro lhs rhs hKnown hEqual
  cases lhs <;> cases rhs <;>
    simp [knownEq?, interpValue, norm] at hKnown hEqual
  · exact hKnown hEqual
  exact hKnown (hHash hEqual)

theorem knownZero?_true_holds {model : ConcreteModel} {value : Value}
    (h : knownZero? value = some true) :
    norm (interpValue model value) = 0 := by
  cases value <;> simp [knownZero?] at h
  simpa [interpValue, norm, Nat.mod_mod] using h

theorem knownZero?_false_holds {model : ConcreteModel} {value : Value}
    (h : knownZero? value = some false) :
    norm (interpValue model value) ≠ 0 := by
  cases value <;> simp [knownZero?] at h
  simpa [interpValue, norm, Nat.mod_mod] using h

theorem constraintsConflict_false_of_satisfies
    {model : ConcreteModel} {candidate : Constraint} {pc : List Constraint}
    (hSat : satisfies model pc)
    (hCandidate : holdsConstraint model candidate) :
    constraintsConflict candidate pc = false := by
  induction pc with
  | nil => rfl
  | cons current rest ih =>
      have hCurrent : holdsConstraint model current :=
        hSat current (by simp)
      have hRestSat : satisfies model rest := by
        intro constraint hConstraint
        exact hSat constraint (by simp [hConstraint])
      have hRest := ih hRestSat
      cases candidate <;> cases current <;>
        simp [constraintsConflict, hRest, holdsConstraint] at hCandidate hCurrent ⊢
      · constructor
        · intro hLeft hRight
          cases hLeft
          cases hRight
          exact hCurrent hCandidate
        · intro hLeft hRight
          cases hLeft
          cases hRight
          exact hCurrent hCandidate.symm
      · constructor
        · intro hLeft hRight
          cases hLeft
          cases hRight
          exact hCandidate hCurrent
        · intro hLeft hRight
          cases hLeft
          cases hRight
          exact hCandidate hCurrent.symm
      · intro hEq
        cases hEq
        exact hCurrent hCandidate
      · intro hEq
        cases hEq
        exact hCandidate hCurrent

theorem satisfies_addConstraint?
    {model : ConcreteModel} {constraint : Constraint}
    {config config' : Config}
    (hSat : satisfies model config.pc)
    (hConstraint : holdsConstraint model constraint)
    (hAdd : addConstraint? constraint config = some config') :
    satisfies model config'.pc := by
  unfold addConstraint? at hAdd
  let known :=
    match constraint with
    | Constraint.eq lhs rhs => knownEq? lhs rhs
    | Constraint.ne lhs rhs => (knownEq? lhs rhs).map not
    | Constraint.iszero value => knownZero? value
    | Constraint.nonzero value => (knownZero? value).map not
  change
      (match known with
      | some true => some config
      | some false => none
      | none =>
          if constraintsConflict constraint config.pc then none
          else some { config with pc := constraint :: config.pc }) =
        some config' at hAdd
  cases hKnown : known with
  | some knownValue =>
      cases knownValue
      · simp [hKnown] at hAdd
      · simp [hKnown] at hAdd
        cases hAdd
        exact hSat
  | none =>
      simp [hKnown] at hAdd
      by_cases hConflict : constraintsConflict constraint config.pc
      · simp [hConflict] at hAdd
      · simp [hConflict] at hAdd
        cases hAdd
        intro current hCurrent
        simp at hCurrent
        rcases hCurrent with hEq | hOld
        · cases hEq
          exact hConstraint
        · exact hSat current hOld

theorem addConstraint?_some_of_satisfies
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {constraint : Constraint} {config : Config}
    (hSat : satisfies model config.pc)
    (hConstraint : holdsConstraint model constraint) :
    ∃ config',
      addConstraint? constraint config = some config' ∧
        satisfies model config'.pc := by
  have hNoConflict :
      constraintsConflict constraint config.pc = false :=
    constraintsConflict_false_of_satisfies hSat hConstraint
  cases constraint with
  | eq lhs rhs =>
      cases hKnown : knownEq? lhs rhs with
      | none =>
          let config' := { config with pc := Constraint.eq lhs rhs :: config.pc }
          have hAdd :
              addConstraint? (Constraint.eq lhs rhs) config = some config' := by
            simp [addConstraint?, hKnown, hNoConflict, config']
          exact
            ⟨config', hAdd,
              satisfies_addConstraint? hSat hConstraint hAdd⟩
      | some known =>
          cases known
          · have hNe := knownEq?_false_holds hSound hKnown
            have hEq :
                norm (interpValue model lhs) =
                  norm (interpValue model rhs) := by
              simpa [holdsConstraint] using hConstraint
            exact False.elim (hNe hEq)
          · have hAdd :
              addConstraint? (Constraint.eq lhs rhs) config = some config := by
              simp [addConstraint?, hKnown]
            exact ⟨config, hAdd, hSat⟩
  | ne lhs rhs =>
      cases hKnown : knownEq? lhs rhs with
      | none =>
          let config' := { config with pc := Constraint.ne lhs rhs :: config.pc }
          have hAdd :
              addConstraint? (Constraint.ne lhs rhs) config = some config' := by
            simp [addConstraint?, hKnown, hNoConflict, config']
          exact
            ⟨config', hAdd,
              satisfies_addConstraint? hSat hConstraint hAdd⟩
      | some known =>
          cases known
          · have hAdd :
              addConstraint? (Constraint.ne lhs rhs) config = some config := by
              simp [addConstraint?, hKnown]
            exact ⟨config, hAdd, hSat⟩
          · have hEq := knownEq?_true_holds (model := model) hKnown
            have hNe :
                norm (interpValue model lhs) ≠
                  norm (interpValue model rhs) := by
              simpa [holdsConstraint] using hConstraint
            exact False.elim (hNe hEq)
  | iszero value =>
      cases hKnown : knownZero? value with
      | none =>
          let config' := { config with pc := Constraint.iszero value :: config.pc }
          have hAdd :
              addConstraint? (Constraint.iszero value) config = some config' := by
            simp [addConstraint?, hKnown, hNoConflict, config']
          exact
            ⟨config', hAdd,
              satisfies_addConstraint? hSat hConstraint hAdd⟩
      | some known =>
          cases known
          · have hNe := knownZero?_false_holds (model := model) hKnown
            have hZero : norm (interpValue model value) = 0 := by
              simpa [holdsConstraint] using hConstraint
            exact False.elim (hNe hZero)
          · have hAdd :
              addConstraint? (Constraint.iszero value) config = some config := by
              simp [addConstraint?, hKnown]
            exact ⟨config, hAdd, hSat⟩
  | nonzero value =>
      cases hKnown : knownZero? value with
      | none =>
          let config' := { config with pc := Constraint.nonzero value :: config.pc }
          have hAdd :
              addConstraint? (Constraint.nonzero value) config = some config' := by
            simp [addConstraint?, hKnown, hNoConflict, config']
          exact
            ⟨config', hAdd,
              satisfies_addConstraint? hSat hConstraint hAdd⟩
      | some known =>
          cases known
          · have hAdd :
              addConstraint? (Constraint.nonzero value) config = some config := by
              simp [addConstraint?, hKnown]
            exact ⟨config, hAdd, hSat⟩
          · have hZero := knownZero?_true_holds (model := model) hKnown
            have hNonzero : norm (interpValue model value) ≠ 0 := by
              simpa [holdsConstraint] using hConstraint
            exact False.elim (hNonzero hZero)

theorem satisfies_addConstraints?
    {model : ConcreteModel} {constraints : List Constraint}
    {config config' : Config}
    (hSat : satisfies model config.pc)
    (hConstraints :
      ∀ constraint, constraint ∈ constraints ->
        holdsConstraint model constraint)
    (hAdd : addConstraints? constraints config = some config') :
    satisfies model config'.pc := by
  induction constraints generalizing config with
  | nil =>
      simp [addConstraints?] at hAdd
      cases hAdd
      exact hSat
  | cons constraint rest ih =>
      simp [addConstraints?] at hAdd
      cases hOne : addConstraint? constraint config with
      | none =>
          simp [hOne] at hAdd
      | some configAfterConstraint =>
          simp [hOne] at hAdd
          have hSatAfterConstraint :
              satisfies model configAfterConstraint.pc :=
            satisfies_addConstraint? hSat
              (hConstraints constraint (by simp)) hOne
          exact
            ih hSatAfterConstraint
              (by
                intro restConstraint hRest
                exact hConstraints restConstraint (by simp [hRest]))
              hAdd

theorem addConstraints?_some_of_satisfies
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {constraints : List Constraint} {config : Config}
    (hSat : satisfies model config.pc)
    (hConstraints :
      ∀ constraint, constraint ∈ constraints ->
        holdsConstraint model constraint) :
    ∃ config',
      addConstraints? constraints config = some config' ∧
        satisfies model config'.pc := by
  induction constraints generalizing config with
  | nil =>
      exact ⟨config, by simp [addConstraints?], hSat⟩
  | cons constraint rest ih =>
      rcases addConstraint?_some_of_satisfies hSound hSat
          (hConstraints constraint (by simp)) with
        ⟨configAfterConstraint, hAddConstraint, hSatAfterConstraint⟩
      have hRestConstraints :
          ∀ restConstraint, restConstraint ∈ rest ->
            holdsConstraint model restConstraint := by
        intro restConstraint hRest
        exact hConstraints restConstraint (by simp [hRest])
      rcases ih hSatAfterConstraint hRestConstraints with
        ⟨config', hAddRest, hSat'⟩
      exact
        ⟨config', by
          simp [addConstraints?, hAddConstraint, hAddRest], hSat'⟩

def branchOn (value : Value) (config : Config) : List (Bool × Config) :=
  match knownZero? value with
  | some true => [(false, config)]
  | some false => [(true, config)]
  | none =>
      let truePath := addConstraint? (Constraint.nonzero value) config
      let falsePath := addConstraint? (Constraint.iszero value) config
      (match truePath with
       | some cfg => [(true, cfg)]
       | none => []) ++
      (match falsePath with
       | some cfg => [(false, cfg)]
       | none => [])

theorem branchOn_true_exists_satisfies
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {config : Config}
    (hSat : satisfies model config.pc)
    (hValue : norm (interpValue model value) ≠ 0) :
    ∃ config',
      (true, config') ∈ branchOn value config ∧
        satisfies model config'.pc := by
  unfold branchOn
  cases hKnown : knownZero? value with
  | none =>
      rcases addConstraint?_some_of_satisfies
          (constraint := Constraint.nonzero value) hSound hSat
          (by simpa [holdsConstraint] using hValue) with
        ⟨config', hAdd, hSat'⟩
      cases hFalse :
          addConstraint? (Constraint.iszero value) config <;>
        exact ⟨config', by simp [hAdd], hSat'⟩
  | some known =>
      cases known
      · exact ⟨config, by simp, hSat⟩
      · have hZero := knownZero?_true_holds (model := model) hKnown
        exact False.elim (hValue hZero)

theorem branchOn_false_exists_satisfies
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {config : Config}
    (hSat : satisfies model config.pc)
    (hValue : norm (interpValue model value) = 0) :
    ∃ config',
      (false, config') ∈ branchOn value config ∧
        satisfies model config'.pc := by
  unfold branchOn
  cases hKnown : knownZero? value with
  | none =>
      rcases addConstraint?_some_of_satisfies
          (constraint := Constraint.iszero value) hSound hSat
          (by simpa [holdsConstraint] using hValue) with
        ⟨config', hAdd, hSat'⟩
      cases hTrue :
          addConstraint? (Constraint.nonzero value) config <;>
        exact ⟨config', by simp [hAdd], hSat'⟩
  | some known =>
      cases known
      · have hNonzero := knownZero?_false_holds (model := model) hKnown
        exact False.elim (hNonzero hValue)
      · exact ⟨config, by simp, hSat⟩

theorem branchOn_guidedBool_exists_satisfies
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {config : Config}
    (hSat : satisfies model config.pc) :
    ∃ config',
      (guidedBool model value, config') ∈ branchOn value config ∧
        satisfies model config'.pc := by
  by_cases hZero : norm (interpValue model value) = 0
  · simpa [guidedBool, hZero] using
      branchOn_false_exists_satisfies hSound hSat hZero
  · simpa [guidedBool, hZero] using
      branchOn_true_exists_satisfies hSound hSat hZero

theorem branchOn_true_satisfies
    {model : ConcreteModel} {value : Value}
    {config config' : Config}
    (hSat : satisfies model config.pc)
    (hValue : norm (interpValue model value) ≠ 0)
    (hBranch : (true, config') ∈ branchOn value config) :
    satisfies model config'.pc := by
  unfold branchOn at hBranch
  cases hKnown : knownZero? value with
  | none =>
      simp [hKnown] at hBranch
      cases hTrue :
          addConstraint? (Constraint.nonzero value) config with
      | none =>
          cases hFalse :
              addConstraint? (Constraint.iszero value) config <;>
            simp [hTrue, hFalse] at hBranch
      | some trueConfig =>
          cases hFalse :
              addConstraint? (Constraint.iszero value) config with
          | none =>
              simp [hTrue, hFalse] at hBranch
              cases hBranch
              exact
                satisfies_addConstraint? hSat
                  (by simpa [holdsConstraint] using hValue) hTrue
          | some falseConfig =>
              simp [hTrue, hFalse] at hBranch
              cases hBranch
              exact
                satisfies_addConstraint? hSat
                  (by simpa [holdsConstraint] using hValue) hTrue
  | some known =>
      cases known
      · simp [hKnown] at hBranch
        cases hBranch
        exact hSat
      · simp [hKnown] at hBranch

theorem branchOn_false_satisfies
    {model : ConcreteModel} {value : Value}
    {config config' : Config}
    (hSat : satisfies model config.pc)
    (hValue : norm (interpValue model value) = 0)
    (hBranch : (false, config') ∈ branchOn value config) :
    satisfies model config'.pc := by
  unfold branchOn at hBranch
  cases hKnown : knownZero? value with
  | none =>
      simp [hKnown] at hBranch
      cases hTrue :
          addConstraint? (Constraint.nonzero value) config with
      | none =>
          cases hFalse :
              addConstraint? (Constraint.iszero value) config with
          | none =>
              simp [hTrue, hFalse] at hBranch
          | some falseConfig =>
              simp [hTrue, hFalse] at hBranch
              cases hBranch
              exact
                satisfies_addConstraint? hSat
                  (by simpa [holdsConstraint] using hValue) hFalse
      | some trueConfig =>
          cases hFalse :
              addConstraint? (Constraint.iszero value) config with
          | none =>
              simp [hTrue, hFalse] at hBranch
          | some falseConfig =>
              simp [hTrue, hFalse] at hBranch
              cases hBranch
              exact
                satisfies_addConstraint? hSat
                  (by simpa [holdsConstraint] using hValue) hFalse
  | some known =>
      cases known
      · simp [hKnown] at hBranch
      · simp [hKnown] at hBranch
        cases hBranch
        exact hSat

mutual
  def evalExpr (config : Config) : Expr -> Option (Value × Config)
    | FullYul.Expr.value value => some (value, config)
    | FullYul.Expr.var name =>
        match FullYul.lookup? config.env name with
        | some value => some (value, config)
        | none => none
    | FullYul.Expr.keccak bytes => some (FullYul.symbolicKeccak bytes, config)
    | FullYul.Expr.dataSize label =>
        match config.object? with
        | some object =>
            match object.data? label with
            | some bytes =>
                some (FullYul.Value.word (FullYul.symbolicDataSize bytes), config)
            | none => none
        | none => none
    | FullYul.Expr.dataOffset label =>
        match config.object? with
        | some object =>
            match object.data? label with
            | some _ => some (FullYul.Value.dataOffset label, config)
            | none => none
        | none => none
    | FullYul.Expr.builtin builtin args =>
        match evalExprs config args with
        | some (values, config') =>
            match FullYul.evalEvmBuiltin builtin values config'.evm with
            | some (value, evm') => some (value, { config' with evm := evm' })
            | none => none
        | none => none

  def evalExprs (config : Config) :
      List Expr -> Option (List Value × Config)
    | [] => some ([], config)
    | expr :: rest =>
        match evalExprs config rest with
        | some (values, config') =>
            match evalExpr config' expr with
            | some (value, config'') => some (value :: values, config'')
            | none => none
        | none => none
end

def evalExprsAsYulValues (config : Config) (exprs : List Expr) :
    Option (List Value × Config) :=
  match exprs with
  | [FullYul.Expr.builtin builtin args] =>
      match builtin.signature? with
      | some sig =>
          if sig.resultCount = 1 then
            evalExprs config exprs
          else
            match evalExprs config args with
            | some (argValues, config') =>
                match FullYul.evalEvmBuiltinValues builtin argValues config'.evm with
                | some (values, evm') =>
                    some (values, { config' with evm := evm' })
                | none => none
            | none => none
      | none => evalExprs config exprs
  | _ => evalExprs config exprs

def restoreBlockConfig (outer : Config) (inner : Config) : Option Config :=
  match FullYul.restoreOuter outer.env inner.env with
  | some env' => some { inner with env := env', funcs := outer.funcs }
  | none => none

theorem restoreBlockConfig_preserves_path_and_evm
    {outer inner restored : Config}
    (h : restoreBlockConfig outer inner = some restored) :
    restored.pc = inner.pc ∧ restored.evm = inner.evm := by
  unfold restoreBlockConfig at h
  cases hRestore : FullYul.restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      constructor <;> rfl

theorem restoreBlockConfig_restores_outer_functions
    {outer inner restored : Config}
    (h : restoreBlockConfig outer inner = some restored) :
    restored.funcs = outer.funcs := by
  unfold restoreBlockConfig at h
  cases hRestore : FullYul.restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      rfl

def withRestoredConfig (outer : Config) (result : Result) :
    Option Result :=
  match restoreBlockConfig outer result.config with
  | some config' => some { flow := result.flow, config := config' }
  | none => none

theorem withRestoredConfig_preserves_path_and_evm
    {outer : Config} {result restored : Result}
    (h : withRestoredConfig outer result = some restored) :
    restored.config.pc = result.config.pc ∧
      restored.config.evm = result.config.evm := by
  unfold withRestoredConfig at h
  cases hRestore : restoreBlockConfig outer result.config with
  | none =>
      simp [hRestore] at h
  | some config' =>
      simp [hRestore] at h
      cases h
      exact restoreBlockConfig_preserves_path_and_evm hRestore


def returnValues? (returns : List FullYul.Name) (result : Result) :
    Option (List Value × Config) :=
  match result.flow with
  | FullYul.Flow.normal =>
      match FullYul.valuesForNames? result.config.env returns with
      | some values => some (values, result.config)
      | none => none
  | FullYul.Flow.left =>
      match FullYul.valuesForNames? result.config.env returns with
      | some values => some (values, result.config)
      | none => none
  | _ => none

def bindNormal (results : List Result) (next : Config -> List Result) :
    List Result :=
  List.flatMap
    (fun result =>
      match result.flow with
      | FullYul.Flow.normal => next result.config
      | _ => [result])
    results

def switchBranches (value : Value) : List (Value × Stmt) -> Option Stmt ->
    List (Stmt × List Constraint)
  | [], some defaultBranch => [(defaultBranch, [])]
  | [], none => []
  | (label, branch) :: rest, defaultBranch =>
      (branch, [Constraint.eq value label]) ::
        (switchBranches value rest defaultBranch).map
          (fun (stmt, constraints) =>
            (stmt, Constraint.ne value label :: constraints))

def switchFallthroughConstraints (value : Value) :
    List (Value × Stmt) -> Option Stmt -> List (List Constraint)
  | [], none => [[]]
  | [], some _ => []
  | (label, _) :: rest, defaultBranch =>
      (switchFallthroughConstraints value rest defaultBranch).map
        (fun constraints => Constraint.ne value label :: constraints)

mutual
  def evalStmtFuel : Nat -> Config -> Stmt -> List Result
    | 0, _, _ => []
    | _fuel + 1, config, FullYul.Stmt.skip => [normalResult config]
    | _fuel + 1, config, FullYul.Stmt.expr expr =>
        match evalExpr config expr with
        | some (_, config') => [resultAfterExpr config']
        | none => []
    | _fuel + 1, config, FullYul.Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr config expr with
            | some (value, config') =>
                match FullYul.declare? config'.env name value with
                | some env' => [normalResult { config' with env := env' }]
                | none => []
            | none => []
        | none =>
            match FullYul.declare? config.env name (FullYul.Value.word 0) with
            | some env' => [normalResult { config with env := env' }]
            | none => []
    | _fuel + 1, config, FullYul.Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprsAsYulValues config exprs with
            | some (values, config') =>
                match FullYul.declareMany? config'.env names values with
                | some env' => [normalResult { config' with env := env' }]
                | none => []
            | none => []
        | none =>
            match FullYul.declareMany? config.env names
                (names.map (fun _ => FullYul.Value.word 0)) with
            | some env' => [normalResult { config with env := env' }]
            | none => []
    | _fuel + 1, config, FullYul.Stmt.funDef fnName params returns body =>
        [normalResult
          { config with
            funcs :=
              declareFunction config.funcs fnName
                { params := params, returns := returns, body := body } }]
    | _fuel + 1, config, FullYul.Stmt.assign name expr =>
        match evalExpr config expr with
        | some (value, config') =>
            match FullYul.assign? config'.env name value with
            | some env' => [normalResult { config' with env := env' }]
            | none => []
        | none => []
    | _fuel + 1, config, FullYul.Stmt.assignMany names exprs =>
        match evalExprsAsYulValues config exprs with
        | some (values, config') =>
            match FullYul.assignMany? config'.env names values with
            | some env' => [normalResult { config' with env := env' }]
            | none => []
        | none => []
    | fuel + 1, config, FullYul.Stmt.letCall names fnName args =>
        match evalExprs config args with
        | some (argValues, config') =>
            List.flatMap
              (fun (returnValues, afterCallConfig) =>
                match FullYul.declareMany?
                    afterCallConfig.env names returnValues with
                | some env' =>
                    [normalResult { afterCallConfig with env := env' }]
                | none => [])
              (evalFunctionFuel fuel config' fnName argValues)
        | none => []
    | fuel + 1, config, FullYul.Stmt.assignCall names fnName args =>
        match evalExprs config args with
        | some (argValues, config') =>
            List.flatMap
              (fun (returnValues, afterCallConfig) =>
                match FullYul.assignMany?
                    afterCallConfig.env names returnValues with
                | some env' =>
                    [normalResult { afterCallConfig with env := env' }]
                | none => [])
              (evalFunctionFuel fuel config' fnName argValues)
        | none => []
    | fuel + 1, config, FullYul.Stmt.seq first second =>
        let config :=
          { config with
            funcs := collectStmtFunctionDefs (FullYul.Stmt.seq first second)
              config.funcs }
        bindNormal (evalStmtFuel fuel config first)
          (fun config' => evalStmtFuel fuel config' second)
    | fuel + 1, config, FullYul.Stmt.block stmts =>
        let blockConfig :=
          { config with funcs := collectBlockFunctionDefs stmts config.funcs }
        (evalBlockFuel fuel blockConfig stmts).filterMap
          (fun result => withRestoredConfig config result)
    | fuel + 1, config, FullYul.Stmt.ifThen cond body =>
        match evalExpr config cond with
        | some (value, config') =>
            List.flatMap
              (fun (takeBranch, branchConfig) =>
                if takeBranch then evalStmtFuel fuel branchConfig body
                else [normalResult branchConfig])
              (branchOn value config')
        | none => []
    | fuel + 1, config, FullYul.Stmt.switch discr cases defaultBranch =>
        match evalExpr config discr with
        | some (value, config') =>
            let branchResults :=
              List.flatMap
                (fun (branch, constraints) =>
                  match addConstraints? constraints config' with
                  | some branchConfig => evalStmtFuel fuel branchConfig branch
                  | none => [])
                (switchBranches value cases defaultBranch)
            let fallthroughResults :=
              List.flatMap
                (fun constraints =>
                  match addConstraints? constraints config' with
                  | some branchConfig => [normalResult branchConfig]
                  | none => [])
                (switchFallthroughConstraints value cases defaultBranch)
            branchResults ++ fallthroughResults
        | none => []
    | fuel + 1, config, FullYul.Stmt.forLoop pre cond post body =>
        List.flatMap
          (fun preResult =>
            match preResult.flow with
            | FullYul.Flow.normal =>
                evalForFuel fuel config preResult.config cond post body
            | _ =>
                match withRestoredConfig config preResult with
                | some restored => [restored]
                | none => [])
          (evalStmtFuel fuel config pre)
    | _fuel + 1, config, FullYul.Stmt.break =>
        [{ flow := FullYul.Flow.broke, config := config }]
    | _fuel + 1, config, FullYul.Stmt.continue =>
        [{ flow := FullYul.Flow.continued, config := config }]
    | _fuel + 1, config, FullYul.Stmt.leave =>
        [{ flow := FullYul.Flow.left, config := config }]

  def evalBlockFuel : Nat -> Config -> List Stmt -> List Result
    | 0, _, _ => []
    | _fuel + 1, config, [] => [normalResult config]
    | fuel + 1, config, stmt :: rest =>
        bindNormal (evalStmtFuel fuel config stmt)
          (fun config' => evalBlockFuel fuel config' rest)

  def evalForFuel : Nat -> Config -> Config -> Expr -> Stmt -> Stmt ->
      List Result
    | 0, _, _, _, _, _ => []
    | fuel + 1, outer, loopConfig, cond, post, body =>
        match evalExpr loopConfig cond with
        | some (value, condConfig) =>
            List.flatMap
              (fun (takeBranch, branchConfig) =>
                if takeBranch then
                  List.flatMap
                    (fun bodyResult =>
                      match bodyResult.flow with
                      | FullYul.Flow.normal
                      | FullYul.Flow.continued =>
                          List.flatMap
                            (fun postResult =>
                              match postResult.flow with
                              | FullYul.Flow.normal
                              | FullYul.Flow.continued =>
                                  evalForFuel fuel outer postResult.config
                                    cond post body
                              | FullYul.Flow.broke =>
                                  match restoreBlockConfig outer postResult.config with
                                  | some restored => [normalResult restored]
                                  | none => []
                              | FullYul.Flow.left =>
                                  match restoreBlockConfig outer postResult.config with
                                  | some restored =>
                                      [{ flow := FullYul.Flow.left
                                         config := restored }]
                                  | none => []
                              | FullYul.Flow.halted =>
                                  match restoreBlockConfig outer postResult.config with
                                  | some restored =>
                                      [{ flow := FullYul.Flow.halted
                                         config := restored }]
                                  | none => [])
                            (evalStmtFuel fuel bodyResult.config post)
                      | FullYul.Flow.broke =>
                          match restoreBlockConfig outer bodyResult.config with
                          | some restored => [normalResult restored]
                          | none => []
                      | FullYul.Flow.left =>
                          match restoreBlockConfig outer bodyResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.left, config := restored }]
                          | none => []
                      | FullYul.Flow.halted =>
                          match restoreBlockConfig outer bodyResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.halted, config := restored }]
                          | none => [])
                    (evalStmtFuel fuel branchConfig body)
                else
                  match restoreBlockConfig outer branchConfig with
                  | some restored => [normalResult restored]
                  | none => [])
              (branchOn value condConfig)
        | none => []

  def evalFunctionFuel : Nat -> Config -> FullYul.Name -> List Value ->
      List (List Value × Config)
    | 0, _, _, _ => []
    | fuel + 1, config, fnName, args =>
        match FullYul.lookupFunction? config.funcs fnName with
        | some fn =>
            match FullYul.initFunctionEnv fn.params args fn.returns with
            | some callEnv =>
                let callConfig :=
                  { config with
                    env := callEnv
                    funcs := collectStmtFunctionDefs fn.body config.funcs }
                List.flatMap
                  (fun result =>
                    match returnValues? fn.returns result with
                    | some (values, resultConfig) =>
                        [ (values,
                            { resultConfig with
                              env := config.env
                              funcs := config.funcs }) ]
                    | none => [])
                  (evalStmtFuel fuel callConfig fn.body)
            | none => []
        | none => []
end

structure GuidedConfig where
  env : Env := []
  evm : EvmState := FullYul.EvmState.empty
  funcs : FunctionEnv := []
  object? : Option YulObject := none
  deriving Repr

def GuidedConfig.empty : GuidedConfig := {}

structure GuidedResult where
  flow : FullYul.Flow
  config : GuidedConfig
  deriving Repr

def guidedNormalResult (config : GuidedConfig) : GuidedResult :=
  { flow := FullYul.Flow.normal, config := config }

def guidedResultAfterExpr (config : GuidedConfig) : GuidedResult :=
  match config.evm.halt? with
  | some _ => { flow := FullYul.Flow.halted, config := config }
  | none => guidedNormalResult config

def erasePC (config : Config) : GuidedConfig :=
  { env := config.env
    evm := config.evm
    funcs := config.funcs
    object? := config.object? }

theorem addConstraint?_erasePC
    {constraint : Constraint} {config config' : Config}
    (h : addConstraint? constraint config = some config') :
    erasePC config' = erasePC config := by
  unfold addConstraint? at h
  cases constraint <;>
    simp [erasePC] at h ⊢
  all_goals
    repeat (split at h <;> simp at h)
  all_goals
    cases h
    subst_vars
    repeat constructor
    all_goals rfl

theorem addConstraints?_erasePC
    {constraints : List Constraint} {config config' : Config}
    (h : addConstraints? constraints config = some config') :
    erasePC config' = erasePC config := by
  induction constraints generalizing config with
  | nil =>
      simp [addConstraints?] at h
      cases h
      rfl
  | cons constraint rest ih =>
      simp [addConstraints?] at h
      cases hOne : addConstraint? constraint config with
      | none =>
          simp [hOne] at h
      | some configAfterConstraint =>
          simp [hOne] at h
          exact Eq.trans (ih h) (addConstraint?_erasePC hOne)

theorem branchOn_mem_erasePC
    {value : Value} {config config' : Config} {takeBranch : Bool}
    (h : (takeBranch, config') ∈ branchOn value config) :
    erasePC config' = erasePC config := by
  unfold branchOn at h
  cases hKnown : knownZero? value with
  | some known =>
      cases known <;> simp [hKnown] at h <;>
        rcases h with ⟨_, hConfig⟩ <;>
        cases hConfig <;>
        rfl
  | none =>
      cases hTrue : addConstraint? (Constraint.nonzero value) config with
      | none =>
          cases hFalse : addConstraint? (Constraint.iszero value) config with
          | none =>
              simp [hKnown, hTrue, hFalse] at h
          | some falseConfig =>
              simp [hKnown, hTrue, hFalse] at h
              rcases h with ⟨_, hConfig⟩
              cases hConfig
              exact addConstraint?_erasePC hFalse
      | some trueConfig =>
          cases hFalse : addConstraint? (Constraint.iszero value) config with
          | none =>
              simp [hKnown, hTrue, hFalse] at h
              rcases h with ⟨_, hConfig⟩
              cases hConfig
              exact addConstraint?_erasePC hTrue
          | some falseConfig =>
              simp [hKnown, hTrue, hFalse] at h
              rcases h with hTrueMem | hFalseMem
              · rcases hTrueMem with ⟨_, hConfig⟩
                cases hConfig
                exact addConstraint?_erasePC hTrue
              · rcases hFalseMem with ⟨_, hConfig⟩
                cases hConfig
                exact addConstraint?_erasePC hFalse

theorem branchOn_guidedBool_exists_satisfies_erasePC
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {config : Config}
    (hSat : satisfies model config.pc) :
    ∃ config',
      (guidedBool model value, config') ∈ branchOn value config ∧
        satisfies model config'.pc ∧
        erasePC config' = erasePC config := by
  rcases branchOn_guidedBool_exists_satisfies hSound hSat with
    ⟨config', hMem, hSat'⟩
  exact ⟨config', hMem, hSat', branchOn_mem_erasePC hMem⟩

def eraseResult (result : Result) : GuidedResult :=
  { flow := result.flow, config := erasePC result.config }

def GuidedResultCovered
    (model : ConcreteModel) (guided : GuidedResult) (results : List Result) :
    Prop :=
  ∃ result,
    result ∈ results ∧
      eraseResult result = guided ∧
      satisfies model result.config.pc

theorem guidedResultCovered_singleton
    {model : ConcreteModel} {result : Result}
    (hSat : satisfies model result.config.pc) :
    GuidedResultCovered model (eraseResult result) [result] := by
  exact ⟨result, by simp, rfl, hSat⟩

mutual
  def guidedEvalExpr (config : GuidedConfig) :
      Expr -> Option (Value × GuidedConfig)
    | FullYul.Expr.value value => some (value, config)
    | FullYul.Expr.var name =>
        match FullYul.lookup? config.env name with
        | some value => some (value, config)
        | none => none
    | FullYul.Expr.keccak bytes => some (FullYul.symbolicKeccak bytes, config)
    | FullYul.Expr.dataSize label =>
        match config.object? with
        | some object =>
            match object.data? label with
            | some bytes =>
                some (FullYul.Value.word (FullYul.symbolicDataSize bytes), config)
            | none => none
        | none => none
    | FullYul.Expr.dataOffset label =>
        match config.object? with
        | some object =>
            match object.data? label with
            | some _ => some (FullYul.Value.dataOffset label, config)
            | none => none
        | none => none
    | FullYul.Expr.builtin builtin args =>
        match guidedEvalExprs config args with
        | some (values, config') =>
            match FullYul.evalEvmBuiltin builtin values config'.evm with
            | some (value, evm') => some (value, { config' with evm := evm' })
            | none => none
        | none => none

  def guidedEvalExprs (config : GuidedConfig) :
      List Expr -> Option (List Value × GuidedConfig)
    | [] => some ([], config)
    | expr :: rest =>
        match guidedEvalExprs config rest with
        | some (values, config') =>
            match guidedEvalExpr config' expr with
            | some (value, config'') => some (value :: values, config'')
            | none => none
        | none => none
end

def guidedEvalExprsAsYulValues (config : GuidedConfig) (exprs : List Expr) :
    Option (List Value × GuidedConfig) :=
  match exprs with
  | [FullYul.Expr.builtin builtin args] =>
      match builtin.signature? with
      | some sig =>
          if sig.resultCount = 1 then
            guidedEvalExprs config exprs
          else
            match guidedEvalExprs config args with
            | some (argValues, config') =>
                match FullYul.evalEvmBuiltinValues builtin argValues config'.evm with
                | some (values, evm') =>
                    some (values, { config' with evm := evm' })
                | none => none
            | none => none
      | none => guidedEvalExprs config exprs
  | _ => guidedEvalExprs config exprs

def restoreGuidedBlockConfig (outer : GuidedConfig) (inner : GuidedConfig) :
    Option GuidedConfig :=
  match FullYul.restoreOuter outer.env inner.env with
  | some env' => some { inner with env := env', funcs := outer.funcs }
  | none => none

theorem restoreGuidedBlockConfig_preserves_evm
    {outer inner restored : GuidedConfig}
    (h : restoreGuidedBlockConfig outer inner = some restored) :
    restored.evm = inner.evm := by
  unfold restoreGuidedBlockConfig at h
  cases hRestore : FullYul.restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      rfl

def withRestoredGuidedConfig (outer : GuidedConfig)
    (result : GuidedResult) : Option GuidedResult :=
  match restoreGuidedBlockConfig outer result.config with
  | some config' => some { flow := result.flow, config := config' }
  | none => none

theorem withRestoredGuidedConfig_preserves_evm
    {outer : GuidedConfig} {result restored : GuidedResult}
    (h : withRestoredGuidedConfig outer result = some restored) :
    restored.config.evm = result.config.evm := by
  unfold withRestoredGuidedConfig at h
  cases hRestore : restoreGuidedBlockConfig outer result.config with
  | none =>
      simp [hRestore] at h
  | some config' =>
      simp [hRestore] at h
      cases h
      exact restoreGuidedBlockConfig_preserves_evm hRestore

theorem restoreGuidedBlockConfig_erasePC_of_restoreBlockConfig
    {outer inner restored : Config}
    (h : restoreBlockConfig outer inner = some restored) :
    restoreGuidedBlockConfig (erasePC outer) (erasePC inner) =
      some (erasePC restored) := by
  unfold restoreBlockConfig at h
  cases hRestore : FullYul.restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      simp [restoreGuidedBlockConfig, erasePC, hRestore]

theorem restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
    {outer inner : Config} {restoredGuided : GuidedConfig}
    (h :
      restoreGuidedBlockConfig (erasePC outer) (erasePC inner) =
        some restoredGuided) :
    ∃ restored,
      restoreBlockConfig outer inner = some restored ∧
        erasePC restored = restoredGuided := by
  unfold restoreGuidedBlockConfig at h
  cases hRestore : FullYul.restoreOuter outer.env inner.env with
  | none =>
      simp [erasePC, hRestore] at h
  | some restoredEnv =>
      simp [erasePC, hRestore] at h
      cases h
      exact
        ⟨{ inner with env := restoredEnv, funcs := outer.funcs },
          by simp [restoreBlockConfig, hRestore],
          by simp [erasePC]⟩

theorem withRestoredConfig_preserves_satisfies
    {model : ConcreteModel} {outer : Config} {result restored : Result}
    (hSat : satisfies model result.config.pc)
    (hRestore : withRestoredConfig outer result = some restored) :
    satisfies model restored.config.pc := by
  have hPath := (withRestoredConfig_preserves_path_and_evm hRestore).1
  simpa [hPath] using hSat

theorem withRestoredGuidedConfig_sound
    {model : ConcreteModel} {outer : Config}
    {guidedResult guidedRestored : GuidedResult} {results : List Result}
    (hCovered : GuidedResultCovered model guidedResult results)
    (hGuided :
      withRestoredGuidedConfig (erasePC outer) guidedResult =
        some guidedRestored) :
    GuidedResultCovered model guidedRestored
      (results.filterMap (fun result => withRestoredConfig outer result)) := by
  rcases hCovered with ⟨result, hMem, hErase, hSat⟩
  rcases result with ⟨flow, config⟩
  rcases guidedResult with ⟨guidedFlow, guidedConfig⟩
  simp [eraseResult] at hErase
  rcases hErase with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  unfold withRestoredGuidedConfig at hGuided
  cases hRestore : FullYul.restoreOuter outer.env config.env with
  | none =>
      simp [restoreGuidedBlockConfig, erasePC, hRestore] at hGuided
  | some env' =>
      simp [restoreGuidedBlockConfig, erasePC, hRestore] at hGuided
      cases hGuided
      let restored : Result :=
        { flow := flow
          config := { config with env := env', funcs := outer.funcs } }
      have hRestoreConcrete :
          withRestoredConfig outer { flow := flow, config := config } =
            some restored := by
        simp [withRestoredConfig, restoreBlockConfig, hRestore, restored]
      have hSatRestored : satisfies model restored.config.pc :=
        withRestoredConfig_preserves_satisfies hSat hRestoreConcrete
      exact
        ⟨restored,
          by
            exact List.mem_filterMap.mpr
              ⟨{ flow := flow, config := config }, hMem, hRestoreConcrete⟩,
          by
            simp [restored, eraseResult, erasePC],
          hSatRestored⟩

def guidedReturnValues? (returns : List FullYul.Name)
    (result : GuidedResult) : Option (List Value × GuidedConfig) :=
  match result.flow with
  | FullYul.Flow.normal =>
      match FullYul.valuesForNames? result.config.env returns with
      | some values => some (values, result.config)
      | none => none
  | FullYul.Flow.left =>
      match FullYul.valuesForNames? result.config.env returns with
      | some values => some (values, result.config)
      | none => none
  | _ => none

theorem guidedReturnValues?_sound
    {model : ConcreteModel} {returns : List FullYul.Name}
    {guidedResult : GuidedResult} {values : List Value}
    {guidedConfig : GuidedConfig} {results : List Result}
    (hCovered : GuidedResultCovered model guidedResult results)
    (hReturn :
      guidedReturnValues? returns guidedResult =
        some (values, guidedConfig)) :
    ∃ resultConfig,
      (values, resultConfig) ∈
          results.filterMap (fun result => returnValues? returns result) ∧
        erasePC resultConfig = guidedConfig ∧
        satisfies model resultConfig.pc := by
  rcases hCovered with ⟨result, hMem, hErase, hSat⟩
  rcases result with ⟨flow, config⟩
  rcases guidedResult with ⟨guidedFlow, guidedConfig'⟩
  simp [eraseResult] at hErase
  rcases hErase with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  cases flow <;> simp [guidedReturnValues?, erasePC] at hReturn
  · cases hValues : FullYul.valuesForNames? config.env returns with
    | none =>
        simp [hValues] at hReturn
    | some returnedValues =>
        simp [hValues] at hReturn
        rcases hReturn with ⟨hValuesEq, hConfigEq⟩
        cases hValuesEq
        cases hConfigEq
        exact
          ⟨config,
            List.mem_filterMap.mpr
              ⟨{ flow := FullYul.Flow.normal, config := config }, hMem,
                by simp [returnValues?, hValues]⟩,
            rfl,
            hSat⟩
  · cases hValues : FullYul.valuesForNames? config.env returns with
    | none =>
        simp [hValues] at hReturn
    | some returnedValues =>
        simp [hValues] at hReturn
        rcases hReturn with ⟨hValuesEq, hConfigEq⟩
        cases hValuesEq
        cases hConfigEq
        exact
          ⟨config,
            List.mem_filterMap.mpr
              ⟨{ flow := FullYul.Flow.left, config := config }, hMem,
                by simp [returnValues?, hValues]⟩,
            rfl,
            hSat⟩

def guidedBindNormal (result : Option GuidedResult)
    (next : GuidedConfig -> Option GuidedResult) : Option GuidedResult :=
  match result with
  | some { flow := FullYul.Flow.normal, config := config } => next config
  | some result => some result
  | none => none

theorem guidedBindNormal_some_non_normal
    {result : GuidedResult}
    {next : GuidedConfig -> Option GuidedResult}
    (hFlow : result.flow ≠ FullYul.Flow.normal) :
    guidedBindNormal (some result) next = some result := by
  rcases result with ⟨flow, config⟩
  cases flow with
  | normal => exact False.elim (hFlow rfl)
  | broke => simp [guidedBindNormal]
  | continued => simp [guidedBindNormal]
  | left => simp [guidedBindNormal]
  | halted => simp [guidedBindNormal]

theorem guidedBindNormal_sound
    {model : ConcreteModel} {guidedResult guidedResult' : GuidedResult}
    {results : List Result}
    {nextGuided : GuidedConfig -> Option GuidedResult}
    {nextResults : Config -> List Result}
    (hCovered : GuidedResultCovered model guidedResult results)
    (hNext :
      ∀ {config guidedResult'},
        satisfies model config.pc ->
          nextGuided (erasePC config) = some guidedResult' ->
          GuidedResultCovered model guidedResult' (nextResults config))
    (hGuided :
      guidedBindNormal (some guidedResult) nextGuided = some guidedResult') :
    GuidedResultCovered model guidedResult'
      (bindNormal results nextResults) := by
  rcases hCovered with ⟨result, hMem, hErase, hSat⟩
  rcases result with ⟨flow, config⟩
  rcases guidedResult with ⟨guidedFlow, guidedConfig⟩
  simp [eraseResult] at hErase
  rcases hErase with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  cases flow <;> simp [guidedBindNormal] at hGuided
  · rcases hNext hSat hGuided with
      ⟨nextResult, hNextMem, hNextErase, hNextSat⟩
    exact
      ⟨nextResult,
        by
          unfold bindNormal
          exact List.mem_flatMap.mpr
            ⟨{ flow := FullYul.Flow.normal, config := config }, hMem,
              by simp [hNextMem]⟩,
        hNextErase,
        hNextSat⟩
  · cases hGuided
    exact
      ⟨{ flow := FullYul.Flow.broke, config := config },
        by
          unfold bindNormal
          exact List.mem_flatMap.mpr
            ⟨{ flow := FullYul.Flow.broke, config := config }, hMem, by simp⟩,
        rfl,
        hSat⟩
  · cases hGuided
    exact
      ⟨{ flow := FullYul.Flow.continued, config := config },
        by
          unfold bindNormal
          exact List.mem_flatMap.mpr
            ⟨{ flow := FullYul.Flow.continued, config := config }, hMem, by simp⟩,
        rfl,
        hSat⟩
  · cases hGuided
    exact
      ⟨{ flow := FullYul.Flow.left, config := config },
        by
          unfold bindNormal
          exact List.mem_flatMap.mpr
            ⟨{ flow := FullYul.Flow.left, config := config }, hMem, by simp⟩,
        rfl,
        hSat⟩
  · cases hGuided
    exact
      ⟨{ flow := FullYul.Flow.halted, config := config },
        by
          unfold bindNormal
          exact List.mem_flatMap.mpr
            ⟨{ flow := FullYul.Flow.halted, config := config }, hMem, by simp⟩,
        rfl,
        hSat⟩

def guidedSwitchTarget? (model : ConcreteModel) (value : Value) :
    List (Value × Stmt) -> Option Stmt -> Option Stmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      if norm (interpValue model value) = norm (interpValue model label) then
        some branch
      else
        guidedSwitchTarget? model value rest defaultBranch

theorem guidedSwitchTarget?_some_mem_switchBranches
    {model : ConcreteModel} {value : Value}
    {cases : List (Value × Stmt)} {defaultBranch : Option Stmt}
    {target : Stmt}
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = some target) :
    ∃ constraints,
      (target, constraints) ∈ switchBranches value cases defaultBranch ∧
        ∀ constraint, constraint ∈ constraints ->
          holdsConstraint model constraint := by
  induction cases generalizing target defaultBranch with
  | nil =>
      cases defaultBranch with
      | none =>
          simp [guidedSwitchTarget?] at hTarget
      | some defaultStmt =>
          simp [guidedSwitchTarget?] at hTarget
          cases hTarget
          exact
            ⟨[]
            , by simp [switchBranches]
            , by simp⟩
  | cons head rest ih =>
      rcases head with ⟨label, branch⟩
      by_cases hMatch :
          norm (interpValue model value) =
            norm (interpValue model label)
      · simp [guidedSwitchTarget?, hMatch] at hTarget
        cases hTarget
        exact
          ⟨[Constraint.eq value label]
          , by simp [switchBranches]
          , by
              intro constraint hConstraint
              simp at hConstraint
              cases hConstraint
              simp [holdsConstraint, hMatch]⟩
      · have hRestTarget :
            guidedSwitchTarget? model value rest defaultBranch =
              some target := by
          simpa [guidedSwitchTarget?, hMatch] using hTarget
        rcases ih hRestTarget with
          ⟨constraints, hMem, hConstraints⟩
        exact
          ⟨Constraint.ne value label :: constraints
          , by simp [switchBranches, hMem]
          , by
              intro constraint hConstraint
              simp at hConstraint
              rcases hConstraint with hEq | hOld
              · cases hEq
                simpa [holdsConstraint] using hMatch
              · exact hConstraints constraint hOld⟩

theorem guidedSwitchTarget?_some_addConstraints_satisfies
    {model : ConcreteModel} {value : Value}
    {cases : List (Value × Stmt)} {defaultBranch : Option Stmt}
    {target : Stmt} {config : Config}
    (hSat : satisfies model config.pc)
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = some target) :
    ∃ constraints,
      (target, constraints) ∈ switchBranches value cases defaultBranch ∧
        ∀ {config'},
          addConstraints? constraints config = some config' ->
            satisfies model config'.pc := by
  rcases guidedSwitchTarget?_some_mem_switchBranches hTarget with
    ⟨constraints, hMem, hConstraints⟩
  exact
    ⟨constraints, hMem, by
      intro config' hAdd
      exact satisfies_addConstraints? hSat hConstraints hAdd⟩

theorem guidedSwitchTarget?_some_addConstraints_exists
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt} {target : Stmt} {config : Config}
    (hSat : satisfies model config.pc)
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = some target) :
    ∃ constraints config',
      (target, constraints) ∈ switchBranches value cases defaultBranch ∧
        addConstraints? constraints config = some config' ∧
        satisfies model config'.pc := by
  rcases guidedSwitchTarget?_some_mem_switchBranches hTarget with
    ⟨constraints, hMem, hConstraints⟩
  rcases addConstraints?_some_of_satisfies hSound hSat hConstraints with
    ⟨config', hAdd, hSat'⟩
  exact ⟨constraints, config', hMem, hAdd, hSat'⟩

theorem guidedSwitchTarget?_some_addConstraints_exists_erasePC
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt} {target : Stmt} {config : Config}
    (hSat : satisfies model config.pc)
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = some target) :
    ∃ constraints config',
      (target, constraints) ∈ switchBranches value cases defaultBranch ∧
        addConstraints? constraints config = some config' ∧
        satisfies model config'.pc ∧
        erasePC config' = erasePC config := by
  rcases guidedSwitchTarget?_some_addConstraints_exists hSound hSat hTarget with
    ⟨constraints, config', hMem, hAdd, hSat'⟩
  exact
    ⟨constraints, config', hMem, hAdd, hSat',
      addConstraints?_erasePC hAdd⟩

theorem guidedSwitchTarget?_none_mem_switchFallthroughConstraints
    {model : ConcreteModel} {value : Value}
    {cases : List (Value × Stmt)} {defaultBranch : Option Stmt}
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = none) :
    ∃ constraints,
      constraints ∈
          switchFallthroughConstraints value cases defaultBranch ∧
        ∀ constraint, constraint ∈ constraints ->
          holdsConstraint model constraint := by
  induction cases generalizing defaultBranch with
  | nil =>
      cases defaultBranch with
      | none =>
          exact
            ⟨[],
              by simp [switchFallthroughConstraints],
              by simp⟩
      | some defaultStmt =>
          simp [guidedSwitchTarget?] at hTarget
  | cons head rest ih =>
      rcases head with ⟨label, branch⟩
      by_cases hMatch :
          norm (interpValue model value) =
            norm (interpValue model label)
      · simp [guidedSwitchTarget?, hMatch] at hTarget
      · have hRestTarget :
            guidedSwitchTarget? model value rest defaultBranch = none := by
          simpa [guidedSwitchTarget?, hMatch] using hTarget
        rcases ih hRestTarget with
          ⟨constraints, hMem, hConstraints⟩
        exact
          ⟨Constraint.ne value label :: constraints,
            by simp [switchFallthroughConstraints, hMem],
            by
              intro constraint hConstraint
              simp at hConstraint
              rcases hConstraint with hEq | hOld
              · cases hEq
                simpa [holdsConstraint] using hMatch
              · exact hConstraints constraint hOld⟩

theorem guidedSwitchTarget?_none_addConstraints_exists_erasePC
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {value : Value} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt} {config : Config}
    (hSat : satisfies model config.pc)
    (hTarget :
      guidedSwitchTarget? model value cases defaultBranch = none) :
    ∃ constraints config',
      constraints ∈
          switchFallthroughConstraints value cases defaultBranch ∧
        addConstraints? constraints config = some config' ∧
        satisfies model config'.pc ∧
        erasePC config' = erasePC config := by
  rcases guidedSwitchTarget?_none_mem_switchFallthroughConstraints hTarget with
    ⟨constraints, hMem, hConstraints⟩
  rcases addConstraints?_some_of_satisfies hSound hSat hConstraints with
    ⟨config', hAdd, hSat'⟩
  exact
    ⟨constraints, config', hMem, hAdd, hSat',
      addConstraints?_erasePC hAdd⟩

mutual
  def guidedEvalStmtFuel (model : ConcreteModel) :
      Nat -> GuidedConfig -> Stmt -> Option GuidedResult
    | 0, _, _ => none
    | _fuel + 1, config, FullYul.Stmt.skip =>
        some (guidedNormalResult config)
    | _fuel + 1, config, FullYul.Stmt.expr expr =>
        match guidedEvalExpr config expr with
        | some (_, config') => some (guidedResultAfterExpr config')
        | none => none
    | _fuel + 1, config, FullYul.Stmt.let1 name init =>
        match init with
        | some expr =>
            match guidedEvalExpr config expr with
            | some (value, config') =>
                match FullYul.declare? config'.env name value with
                | some env' => some (guidedNormalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match FullYul.declare? config.env name (FullYul.Value.word 0) with
            | some env' => some (guidedNormalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, FullYul.Stmt.letMany names init =>
        match init with
        | some exprs =>
            match guidedEvalExprsAsYulValues config exprs with
            | some (values, config') =>
                match FullYul.declareMany? config'.env names values with
                | some env' => some (guidedNormalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match FullYul.declareMany? config.env names
                (names.map (fun _ => FullYul.Value.word 0)) with
            | some env' => some (guidedNormalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, FullYul.Stmt.funDef fnName params returns body =>
        some
          (guidedNormalResult
            { config with
              funcs :=
                declareFunction config.funcs fnName
                  { params := params, returns := returns, body := body } })
    | _fuel + 1, config, FullYul.Stmt.assign name expr =>
        match guidedEvalExpr config expr with
        | some (value, config') =>
            match FullYul.assign? config'.env name value with
            | some env' => some (guidedNormalResult { config' with env := env' })
            | none => none
        | none => none
    | _fuel + 1, config, FullYul.Stmt.assignMany names exprs =>
        match guidedEvalExprsAsYulValues config exprs with
        | some (values, config') =>
            match FullYul.assignMany? config'.env names values with
            | some env' => some (guidedNormalResult { config' with env := env' })
            | none => none
        | none => none
    | fuel + 1, config, FullYul.Stmt.letCall names fnName args =>
        match guidedEvalExprs config args with
        | some (argValues, config') =>
            match guidedEvalFunctionFuel model fuel config' fnName argValues with
            | some (returnValues, afterCallConfig) =>
                match FullYul.declareMany?
                    afterCallConfig.env names returnValues with
                | some env' =>
                    some (guidedNormalResult { afterCallConfig with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, FullYul.Stmt.assignCall names fnName args =>
        match guidedEvalExprs config args with
        | some (argValues, config') =>
            match guidedEvalFunctionFuel model fuel config' fnName argValues with
            | some (returnValues, afterCallConfig) =>
                match FullYul.assignMany?
                    afterCallConfig.env names returnValues with
                | some env' =>
                    some (guidedNormalResult { afterCallConfig with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, FullYul.Stmt.seq first second =>
        let config :=
          { config with
            funcs := collectStmtFunctionDefs (FullYul.Stmt.seq first second)
              config.funcs }
        guidedBindNormal (guidedEvalStmtFuel model fuel config first)
          (fun config' => guidedEvalStmtFuel model fuel config' second)
    | fuel + 1, config, FullYul.Stmt.block stmts =>
        let blockConfig :=
          { config with funcs := collectBlockFunctionDefs stmts config.funcs }
        match guidedEvalBlockFuel model fuel blockConfig stmts with
        | some result => withRestoredGuidedConfig config result
        | none => none
    | fuel + 1, config, FullYul.Stmt.ifThen cond body =>
        match guidedEvalExpr config cond with
        | some (value, config') =>
            if guidedBool model value then
              guidedEvalStmtFuel model fuel config' body
            else
              some (guidedNormalResult config')
        | none => none
    | fuel + 1, config, FullYul.Stmt.switch discr cases defaultBranch =>
        match guidedEvalExpr config discr with
        | some (value, config') =>
            match guidedSwitchTarget? model value cases defaultBranch with
            | some branch => guidedEvalStmtFuel model fuel config' branch
            | none => some (guidedNormalResult config')
        | none => none
    | fuel + 1, config, FullYul.Stmt.forLoop pre cond post body =>
        match guidedEvalStmtFuel model fuel config pre with
        | some { flow := FullYul.Flow.normal, config := loopConfig } =>
            guidedEvalForFuel model fuel config loopConfig cond post body
        | some result => withRestoredGuidedConfig config result
        | none => none
    | _fuel + 1, config, FullYul.Stmt.break =>
        some { flow := FullYul.Flow.broke, config := config }
    | _fuel + 1, config, FullYul.Stmt.continue =>
        some { flow := FullYul.Flow.continued, config := config }
    | _fuel + 1, config, FullYul.Stmt.leave =>
        some { flow := FullYul.Flow.left, config := config }

  def guidedEvalBlockFuel (model : ConcreteModel) :
      Nat -> GuidedConfig -> List Stmt -> Option GuidedResult
    | 0, _, _ => none
    | _fuel + 1, config, [] => some (guidedNormalResult config)
    | fuel + 1, config, stmt :: rest =>
        guidedBindNormal (guidedEvalStmtFuel model fuel config stmt)
          (fun config' => guidedEvalBlockFuel model fuel config' rest)

  def guidedEvalForFuel (model : ConcreteModel) :
      Nat -> GuidedConfig -> GuidedConfig -> Expr -> Stmt -> Stmt ->
        Option GuidedResult
    | 0, _, _, _, _, _ => none
    | fuel + 1, outer, loopConfig, cond, post, body =>
        match guidedEvalExpr loopConfig cond with
        | some (value, condConfig) =>
            if guidedBool model value then
              match guidedEvalStmtFuel model fuel condConfig body with
              | some { flow := FullYul.Flow.normal, config := bodyConfig }
              | some { flow := FullYul.Flow.continued, config := bodyConfig } =>
                  match guidedEvalStmtFuel model fuel bodyConfig post with
                  | some { flow := FullYul.Flow.normal, config := postConfig }
                  | some { flow := FullYul.Flow.continued, config := postConfig } =>
                      guidedEvalForFuel model fuel outer postConfig cond post body
                  | some { flow := FullYul.Flow.broke, config := postConfig } =>
                      match restoreGuidedBlockConfig outer postConfig with
                      | some restored => some (guidedNormalResult restored)
                      | none => none
                  | some { flow := FullYul.Flow.left, config := postConfig } =>
                      match restoreGuidedBlockConfig outer postConfig with
                      | some restored =>
                          some { flow := FullYul.Flow.left, config := restored }
                      | none => none
                  | some { flow := FullYul.Flow.halted, config := postConfig } =>
                      match restoreGuidedBlockConfig outer postConfig with
                      | some restored =>
                          some { flow := FullYul.Flow.halted, config := restored }
                      | none => none
                  | none => none
              | some { flow := FullYul.Flow.broke, config := bodyConfig } =>
                  match restoreGuidedBlockConfig outer bodyConfig with
                  | some restored => some (guidedNormalResult restored)
                  | none => none
              | some { flow := FullYul.Flow.left, config := bodyConfig } =>
                  match restoreGuidedBlockConfig outer bodyConfig with
                  | some restored =>
                      some { flow := FullYul.Flow.left, config := restored }
                  | none => none
              | some { flow := FullYul.Flow.halted, config := bodyConfig } =>
                  match restoreGuidedBlockConfig outer bodyConfig with
                  | some restored =>
                      some { flow := FullYul.Flow.halted, config := restored }
                  | none => none
              | none => none
            else
              match restoreGuidedBlockConfig outer condConfig with
              | some restored => some (guidedNormalResult restored)
              | none => none
        | none => none

  def guidedEvalFunctionFuel (model : ConcreteModel) :
      Nat -> GuidedConfig -> FullYul.Name -> List Value ->
        Option (List Value × GuidedConfig)
    | 0, _, _, _ => none
    | fuel + 1, config, fnName, args =>
        match FullYul.lookupFunction? config.funcs fnName with
        | some fn =>
            match FullYul.initFunctionEnv fn.params args fn.returns with
            | some callEnv =>
                let callConfig :=
                  { config with
                    env := callEnv
                    funcs := collectStmtFunctionDefs fn.body config.funcs }
                match guidedEvalStmtFuel model fuel callConfig fn.body with
                | some result =>
                    match guidedReturnValues? fn.returns result with
                    | some (values, resultConfig) =>
                        some
                          (values,
                            { resultConfig with
                              env := config.env
                              funcs := config.funcs })
                    | none => none
                | none => none
            | none => none
        | none => none
end

theorem guidedEvalBlockFuel_cons_non_normal_of_head
    {model : ConcreteModel} {fuel : Nat}
    {config : GuidedConfig} {stmt : Stmt} {rest : List Stmt}
    {result : GuidedResult}
    (hFlow : result.flow ≠ FullYul.Flow.normal)
    (hHead : guidedEvalStmtFuel model fuel config stmt = some result) :
    guidedEvalBlockFuel model fuel.succ config (stmt :: rest) =
      some result := by
  simpa [guidedEvalBlockFuel, hHead] using
    (guidedBindNormal_some_non_normal
      (result := result)
      (next := fun config' => guidedEvalBlockFuel model fuel config' rest)
      hFlow)

theorem guidedEvalStmtFuel_seq_first_non_normal_of_head
    {model : ConcreteModel} {fuel : Nat}
    {config : GuidedConfig} {first second : Stmt}
    {result : GuidedResult}
    (hFlow : result.flow ≠ FullYul.Flow.normal)
    (hFirst :
      guidedEvalStmtFuel model fuel
          { config with
            funcs :=
              collectStmtFunctionDefs (FullYul.Stmt.seq first second)
                config.funcs }
          first =
        some result) :
    guidedEvalStmtFuel model fuel.succ config
        (FullYul.Stmt.seq first second) =
      some result := by
  cases fuel with
  | zero =>
      simp [guidedEvalStmtFuel] at hFirst
  | succ fuel =>
      simpa [guidedEvalStmtFuel, hFirst] using
        (guidedBindNormal_some_non_normal
          (result := result)
          (next := fun config' =>
            guidedEvalStmtFuel model fuel.succ config' second)
          hFlow)

theorem guidedEvalStmtFuel_forLoop_pre_non_normal_restore
    {model : ConcreteModel} {fuel : Nat}
    {config : GuidedConfig} {pre post body : Stmt} {cond : Expr}
    {preResult restored : GuidedResult}
    (hFlow : preResult.flow ≠ FullYul.Flow.normal)
    (hPre :
      guidedEvalStmtFuel model fuel config pre = some preResult)
    (hRestore :
      withRestoredGuidedConfig config preResult = some restored) :
    guidedEvalStmtFuel model fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body) =
      some restored := by
  rcases preResult with ⟨flow, preConfig⟩
  cases flow with
  | normal =>
      exact False.elim (hFlow rfl)
  | broke =>
      simpa [guidedEvalStmtFuel, hPre] using hRestore
  | continued =>
      simpa [guidedEvalStmtFuel, hPre] using hRestore
  | left =>
      simpa [guidedEvalStmtFuel, hPre] using hRestore
  | halted =>
      simpa [guidedEvalStmtFuel, hPre] using hRestore

theorem guidedEvalFunctionFuel_sound_of_body
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {fnName : FullYul.Name} {args values : List Value}
    {guidedConfig : GuidedConfig}
    (hSat : satisfies model config.pc)
    (hBody :
      ∀ {fn : FullYul.FunctionDef} {callEnv : Env}
          {guidedBody : GuidedResult},
        FullYul.lookupFunction? config.funcs fnName = some fn ->
          FullYul.initFunctionEnv fn.params args fn.returns = some callEnv ->
          let callConfig : Config :=
            { config with
              env := callEnv
              funcs := collectStmtFunctionDefs fn.body config.funcs }
          satisfies model callConfig.pc ->
            guidedEvalStmtFuel model fuel (erasePC callConfig) fn.body =
              some guidedBody ->
            GuidedResultCovered model guidedBody
              (evalStmtFuel fuel callConfig fn.body))
    (hGuided :
      guidedEvalFunctionFuel model fuel.succ (erasePC config) fnName args =
        some (values, guidedConfig)) :
    ∃ config',
      (values, config') ∈ evalFunctionFuel fuel.succ config fnName args ∧
        erasePC config' = guidedConfig ∧
        satisfies model config'.pc := by
  simp [guidedEvalFunctionFuel, erasePC] at hGuided
  cases hLookup : FullYul.lookupFunction? config.funcs fnName with
  | none =>
      simp [hLookup] at hGuided
  | some fn =>
      cases hInit : FullYul.initFunctionEnv fn.params args fn.returns with
      | none =>
          simp [hLookup, hInit] at hGuided
      | some callEnv =>
          let callConfig : Config :=
            { config with
              env := callEnv
              funcs := collectStmtFunctionDefs fn.body config.funcs }
          have hSatCall : satisfies model callConfig.pc := by
            simpa [callConfig] using hSat
          cases hBodyEval :
              guidedEvalStmtFuel model fuel (erasePC callConfig) fn.body with
          | none =>
              have hBodyEvalExplicit :
                  guidedEvalStmtFuel model fuel
                      { env := callEnv
                        evm := config.evm
                        funcs := collectStmtFunctionDefs fn.body config.funcs
                        object? := config.object? } fn.body = none := by
                simpa [callConfig, erasePC] using hBodyEval
              simp [hLookup, hInit, hBodyEvalExplicit] at hGuided
          | some guidedBody =>
              have hBodyEvalExplicit :
                  guidedEvalStmtFuel model fuel
                      { env := callEnv
                        evm := config.evm
                        funcs := collectStmtFunctionDefs fn.body config.funcs
                        object? := config.object? } fn.body =
                    some guidedBody := by
                simpa [callConfig, erasePC] using hBodyEval
              have hBodyCovered :
                  GuidedResultCovered model guidedBody
                    (evalStmtFuel fuel callConfig fn.body) :=
                hBody hLookup hInit hSatCall hBodyEval
              cases hReturn :
                  guidedReturnValues? fn.returns guidedBody with
              | none =>
                  simp [hLookup, hInit, hBodyEvalExplicit, hReturn] at hGuided
              | some returned =>
                  rcases returned with ⟨returnedValues, guidedResultConfig⟩
                  simp [hLookup, hInit, hBodyEvalExplicit, hReturn] at hGuided
                  rcases hGuided with ⟨hValues, hGuidedConfig⟩
                  cases hValues
                  cases hGuidedConfig
                  rcases guidedReturnValues?_sound hBodyCovered hReturn with
                    ⟨resultConfig, hReturnMem, hEraseReturn, hSatReturn⟩
                  let finalConfig : Config :=
                    { resultConfig with env := config.env, funcs := config.funcs }
                  rcases List.mem_filterMap.mp hReturnMem with
                    ⟨bodyResult, hBodyMem, hReturnEq⟩
                  exact
                    ⟨finalConfig,
                      by
                        have hGenerated :
                            (values, finalConfig) ∈
                              (match returnValues? fn.returns bodyResult with
                              | some (returnedValues, returnedConfig) =>
                                  [(returnedValues,
                                    { returnedConfig with
                                      env := config.env
                                      funcs := config.funcs })]
                              | none => []) := by
                          rw [hReturnEq]
                          simp [finalConfig]
                        have hFlat :
                            (values, finalConfig) ∈
                              List.flatMap
                                (fun result =>
                                  match returnValues? fn.returns result with
                                  | some (returnedValues, returnedConfig) =>
                                      [(returnedValues,
                                        { returnedConfig with
                                          env := config.env
                                          funcs := config.funcs })]
                                  | none => [])
                                (evalStmtFuel fuel callConfig fn.body) :=
                          List.mem_flatMap.mpr
                            ⟨bodyResult, hBodyMem, hGenerated⟩
                        simpa [evalFunctionFuel, hLookup, hInit, callConfig]
                          using hFlat,
                      by
                        cases hEraseReturn
                        rfl,
                      by
                        simpa [finalConfig] using hSatReturn⟩

mutual
  theorem guidedEvalExpr_erasePC_eq
      (config : Config) (expr : Expr) :
      guidedEvalExpr (erasePC config) expr =
        (evalExpr config expr).map
          (fun evaluated => (evaluated.1, erasePC evaluated.2)) := by
    cases expr with
    | value value =>
        rfl
    | var name =>
        cases hLookup : FullYul.lookup? config.env name <;>
          simp [evalExpr, guidedEvalExpr, erasePC, hLookup]
    | keccak bytes =>
        rfl
    | dataSize label =>
        cases hObject : config.object? with
        | none =>
            simp [evalExpr, guidedEvalExpr, erasePC, hObject]
        | some object =>
            cases hData : object.data? label <;>
              simp [evalExpr, guidedEvalExpr, erasePC, hObject, hData]
    | dataOffset label =>
        cases hObject : config.object? with
        | none =>
            simp [evalExpr, guidedEvalExpr, erasePC, hObject]
        | some object =>
            cases hData : object.data? label <;>
              simp [evalExpr, guidedEvalExpr, erasePC, hObject, hData]
    | builtin builtin args =>
        simp [evalExpr, guidedEvalExpr]
        rw [guidedEvalExprs_erasePC_eq config args]
        cases hArgs : evalExprs config args with
        | none =>
            simp
        | some evaluatedArgs =>
            cases evaluatedArgs with
            | mk values configAfterArgs =>
                simp [erasePC]
                cases hBuiltin :
                    FullYul.evalEvmBuiltin builtin values configAfterArgs.evm with
                | none =>
                    simp
                | some evaluatedBuiltin =>
                    cases evaluatedBuiltin
                    simp

  theorem guidedEvalExprs_erasePC_eq
      (config : Config) (exprs : List Expr) :
      guidedEvalExprs (erasePC config) exprs =
        (evalExprs config exprs).map
          (fun evaluated => (evaluated.1, erasePC evaluated.2)) := by
    cases exprs with
    | nil =>
        rfl
    | cons expr rest =>
        simp [evalExprs, guidedEvalExprs]
        rw [guidedEvalExprs_erasePC_eq config rest]
        cases hRest : evalExprs config rest with
        | none =>
            simp
        | some evaluatedRest =>
            cases evaluatedRest with
            | mk restValues restConfig =>
                simp
                rw [guidedEvalExpr_erasePC_eq restConfig expr]
                cases hExpr : evalExpr restConfig expr with
                | none =>
                    simp
                | some evaluatedExpr =>
                    cases evaluatedExpr
                    simp [erasePC]
end

theorem guidedEvalExprsAsYulValues_erasePC_eq
    (config : Config) (exprs : List Expr) :
    guidedEvalExprsAsYulValues (erasePC config) exprs =
      (evalExprsAsYulValues config exprs).map
        (fun evaluated => (evaluated.1, erasePC evaluated.2)) := by
  cases exprs with
  | nil =>
      rfl
  | cons expr rest =>
      cases rest with
      | nil =>
          cases expr with
          | builtin builtin args =>
              simp [evalExprsAsYulValues, guidedEvalExprsAsYulValues]
              cases hSig : builtin.signature? with
              | none =>
                  simpa [hSig] using
                    guidedEvalExprs_erasePC_eq config
                      [FullYul.Expr.builtin builtin args]
              | some sig =>
                  by_cases hOne : sig.resultCount = 1
                  · simpa [hSig, hOne] using
                      guidedEvalExprs_erasePC_eq config
                        [FullYul.Expr.builtin builtin args]
                  · simp [hOne]
                    rw [guidedEvalExprs_erasePC_eq config args]
                    cases hArgs : evalExprs config args with
                    | none =>
                        simp
                    | some evaluatedArgs =>
                        cases evaluatedArgs with
                        | mk values configAfterArgs =>
                            simp [erasePC]
                            cases hBuiltin :
                                FullYul.evalEvmBuiltinValues builtin values
                                  configAfterArgs.evm with
                            | none =>
                                simp
                            | some evaluatedBuiltin =>
                                cases evaluatedBuiltin
                                simp
          | value value =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_eq config [FullYul.Expr.value value]
          | var name =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_eq config [FullYul.Expr.var name]
          | keccak bytes =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_eq config [FullYul.Expr.keccak bytes]
          | dataSize label =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_eq config [FullYul.Expr.dataSize label]
          | dataOffset label =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_eq config [FullYul.Expr.dataOffset label]
      | cons second more =>
          simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
            guidedEvalExprs_erasePC_eq config (expr :: second :: more)

mutual
  theorem evalExpr_preserves_pc
      {config config' : Config} {expr : Expr} {value : Value}
      (h : evalExpr config expr = some (value, config')) :
      config'.pc = config.pc := by
    cases expr with
    | value value =>
        simp [evalExpr] at h
        cases h
        subst_vars
        rfl
    | var name =>
        simp [evalExpr] at h
        split at h <;> simp_all
    | keccak bytes =>
        simp [evalExpr] at h
        cases h
        subst_vars
        rfl
    | dataSize label =>
        cases hObject : config.object? with
        | none =>
            simp [evalExpr, hObject] at h
        | some object =>
            cases hData : object.data? label with
            | none =>
                simp [evalExpr, hObject, hData] at h
            | some bytes =>
                simp [evalExpr, hObject, hData] at h
                cases h
                subst_vars
                rfl
    | dataOffset label =>
        cases hObject : config.object? with
        | none =>
            simp [evalExpr, hObject] at h
        | some object =>
            cases hData : object.data? label with
            | none =>
                simp [evalExpr, hObject, hData] at h
            | some bytes =>
                simp [evalExpr, hObject, hData] at h
                cases h
                subst_vars
                rfl
    | builtin builtin args =>
        simp [evalExpr] at h
        cases hArgs : evalExprs config args with
        | none =>
            simp [hArgs] at h
        | some evaluatedArgs =>
            cases evaluatedArgs with
            | mk values configAfterArgs =>
                have hArgsPc := evalExprs_preserves_pc hArgs
                cases hBuiltin :
                    FullYul.evalEvmBuiltin builtin values configAfterArgs.evm with
                | none =>
                    simp [hArgs, hBuiltin] at h
                | some evaluatedBuiltin =>
                    cases evaluatedBuiltin with
                    | mk value' evm' =>
                        simp [hArgs, hBuiltin] at h
                        cases h
                        subst_vars
                        exact hArgsPc

  theorem evalExprs_preserves_pc
      {config config' : Config} {exprs : List Expr} {values : List Value}
      (h : evalExprs config exprs = some (values, config')) :
      config'.pc = config.pc := by
    cases exprs with
    | nil =>
        simp [evalExprs] at h
        cases h
        subst_vars
        rfl
    | cons expr rest =>
        simp [evalExprs] at h
        cases hRest : evalExprs config rest with
        | none =>
            simp [hRest] at h
        | some evaluatedRest =>
            cases evaluatedRest with
            | mk restValues restConfig =>
                cases hExpr : evalExpr restConfig expr with
                | none =>
                    simp [hRest, hExpr] at h
                | some evaluatedExpr =>
                    cases evaluatedExpr with
                    | mk headValue headConfig =>
                        simp [hRest, hExpr] at h
                        cases h
                        subst_vars
                        exact
                          Eq.trans (evalExpr_preserves_pc hExpr)
                            (evalExprs_preserves_pc hRest)
end

theorem evalExprsAsYulValues_preserves_pc
    {config config' : Config} {exprs : List Expr} {values : List Value}
    (h : evalExprsAsYulValues config exprs = some (values, config')) :
    config'.pc = config.pc := by
  cases exprs with
  | nil =>
      simpa [evalExprsAsYulValues] using evalExprs_preserves_pc h
  | cons expr rest =>
      cases rest with
      | nil =>
          cases expr with
          | builtin builtin args =>
              cases hSig : builtin.signature? with
              | none =>
                  have hEval :
                      evalExprs config [FullYul.Expr.builtin builtin args] =
                        some (values, config') := by
                    simpa [evalExprsAsYulValues, hSig] using h
                  exact evalExprs_preserves_pc hEval
              | some sig =>
                  by_cases hOne : sig.resultCount = 1
                  · have hEval :
                        evalExprs config [FullYul.Expr.builtin builtin args] =
                          some (values, config') := by
                      simpa [evalExprsAsYulValues, hSig, hOne] using h
                    exact evalExprs_preserves_pc hEval
                  · simp [evalExprsAsYulValues, hSig, hOne] at h
                    cases hArgs : evalExprs config args with
                    | none =>
                        simp [hArgs] at h
                    | some evaluatedArgs =>
                        cases evaluatedArgs with
                        | mk argValues configAfterArgs =>
                            have hArgsPc := evalExprs_preserves_pc hArgs
                            cases hBuiltin :
                                FullYul.evalEvmBuiltinValues builtin argValues
                                  configAfterArgs.evm with
                            | none =>
                                simp [hArgs, hBuiltin] at h
                            | some evaluatedBuiltin =>
                                cases evaluatedBuiltin with
                                | mk values' evm' =>
                                    simp [hArgs, hBuiltin] at h
                                    cases h
                                    subst_vars
                                    exact hArgsPc
          | value value =>
              have hEval :
                  evalExprs config [FullYul.Expr.value value] =
                    some (values, config') := by
                simpa [evalExprsAsYulValues] using h
              exact evalExprs_preserves_pc hEval
          | var name =>
              have hEval :
                  evalExprs config [FullYul.Expr.var name] =
                    some (values, config') := by
                simpa [evalExprsAsYulValues] using h
              exact evalExprs_preserves_pc hEval
          | keccak bytes =>
              have hEval :
                  evalExprs config [FullYul.Expr.keccak bytes] =
                    some (values, config') := by
                simpa [evalExprsAsYulValues] using h
              exact evalExprs_preserves_pc hEval
          | dataSize label =>
              have hEval :
                  evalExprs config [FullYul.Expr.dataSize label] =
                    some (values, config') := by
                simpa [evalExprsAsYulValues] using h
              exact evalExprs_preserves_pc hEval
          | dataOffset label =>
              have hEval :
                  evalExprs config [FullYul.Expr.dataOffset label] =
                    some (values, config') := by
                simpa [evalExprsAsYulValues] using h
              exact evalExprs_preserves_pc hEval
      | cons second more =>
          have hEval :
              evalExprs config (expr :: second :: more) =
                some (values, config') := by
            simpa [evalExprsAsYulValues] using h
          exact evalExprs_preserves_pc hEval

mutual
  theorem guidedEvalExpr_erasePC_of_evalExpr
      {config config' : Config} {expr : Expr} {value : Value}
      (h : evalExpr config expr = some (value, config')) :
      guidedEvalExpr (erasePC config) expr =
        some (value, erasePC config') := by
    cases expr with
    | value literal =>
        simp [evalExpr] at h
        cases h
        simp_all [guidedEvalExpr, erasePC]
    | var name =>
        simp [evalExpr, guidedEvalExpr, erasePC] at h ⊢
        split at h <;> simp_all
    | keccak bytes =>
        simp [evalExpr] at h
        cases h
        simp_all [guidedEvalExpr, erasePC]
    | dataSize label =>
        simp [evalExpr, guidedEvalExpr, erasePC] at h ⊢
        split at h <;> simp_all
        split at h <;> simp_all
    | dataOffset label =>
        simp [evalExpr, guidedEvalExpr, erasePC] at h ⊢
        split at h <;> simp_all
        split at h <;> simp_all
    | builtin builtin args =>
        simp [evalExpr] at h
        cases hArgs : evalExprs config args with
        | none =>
            simp [hArgs] at h
        | some evaluated =>
            cases evaluated with
            | mk values configAfterArgs =>
                have hGuidedArgs :=
                  guidedEvalExprs_erasePC_of_evalExprs hArgs
                have hGuidedArgsUnfold :
                    guidedEvalExprs
                        { env := config.env
                          evm := config.evm
                          funcs := config.funcs
                          object? := config.object? } args =
                      some
                        ( values
                        , { env := configAfterArgs.env
                            evm := configAfterArgs.evm
                            funcs := configAfterArgs.funcs
                            object? := configAfterArgs.object? } ) := by
                  simpa [erasePC] using hGuidedArgs
                cases hBuiltin :
                    FullYul.evalEvmBuiltin builtin values configAfterArgs.evm with
                | none =>
                    simp [hArgs, hBuiltin] at h
                | some evaluatedBuiltin =>
                    cases evaluatedBuiltin with
                    | mk builtinValue evm' =>
                        simp [hArgs, hBuiltin] at h
                        rcases h with ⟨hValue, hConfig⟩
                        cases hValue
                        cases hConfig
                        simp [guidedEvalExpr]
                        rw [hGuidedArgs]
                        simp [hBuiltin, erasePC]

  theorem guidedEvalExprs_erasePC_of_evalExprs
      {config config' : Config} {exprs : List Expr} {values : List Value}
      (h : evalExprs config exprs = some (values, config')) :
      guidedEvalExprs (erasePC config) exprs =
        some (values, erasePC config') := by
    cases exprs with
    | nil =>
        simp [evalExprs] at h
        cases h
        simp_all [guidedEvalExprs, erasePC]
    | cons expr rest =>
        simp [evalExprs, guidedEvalExprs] at h ⊢
        cases hRest : evalExprs config rest with
        | none =>
            simp [hRest] at h
        | some restEvaluated =>
            cases restEvaluated with
            | mk restValues restConfig =>
                have hGuidedRest :=
                  guidedEvalExprs_erasePC_of_evalExprs hRest
                cases hExpr : evalExpr restConfig expr with
                | none =>
                    simp [hRest, hExpr] at h
                | some headEvaluated =>
                    cases headEvaluated with
                    | mk headValue headConfig =>
                        have hGuidedHead :=
                          guidedEvalExpr_erasePC_of_evalExpr hExpr
                        simp [hRest, hExpr] at h
                        cases h
                        simp_all [erasePC]
end

theorem guidedEvalExprsAsYulValues_erasePC_of_evalExprsAsYulValues
    {config config' : Config} {exprs : List Expr} {values : List Value}
    (h : evalExprsAsYulValues config exprs = some (values, config')) :
    guidedEvalExprsAsYulValues (erasePC config) exprs =
      some (values, erasePC config') := by
  cases exprs with
  | nil =>
      simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
        guidedEvalExprs_erasePC_of_evalExprs h
  | cons expr rest =>
      cases rest with
      | nil =>
          cases expr with
          | value value =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_of_evalExprs h
          | var name =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_of_evalExprs h
          | keccak bytes =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_of_evalExprs h
          | dataSize label =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_of_evalExprs h
          | dataOffset label =>
              simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
                guidedEvalExprs_erasePC_of_evalExprs h
          | builtin builtin args =>
              cases hSig : builtin.signature? with
              | none =>
                  have hEval :
                      evalExprs config [FullYul.Expr.builtin builtin args] =
                        some (values, config') := by
                    simpa [evalExprsAsYulValues, hSig] using h
                  simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues,
                    hSig] using guidedEvalExprs_erasePC_of_evalExprs hEval
              | some sig =>
                  by_cases hOne : sig.resultCount = 1
                  · have hEval :
                        evalExprs config [FullYul.Expr.builtin builtin args] =
                          some (values, config') := by
                      simpa [evalExprsAsYulValues, hSig, hOne] using h
                    simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues,
                      hSig, hOne] using guidedEvalExprs_erasePC_of_evalExprs hEval
                  · simp [evalExprsAsYulValues, guidedEvalExprsAsYulValues,
                      hSig, hOne] at h ⊢
                    cases hArgs : evalExprs config args with
                    | none =>
                        simp [hArgs] at h
                    | some evaluatedArgs =>
                        cases evaluatedArgs with
                        | mk argValues configAfterArgs =>
                            have hGuidedArgs :=
                              guidedEvalExprs_erasePC_of_evalExprs hArgs
                            have hGuidedArgs' :
                                guidedEvalExprs
                                    { env := config.env
                                      evm := config.evm
                                      funcs := config.funcs
                                      object? := config.object? } args =
                                  some
                                    ( argValues
                                    , { env := configAfterArgs.env
                                        evm := configAfterArgs.evm
                                        funcs := configAfterArgs.funcs
                                        object? := configAfterArgs.object? } ) := by
                              simpa [erasePC] using hGuidedArgs
                            cases hBuiltin :
                                FullYul.evalEvmBuiltinValues builtin argValues
                                  configAfterArgs.evm with
                            | none =>
                                simp [hArgs, hBuiltin] at h
                            | some evaluatedBuiltin =>
                                cases evaluatedBuiltin with
                                  | mk yulValues evm' =>
                                      simp [hArgs, hBuiltin] at h
                                      rcases h with ⟨hValues, hConfig⟩
                                      cases hValues
                                      cases hConfig
                                      simp [hGuidedArgs', hBuiltin, erasePC]
      | cons second more =>
          have hEval :
              evalExprs config (expr :: second :: more) =
                some (values, config') := by
            simpa [evalExprsAsYulValues] using h
          simpa [evalExprsAsYulValues, guidedEvalExprsAsYulValues] using
            guidedEvalExprs_erasePC_of_evalExprs hEval

theorem guidedEvalStmt_skip_erasePC (model : ConcreteModel)
    (fuel : Nat) (config : Config) :
    guidedEvalStmtFuel model fuel.succ (erasePC config) FullYul.Stmt.skip =
      some (eraseResult (normalResult config)) ∧
    evalStmtFuel fuel.succ config FullYul.Stmt.skip =
      [normalResult config] := by
  constructor <;> rfl

theorem guidedEvalStmt_skip_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        FullYul.Stmt.skip = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config FullYul.Stmt.skip) := by
  simp [guidedEvalStmtFuel, evalStmtFuel] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalStmt_expr_erasePC_of_evalExpr
    (model : ConcreteModel) {fuel : Nat} {config config' : Config}
    {expr : Expr} {value : Value}
    (hExpr : evalExpr config expr = some (value, config')) :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.expr expr) =
      some (eraseResult (resultAfterExpr config')) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.expr expr) =
      [resultAfterExpr config'] := by
  have hGuidedExpr := guidedEvalExpr_erasePC_of_evalExpr hExpr
  simp [erasePC] at hGuidedExpr
  constructor
  · cases hHalt : config'.evm.halt? with
    | none =>
        simp [guidedEvalStmtFuel, hGuidedExpr, resultAfterExpr,
          guidedResultAfterExpr, eraseResult, erasePC, normalResult,
          guidedNormalResult, hHalt]
    | some halt =>
        simp [guidedEvalStmtFuel, hGuidedExpr, resultAfterExpr,
          guidedResultAfterExpr, eraseResult, erasePC, hHalt]
  · simp [evalStmtFuel, hExpr]

theorem guidedEvalStmt_expr_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {expr : Expr} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.expr expr) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.expr expr)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq config expr] at hGuided
  cases hExpr : evalExpr config expr with
  | none =>
      simp [hExpr] at hGuided
  | some evaluatedExpr =>
      cases evaluatedExpr with
      | mk value configAfterExpr =>
          simp [hExpr] at hGuided
          cases hGuided
          have hPc := evalExpr_preserves_pc hExpr
          cases hHalt : configAfterExpr.evm.halt? with
          | none =>
              have hSatAfter :
                  satisfies model
                    (normalResult configAfterExpr).config.pc := by
                simp [normalResult]
                simpa [hPc] using hSat
              simp [evalStmtFuel, hExpr, resultAfterExpr,
                guidedResultAfterExpr, erasePC, normalResult,
                guidedNormalResult, hHalt]
              exact guidedResultCovered_singleton hSatAfter
          | some halt =>
              have hSatAfter :
                  satisfies model
                    ({ flow := FullYul.Flow.halted
                       config := configAfterExpr } : Result).config.pc := by
                simp
                simpa [hPc] using hSat
              simp [evalStmtFuel, hExpr, resultAfterExpr,
                guidedResultAfterExpr, erasePC, hHalt]
              exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_let1_init_erasePC_of_evalExpr
    (model : ConcreteModel) {fuel : Nat} {config config' : Config}
    {name : FullYul.Name} {expr : Expr} {value : Value} {env' : Env}
    (hExpr : evalExpr config expr = some (value, config'))
    (hDecl : FullYul.declare? config'.env name value = some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.let1 name (some expr)) =
      some (eraseResult (normalResult { config' with env := env' })) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.let1 name (some expr)) =
      [normalResult { config' with env := env' }] := by
  have hGuidedExpr := guidedEvalExpr_erasePC_of_evalExpr hExpr
  simp [erasePC] at hGuidedExpr
  constructor
  · simp [guidedEvalStmtFuel, hGuidedExpr, hDecl, eraseResult, erasePC,
      normalResult, guidedNormalResult]
  · simp [evalStmtFuel, hExpr, hDecl]

theorem guidedEvalStmt_let1_init_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {name : FullYul.Name} {expr : Expr} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.let1 name (some expr)) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.let1 name (some expr))) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq config expr] at hGuided
  cases hExpr : evalExpr config expr with
  | none =>
      simp [hExpr] at hGuided
  | some evaluatedExpr =>
      cases evaluatedExpr with
      | mk value configAfterExpr =>
          simp [hExpr] at hGuided
          simp [erasePC] at hGuided
          cases hDecl :
              FullYul.declare? configAfterExpr.env name value with
          | none =>
              simp [hDecl] at hGuided
          | some env' =>
              simp [hDecl] at hGuided
              cases hGuided
              have hPc := evalExpr_preserves_pc hExpr
              have hSatAfter :
                  satisfies model
                    (normalResult { configAfterExpr with env := env' }).config.pc := by
                simpa [normalResult, hPc] using hSat
              simp [evalStmtFuel, hExpr, hDecl]
              exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_let1_default_erasePC_of_declare
    (model : ConcreteModel) {fuel : Nat} {config : Config}
    {name : FullYul.Name} {env' : Env}
    (hDecl : FullYul.declare? config.env name (FullYul.Value.word 0) =
      some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.let1 name none) =
      some (eraseResult (normalResult { config with env := env' })) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.let1 name none) =
      [normalResult { config with env := env' }] := by
  constructor
  · simp [guidedEvalStmtFuel, hDecl, eraseResult, erasePC, normalResult,
      guidedNormalResult]
  · simp [evalStmtFuel, hDecl]

theorem guidedEvalStmt_let1_default_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {name : FullYul.Name} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.let1 name none) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.let1 name none)) := by
  simp [guidedEvalStmtFuel, erasePC] at hGuided
  cases hDecl :
      FullYul.declare? config.env name (FullYul.Value.word 0) with
  | none =>
      simp [hDecl] at hGuided
  | some env' =>
      simp [hDecl] at hGuided
      cases hGuided
      have hSatAfter :
          satisfies model
            (normalResult { config with env := env' }).config.pc := by
        simpa [normalResult] using hSat
      simp [evalStmtFuel, hDecl]
      exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_letMany_init_erasePC_of_evalExprsAsYulValues
    (model : ConcreteModel) {fuel : Nat} {config config' : Config}
    {names : List FullYul.Name} {exprs : List Expr} {values : List Value}
    {env' : Env}
    (hExprs : evalExprsAsYulValues config exprs = some (values, config'))
    (hDecls : FullYul.declareMany? config'.env names values = some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.letMany names (some exprs)) =
      some (eraseResult (normalResult { config' with env := env' })) ∧
    evalStmtFuel fuel.succ config
        (FullYul.Stmt.letMany names (some exprs)) =
      [normalResult { config' with env := env' }] := by
  have hGuidedExprs :=
    guidedEvalExprsAsYulValues_erasePC_of_evalExprsAsYulValues hExprs
  simp [erasePC] at hGuidedExprs
  constructor
  · simp [guidedEvalStmtFuel, hGuidedExprs, hDecls, eraseResult, erasePC,
      normalResult, guidedNormalResult]
  · simp [evalStmtFuel, hExprs, hDecls]

theorem guidedEvalStmt_letMany_init_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {exprs : List Expr}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.letMany names (some exprs)) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.letMany names (some exprs))) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExprsAsYulValues_erasePC_eq config exprs] at hGuided
  cases hExprs : evalExprsAsYulValues config exprs with
  | none =>
      simp [hExprs] at hGuided
  | some evaluatedExprs =>
      cases evaluatedExprs with
      | mk values configAfterExprs =>
          simp [hExprs] at hGuided
          simp [erasePC] at hGuided
          cases hDecls :
              FullYul.declareMany? configAfterExprs.env names values with
          | none =>
              simp [hDecls] at hGuided
          | some env' =>
              simp [hDecls] at hGuided
              cases hGuided
              have hPc := evalExprsAsYulValues_preserves_pc hExprs
              have hSatAfter :
                  satisfies model
                    (normalResult { configAfterExprs with env := env' }).config.pc := by
                simpa [normalResult, hPc] using hSat
              simp [evalStmtFuel, hExprs, hDecls]
              exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_letMany_default_erasePC_of_declare
    (model : ConcreteModel) {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {env' : Env}
    (hDecls : FullYul.declareMany? config.env names
        (names.map (fun _ => FullYul.Value.word 0)) = some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.letMany names none) =
      some (eraseResult (normalResult { config with env := env' })) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.letMany names none) =
      [normalResult { config with env := env' }] := by
  constructor
  · simp [guidedEvalStmtFuel, hDecls, eraseResult, erasePC, normalResult,
      guidedNormalResult]
  · simp [evalStmtFuel, hDecls]

theorem guidedEvalStmt_letMany_default_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.letMany names none) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.letMany names none)) := by
  simp [guidedEvalStmtFuel, erasePC] at hGuided
  cases hDecls :
      FullYul.declareMany? config.env names
        (names.map (fun _ => FullYul.Value.word 0)) with
  | none =>
      simp [hDecls] at hGuided
  | some env' =>
      simp [hDecls] at hGuided
      cases hGuided
      have hSatAfter :
          satisfies model
            (normalResult { config with env := env' }).config.pc := by
        simpa [normalResult] using hSat
      simp [evalStmtFuel, hDecls]
      exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_funDef_erasePC (model : ConcreteModel)
    (fuel : Nat) (config : Config) (fnName : FullYul.Name)
    (params returns : List FullYul.Name) (body : Stmt) :
    let fn : FullYul.FunctionDef :=
      { params := params, returns := returns, body := body }
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.funDef fnName params returns body) =
      some
        (eraseResult
          (normalResult
            { config with
              funcs := declareFunction config.funcs fnName fn })) ∧
    evalStmtFuel fuel.succ config
        (FullYul.Stmt.funDef fnName params returns body) =
      [normalResult
        { config with funcs := declareFunction config.funcs fnName fn }] := by
  intro fn
  constructor <;>
    simp [guidedEvalStmtFuel, evalStmtFuel, eraseResult, erasePC, normalResult,
      guidedNormalResult, fn]

theorem guidedEvalStmt_funDef_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {fnName : FullYul.Name} {params returns : List FullYul.Name}
    {body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.funDef fnName params returns body) =
          some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.funDef fnName params returns body)) := by
  simp [guidedEvalStmtFuel, evalStmtFuel, erasePC,
    normalResult, guidedNormalResult] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalStmt_assign_erasePC_of_evalExpr
    (model : ConcreteModel) {fuel : Nat} {config config' : Config}
    {name : FullYul.Name} {expr : Expr} {value : Value} {env' : Env}
    (hExpr : evalExpr config expr = some (value, config'))
    (hAssign : FullYul.assign? config'.env name value = some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.assign name expr) =
      some (eraseResult (normalResult { config' with env := env' })) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.assign name expr) =
      [normalResult { config' with env := env' }] := by
  have hGuidedExpr := guidedEvalExpr_erasePC_of_evalExpr hExpr
  simp [erasePC] at hGuidedExpr
  constructor
  · simp [guidedEvalStmtFuel, hGuidedExpr, hAssign, eraseResult, erasePC,
      normalResult, guidedNormalResult]
  · simp [evalStmtFuel, hExpr, hAssign]

theorem guidedEvalStmt_assign_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {name : FullYul.Name} {expr : Expr} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.assign name expr) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.assign name expr)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq config expr] at hGuided
  cases hExpr : evalExpr config expr with
  | none =>
      simp [hExpr] at hGuided
  | some evaluatedExpr =>
      cases evaluatedExpr with
      | mk value configAfterExpr =>
          simp [hExpr] at hGuided
          simp [erasePC] at hGuided
          cases hAssign :
              FullYul.assign? configAfterExpr.env name value with
          | none =>
              simp [hAssign] at hGuided
          | some env' =>
              simp [hAssign] at hGuided
              cases hGuided
              have hPc := evalExpr_preserves_pc hExpr
              have hSatAfter :
                  satisfies model
                    (normalResult { configAfterExpr with env := env' }).config.pc := by
                simpa [normalResult, hPc] using hSat
              simp [evalStmtFuel, hExpr, hAssign]
              exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_assignMany_erasePC_of_evalExprsAsYulValues
    (model : ConcreteModel) {fuel : Nat} {config config' : Config}
    {names : List FullYul.Name} {exprs : List Expr} {values : List Value}
    {env' : Env}
    (hExprs : evalExprsAsYulValues config exprs = some (values, config'))
    (hAssigns : FullYul.assignMany? config'.env names values = some env') :
    guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.assignMany names exprs) =
      some (eraseResult (normalResult { config' with env := env' })) ∧
    evalStmtFuel fuel.succ config (FullYul.Stmt.assignMany names exprs) =
      [normalResult { config' with env := env' }] := by
  have hGuidedExprs :=
    guidedEvalExprsAsYulValues_erasePC_of_evalExprsAsYulValues hExprs
  simp [erasePC] at hGuidedExprs
  constructor
  · simp [guidedEvalStmtFuel, hGuidedExprs, hAssigns, eraseResult, erasePC,
      normalResult, guidedNormalResult]
  · simp [evalStmtFuel, hExprs, hAssigns]

theorem guidedEvalStmt_assignMany_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {exprs : List Expr}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.assignMany names exprs) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.assignMany names exprs)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExprsAsYulValues_erasePC_eq config exprs] at hGuided
  cases hExprs : evalExprsAsYulValues config exprs with
  | none =>
      simp [hExprs] at hGuided
  | some evaluatedExprs =>
      cases evaluatedExprs with
      | mk values configAfterExprs =>
          simp [hExprs] at hGuided
          simp [erasePC] at hGuided
          cases hAssigns :
              FullYul.assignMany? configAfterExprs.env names values with
          | none =>
              simp [hAssigns] at hGuided
          | some env' =>
              simp [hAssigns] at hGuided
              cases hGuided
              have hPc := evalExprsAsYulValues_preserves_pc hExprs
              have hSatAfter :
                  satisfies model
                    (normalResult { configAfterExprs with env := env' }).config.pc := by
                simpa [normalResult, hPc] using hSat
              simp [evalStmtFuel, hExprs, hAssigns]
              exact guidedResultCovered_singleton hSatAfter

theorem guidedEvalStmt_letCall_sound_of
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {fnName : FullYul.Name}
    {args : List Expr} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hFunction :
      ∀ {configAfterArgs : Config} {argValues returnValues : List Value}
          {guidedAfter : GuidedConfig},
        satisfies model configAfterArgs.pc ->
          guidedEvalFunctionFuel model fuel (erasePC configAfterArgs)
            fnName argValues = some (returnValues, guidedAfter) ->
          ∃ afterConfig,
            (returnValues, afterConfig) ∈
                evalFunctionFuel fuel configAfterArgs fnName argValues ∧
              erasePC afterConfig = guidedAfter ∧
              satisfies model afterConfig.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.letCall names fnName args) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.letCall names fnName args)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExprs_erasePC_eq config args] at hGuided
  cases hArgs : evalExprs config args with
  | none =>
      simp [hArgs] at hGuided
  | some evaluatedArgs =>
      cases evaluatedArgs with
      | mk argValues configAfterArgs =>
          simp [hArgs] at hGuided
          have hPc := evalExprs_preserves_pc hArgs
          have hSatArgs : satisfies model configAfterArgs.pc := by
            simpa [hPc] using hSat
          cases hCall :
              guidedEvalFunctionFuel model fuel (erasePC configAfterArgs)
                fnName argValues with
          | none =>
              simp [hCall] at hGuided
          | some callResult =>
              rcases callResult with ⟨returnValues, guidedAfter⟩
              simp [hCall] at hGuided
              rcases hFunction hSatArgs hCall with
                ⟨afterConfig, hCallMem, hEraseCall, hSatAfter⟩
              cases hEraseCall
              simp [erasePC] at hGuided
              cases hDecl :
                  FullYul.declareMany? afterConfig.env names returnValues with
              | none =>
                  simp [hDecl] at hGuided
              | some env' =>
                  simp [hDecl] at hGuided
                  cases hGuided
                  let finalResult : Result :=
                    normalResult { afterConfig with env := env' }
                  have hSatFinal :
                      satisfies model finalResult.config.pc := by
                    simpa [finalResult, normalResult] using hSatAfter
                  exact
                    ⟨finalResult,
                      by
                        have hGenerated :
                            finalResult ∈
                              (match
                                FullYul.declareMany? afterConfig.env names
                                  returnValues with
                              | some env' =>
                                  [normalResult { afterConfig with env := env' }]
                              | none => []) := by
                          rw [hDecl]
                          simp [finalResult]
                        have hFlat :
                            finalResult ∈
                              List.flatMap
                                (fun (returnValues, afterCallConfig) =>
                                  match FullYul.declareMany?
                                      afterCallConfig.env names returnValues with
                                  | some env' =>
                                      [normalResult { afterCallConfig with env := env' }]
                                  | none => [])
                                (evalFunctionFuel fuel configAfterArgs fnName
                                  argValues) :=
                          List.mem_flatMap.mpr
                            ⟨(returnValues, afterConfig), hCallMem, hGenerated⟩
                        simpa [evalStmtFuel, hArgs, finalResult] using hFlat,
                      by
                        simp [finalResult, eraseResult, normalResult,
                          guidedNormalResult, erasePC],
                      hSatFinal⟩

theorem guidedEvalStmt_assignCall_sound_of
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {names : List FullYul.Name} {fnName : FullYul.Name}
    {args : List Expr} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hFunction :
      ∀ {configAfterArgs : Config} {argValues returnValues : List Value}
          {guidedAfter : GuidedConfig},
        satisfies model configAfterArgs.pc ->
          guidedEvalFunctionFuel model fuel (erasePC configAfterArgs)
            fnName argValues = some (returnValues, guidedAfter) ->
          ∃ afterConfig,
            (returnValues, afterConfig) ∈
                evalFunctionFuel fuel configAfterArgs fnName argValues ∧
              erasePC afterConfig = guidedAfter ∧
              satisfies model afterConfig.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.assignCall names fnName args) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.assignCall names fnName args)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExprs_erasePC_eq config args] at hGuided
  cases hArgs : evalExprs config args with
  | none =>
      simp [hArgs] at hGuided
  | some evaluatedArgs =>
      cases evaluatedArgs with
      | mk argValues configAfterArgs =>
          simp [hArgs] at hGuided
          have hPc := evalExprs_preserves_pc hArgs
          have hSatArgs : satisfies model configAfterArgs.pc := by
            simpa [hPc] using hSat
          cases hCall :
              guidedEvalFunctionFuel model fuel (erasePC configAfterArgs)
                fnName argValues with
          | none =>
              simp [hCall] at hGuided
          | some callResult =>
              rcases callResult with ⟨returnValues, guidedAfter⟩
              simp [hCall] at hGuided
              rcases hFunction hSatArgs hCall with
                ⟨afterConfig, hCallMem, hEraseCall, hSatAfter⟩
              cases hEraseCall
              simp [erasePC] at hGuided
              cases hAssign :
                  FullYul.assignMany? afterConfig.env names returnValues with
              | none =>
                  simp [hAssign] at hGuided
              | some env' =>
                  simp [hAssign] at hGuided
                  cases hGuided
                  let finalResult : Result :=
                    normalResult { afterConfig with env := env' }
                  have hSatFinal :
                      satisfies model finalResult.config.pc := by
                    simpa [finalResult, normalResult] using hSatAfter
                  exact
                    ⟨finalResult,
                      by
                        have hGenerated :
                            finalResult ∈
                              (match
                                FullYul.assignMany? afterConfig.env names
                                  returnValues with
                              | some env' =>
                                  [normalResult { afterConfig with env := env' }]
                              | none => []) := by
                          rw [hAssign]
                          simp [finalResult]
                        have hFlat :
                            finalResult ∈
                              List.flatMap
                                (fun (returnValues, afterCallConfig) =>
                                  match FullYul.assignMany?
                                      afterCallConfig.env names returnValues with
                                  | some env' =>
                                      [normalResult { afterCallConfig with env := env' }]
                                  | none => [])
                                (evalFunctionFuel fuel configAfterArgs fnName
                                  argValues) :=
                          List.mem_flatMap.mpr
                            ⟨(returnValues, afterConfig), hCallMem, hGenerated⟩
                        simpa [evalStmtFuel, hArgs, finalResult] using hFlat,
                      by
                        simp [finalResult, eraseResult, normalResult,
                          guidedNormalResult, erasePC],
                      hSatFinal⟩

theorem guidedEvalStmt_break_erasePC (model : ConcreteModel)
    (fuel : Nat) (config : Config) :
    guidedEvalStmtFuel model fuel.succ (erasePC config) FullYul.Stmt.break =
      some (eraseResult { flow := FullYul.Flow.broke, config := config }) ∧
    evalStmtFuel fuel.succ config FullYul.Stmt.break =
      [{ flow := FullYul.Flow.broke, config := config }] := by
  constructor <;> rfl

theorem guidedEvalStmt_break_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        FullYul.Stmt.break = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config FullYul.Stmt.break) := by
  simp [guidedEvalStmtFuel, evalStmtFuel] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalStmt_continue_erasePC (model : ConcreteModel)
    (fuel : Nat) (config : Config) :
    guidedEvalStmtFuel model fuel.succ (erasePC config) FullYul.Stmt.continue =
      some (eraseResult { flow := FullYul.Flow.continued, config := config }) ∧
    evalStmtFuel fuel.succ config FullYul.Stmt.continue =
      [{ flow := FullYul.Flow.continued, config := config }] := by
  constructor <;> rfl

theorem guidedEvalStmt_continue_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        FullYul.Stmt.continue = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config FullYul.Stmt.continue) := by
  simp [guidedEvalStmtFuel, evalStmtFuel] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalStmt_leave_erasePC (model : ConcreteModel)
    (fuel : Nat) (config : Config) :
    guidedEvalStmtFuel model fuel.succ (erasePC config) FullYul.Stmt.leave =
      some (eraseResult { flow := FullYul.Flow.left, config := config }) ∧
    evalStmtFuel fuel.succ config FullYul.Stmt.leave =
      [{ flow := FullYul.Flow.left, config := config }] := by
  constructor <;> rfl

theorem guidedEvalStmt_leave_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        FullYul.Stmt.leave = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config FullYul.Stmt.leave) := by
  simp [guidedEvalStmtFuel, evalStmtFuel] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalStmt_seq_sound_of
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {first second : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hFirst :
      ∀ {guidedFirst},
        satisfies model
          ({ config with
            funcs :=
              collectStmtFunctionDefs (FullYul.Stmt.seq first second)
                config.funcs } : Config).pc ->
          guidedEvalStmtFuel model fuel
            (erasePC
              ({ config with
                funcs :=
                  collectStmtFunctionDefs (FullYul.Stmt.seq first second)
                    config.funcs } : Config)) first =
            some guidedFirst ->
          GuidedResultCovered model guidedFirst
            (evalStmtFuel fuel
              ({ config with
                funcs :=
                  collectStmtFunctionDefs (FullYul.Stmt.seq first second)
                    config.funcs } : Config) first))
    (hSecond :
      ∀ {config' guidedSecond},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') second =
            some guidedSecond ->
          GuidedResultCovered model guidedSecond
            (evalStmtFuel fuel config' second))
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.seq first second) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.seq first second)) := by
  let seqConfig : Config :=
    { config with
      funcs :=
        collectStmtFunctionDefs (FullYul.Stmt.seq first second)
          config.funcs }
  have hSatSeq : satisfies model seqConfig.pc := by
    simpa [seqConfig] using hSat
  have hGuidedBind :
      guidedBindNormal
          (guidedEvalStmtFuel model fuel (erasePC seqConfig) first)
          (fun config' => guidedEvalStmtFuel model fuel config' second) =
        some guidedResult := by
    simpa [guidedEvalStmtFuel, erasePC, seqConfig] using hGuided
  have hEvalSeq :
      evalStmtFuel fuel.succ config (FullYul.Stmt.seq first second) =
        bindNormal (evalStmtFuel fuel seqConfig first)
          (fun config' => evalStmtFuel fuel config' second) := by
    simp [evalStmtFuel, seqConfig]
  rw [hEvalSeq]
  cases hFirstEval :
      guidedEvalStmtFuel model fuel (erasePC seqConfig) first with
  | none =>
      simp [hFirstEval, guidedBindNormal] at hGuidedBind
  | some guidedFirst =>
      have hFirstCovered :
          GuidedResultCovered model guidedFirst
            (evalStmtFuel fuel seqConfig first) :=
        hFirst hSatSeq (by simpa [seqConfig] using hFirstEval)
      exact
        guidedBindNormal_sound
          (nextGuided := fun config' =>
            guidedEvalStmtFuel model fuel config' second)
          (nextResults := fun config' => evalStmtFuel fuel config' second)
          hFirstCovered
          (by
            intro config' guidedSecond hSatConfig hSecondGuided
            exact hSecond hSatConfig hSecondGuided)
          (by simpa [hFirstEval] using hGuidedBind)

theorem guidedEvalStmt_block_sound_of
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {stmts : List Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hBlock :
      ∀ {guidedBlock},
        satisfies model
          ({ config with
            funcs := collectBlockFunctionDefs stmts config.funcs } : Config).pc ->
          guidedEvalBlockFuel model fuel
            (erasePC
              ({ config with
                funcs := collectBlockFunctionDefs stmts config.funcs } : Config))
            stmts =
            some guidedBlock ->
          GuidedResultCovered model guidedBlock
            (evalBlockFuel fuel
              ({ config with
                funcs := collectBlockFunctionDefs stmts config.funcs } : Config)
              stmts))
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.block stmts) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.block stmts)) := by
  let blockConfig : Config :=
    { config with funcs := collectBlockFunctionDefs stmts config.funcs }
  have hSatBlock : satisfies model blockConfig.pc := by
    simpa [blockConfig] using hSat
  have hGuidedBlockStmt :
      (match guidedEvalBlockFuel model fuel (erasePC blockConfig) stmts with
      | some result => withRestoredGuidedConfig (erasePC config) result
      | none => none) =
        some guidedResult := by
    simpa [guidedEvalStmtFuel, erasePC, blockConfig] using hGuided
  have hEvalBlockStmt :
      evalStmtFuel fuel.succ config (FullYul.Stmt.block stmts) =
        (evalBlockFuel fuel blockConfig stmts).filterMap
          (fun result => withRestoredConfig config result) := by
    simp [evalStmtFuel, blockConfig]
  rw [hEvalBlockStmt]
  cases hBlockEval :
      guidedEvalBlockFuel model fuel (erasePC blockConfig) stmts with
  | none =>
      simp [hBlockEval] at hGuidedBlockStmt
  | some guidedBlock =>
      have hBlockCovered :
          GuidedResultCovered model guidedBlock
            (evalBlockFuel fuel blockConfig stmts) :=
        hBlock hSatBlock (by simpa [blockConfig] using hBlockEval)
      exact
        withRestoredGuidedConfig_sound hBlockCovered
          (by simpa [hBlockEval] using hGuidedBlockStmt)

theorem guidedEvalStmt_ifThen_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {config : Config} {cond : Expr} {body : Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.ifThen cond body) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config (FullYul.Stmt.ifThen cond body)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq config cond] at hGuided
  cases hCond : evalExpr config cond with
  | none =>
      simp [hCond] at hGuided
  | some evaluatedCond =>
      cases evaluatedCond with
      | mk value configAfterCond =>
          simp [hCond] at hGuided
          have hPc := evalExpr_preserves_pc hCond
          have hSatCond : satisfies model configAfterCond.pc := by
            simpa [hPc] using hSat
          rcases branchOn_guidedBool_exists_satisfies_erasePC
              (value := value) hSound hSatCond with
            ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
          cases hBool : guidedBool model value
          · have hBranchMemFalse :
                (false, branchConfig) ∈ branchOn value configAfterCond := by
              simpa [hBool] using hBranchMem
            simp [hBool] at hGuided
            cases hGuided
            have hCovered :
                GuidedResultCovered model (guidedNormalResult (erasePC configAfterCond))
                  [normalResult branchConfig] := by
              simpa [eraseResult, normalResult, guidedNormalResult,
                hBranchErase] using
                (guidedResultCovered_singleton
                  (model := model) (result := normalResult branchConfig)
                  hBranchSat)
            rcases hCovered with ⟨result, hResultMem, hErase, hResultSat⟩
            simp [evalStmtFuel, hCond]
            exact
              ⟨result,
                List.mem_flatMap.mpr
                  ⟨(false, branchConfig), hBranchMemFalse,
                    by simpa using hResultMem⟩,
                hErase,
                hResultSat⟩
          · have hBranchMemTrue :
                (true, branchConfig) ∈ branchOn value configAfterCond := by
              simpa [hBool] using hBranchMem
            simp [hBool] at hGuided
            have hBodyGuided :
                guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
                  some guidedResult := by
              simpa [hBranchErase] using hGuided
            rcases hBody hBranchSat hBodyGuided with
              ⟨result, hResultMem, hErase, hResultSat⟩
            simp [evalStmtFuel, hCond]
            exact
              ⟨result,
                List.mem_flatMap.mpr
                  ⟨(true, branchConfig), hBranchMemTrue, hResultMem⟩,
                hErase,
                hResultSat⟩

theorem guidedEvalStmt_switch_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {config : Config} {discr : Expr}
    {cases : List (Value × Stmt)} {defaultBranch : Option Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hBranch :
      ∀ {config' branch guidedBranch},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') branch =
            some guidedBranch ->
          GuidedResultCovered model guidedBranch
            (evalStmtFuel fuel config' branch))
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.switch discr cases defaultBranch) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.switch discr cases defaultBranch)) := by
  simp [guidedEvalStmtFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq config discr] at hGuided
  cases hDiscr : evalExpr config discr with
  | none =>
      simp [hDiscr] at hGuided
  | some evaluatedDiscr =>
      cases evaluatedDiscr with
      | mk value configAfterDiscr =>
          simp [hDiscr] at hGuided
          have hPc := evalExpr_preserves_pc hDiscr
          have hSatDiscr : satisfies model configAfterDiscr.pc := by
            simpa [hPc] using hSat
          cases hTarget :
              guidedSwitchTarget? model value cases defaultBranch with
          | some target =>
              simp [hTarget] at hGuided
              rcases guidedSwitchTarget?_some_addConstraints_exists_erasePC
                  (value := value) hSound hSatDiscr hTarget with
                ⟨constraints, branchConfig, hMem, hAdd, hSatBranch, hErase⟩
              have hBranchGuided :
                  guidedEvalStmtFuel model fuel (erasePC branchConfig) target =
                    some guidedResult := by
                simpa [hErase] using hGuided
              rcases hBranch hSatBranch hBranchGuided with
                ⟨result, hResultMem, hEraseResult, hResultSat⟩
              simp [evalStmtFuel, hDiscr]
              exact
                ⟨result,
                  List.mem_append.mpr
                    (Or.inl
                      (List.mem_flatMap.mpr
                        ⟨(target, constraints), hMem,
                          by simp [hAdd, hResultMem]⟩)),
                  hEraseResult,
                  hResultSat⟩
          | none =>
              simp [hTarget] at hGuided
              cases hGuided
              rcases guidedSwitchTarget?_none_addConstraints_exists_erasePC
                  (value := value) hSound hSatDiscr hTarget with
                ⟨constraints, branchConfig, hMem, hAdd, hSatBranch, hErase⟩
              have hCovered :
                  GuidedResultCovered model
                    (guidedNormalResult (erasePC configAfterDiscr))
                    [normalResult branchConfig] := by
                simpa [eraseResult, normalResult, guidedNormalResult,
                  hErase] using
                  (guidedResultCovered_singleton
                    (model := model) (result := normalResult branchConfig)
                    hSatBranch)
              rcases hCovered with
                ⟨result, hResultMem, hEraseResult, hResultSat⟩
              simp [evalStmtFuel, hDiscr]
              exact
                ⟨result,
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_flatMap.mpr
                        ⟨constraints, hMem,
                          by simp [hAdd, hResultMem]⟩)),
                  hEraseResult,
                  hResultSat⟩

theorem guidedEvalBlock_nil_sound
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalBlockFuel model fuel.succ (erasePC config) [] =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalBlockFuel fuel.succ config []) := by
  simp [guidedEvalBlockFuel, evalBlockFuel] at hGuided ⊢
  cases hGuided
  exact guidedResultCovered_singleton hSat

theorem guidedEvalBlock_cons_sound_of
    {model : ConcreteModel} {fuel : Nat} {config : Config}
    {stmt : Stmt} {rest : List Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hStmt :
      ∀ {guidedStmt},
        satisfies model config.pc ->
          guidedEvalStmtFuel model fuel (erasePC config) stmt =
            some guidedStmt ->
          GuidedResultCovered model guidedStmt
            (evalStmtFuel fuel config stmt))
    (hRest :
      ∀ {config' guidedRest},
        satisfies model config'.pc ->
          guidedEvalBlockFuel model fuel (erasePC config') rest =
            some guidedRest ->
          GuidedResultCovered model guidedRest
            (evalBlockFuel fuel config' rest))
    (hGuided :
      guidedEvalBlockFuel model fuel.succ (erasePC config) (stmt :: rest) =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalBlockFuel fuel.succ config (stmt :: rest)) := by
  have hGuidedBind :
      guidedBindNormal
          (guidedEvalStmtFuel model fuel (erasePC config) stmt)
          (fun config' => guidedEvalBlockFuel model fuel config' rest) =
        some guidedResult := by
    simpa [guidedEvalBlockFuel] using hGuided
  simp [evalBlockFuel]
  cases hStmtEval :
      guidedEvalStmtFuel model fuel (erasePC config) stmt with
  | none =>
      simp [hStmtEval, guidedBindNormal] at hGuidedBind
  | some guidedStmt =>
      have hStmtCovered :
          GuidedResultCovered model guidedStmt
            (evalStmtFuel fuel config stmt) :=
        hStmt hSat hStmtEval
      exact
        guidedBindNormal_sound
          (nextGuided := fun config' =>
            guidedEvalBlockFuel model fuel config' rest)
          (nextResults := fun config' => evalBlockFuel fuel config' rest)
          hStmtCovered
          (by
            intro config' guidedRest hSatConfig hRestGuided
            exact hRest hSatConfig hRestGuided)
          (by simpa [hStmtEval] using hGuidedBind)

private theorem guidedEvalFor_false_sound_of_cond
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = false)
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  simp [guidedEvalForFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
  simp [hCond, hBool] at hGuided
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemFalse :
      (false, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  cases hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) (erasePC condConfig) with
  | none =>
      simp [hRestoreGuided] at hGuided
  | some restoredGuided =>
      simp [hRestoreGuided] at hGuided
      cases hGuided
      have hRestoreGuidedBranch :
          restoreGuidedBlockConfig (erasePC outer) (erasePC branchConfig) =
            some restoredGuided := by
        simpa [hBranchErase] using hRestoreGuided
      rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
          hRestoreGuidedBranch with
        ⟨restored, hRestore, hEraseRestored⟩
      have hSatRestored : satisfies model restored.pc := by
        have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
        simpa [hPath] using hBranchSat
      exact
        ⟨normalResult restored,
          by
            have hGenerated :
                normalResult restored ∈
                  (if false then
                    List.flatMap
                      (fun bodyResult =>
                        match bodyResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            List.flatMap
                              (fun postResult =>
                                match postResult.flow with
                                | FullYul.Flow.normal
                                | FullYul.Flow.continued =>
                                    evalForFuel fuel outer postResult.config
                                      cond post body
                                | FullYul.Flow.broke =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored => [normalResult restored]
                                    | none => []
                                | FullYul.Flow.left =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.left
                                           config := restored }]
                                    | none => []
                                | FullYul.Flow.halted =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.halted
                                           config := restored }]
                                    | none => [])
                              (evalStmtFuel fuel bodyResult.config post)
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer bodyResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel branchConfig body)
                  else
                    match restoreBlockConfig outer branchConfig with
                    | some restored => [normalResult restored]
                    | none => []) := by
              simp [hRestore]
            have hFlat :
                normalResult restored ∈
                  List.flatMap
                    (fun (takeBranch, branchConfig) =>
                      if takeBranch then
                        List.flatMap
                          (fun bodyResult =>
                            match bodyResult.flow with
                            | FullYul.Flow.normal
                            | FullYul.Flow.continued =>
                                List.flatMap
                                  (fun postResult =>
                                    match postResult.flow with
                                    | FullYul.Flow.normal
                                    | FullYul.Flow.continued =>
                                        evalForFuel fuel outer postResult.config
                                          cond post body
                                    | FullYul.Flow.broke =>
                                        match restoreBlockConfig outer
                                            postResult.config with
                                        | some restored => [normalResult restored]
                                        | none => []
                                    | FullYul.Flow.left =>
                                        match restoreBlockConfig outer
                                            postResult.config with
                                        | some restored =>
                                            [{ flow := FullYul.Flow.left
                                               config := restored }]
                                        | none => []
                                    | FullYul.Flow.halted =>
                                        match restoreBlockConfig outer
                                            postResult.config with
                                        | some restored =>
                                            [{ flow := FullYul.Flow.halted
                                               config := restored }]
                                        | none => [])
                                  (evalStmtFuel fuel bodyResult.config post)
                            | FullYul.Flow.broke =>
                                match restoreBlockConfig outer
                                    bodyResult.config with
                                | some restored => [normalResult restored]
                                | none => []
                            | FullYul.Flow.left =>
                                match restoreBlockConfig outer
                                    bodyResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.left
                                       config := restored }]
                                | none => []
                            | FullYul.Flow.halted =>
                                match restoreBlockConfig outer
                                    bodyResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.halted
                                       config := restored }]
                                | none => [])
                          (evalStmtFuel fuel branchConfig body)
                      else
                        match restoreBlockConfig outer branchConfig with
                        | some restored => [normalResult restored]
                        | none => [])
                    (branchOn value condConfig) :=
              List.mem_flatMap.mpr
                ⟨(false, branchConfig), hBranchMemFalse, hGenerated⟩
            simpa [evalForFuel, hCond] using hFlat,
          by
            simp [eraseResult, normalResult, guidedNormalResult,
              hEraseRestored],
          by simpa [normalResult] using hSatRestored⟩

private theorem guidedEvalFor_body_break_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyGuidedConfig restoredGuided : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some { flow := FullYul.Flow.broke, config := bodyGuidedConfig })
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig =
        some restoredGuided) :
    GuidedResultCovered model (guidedNormalResult restoredGuided)
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some { flow := FullYul.Flow.broke, config := bodyGuidedConfig } := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨bodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatBody
  exact
    ⟨normalResult restored,
      by
        have hGenerated :
            normalResult restored ∈
              (if true then
                List.flatMap
                  (fun bodyResult =>
                    match bodyResult.flow with
                    | FullYul.Flow.normal
                    | FullYul.Flow.continued =>
                        List.flatMap
                          (fun postResult =>
                            match postResult.flow with
                            | FullYul.Flow.normal
                            | FullYul.Flow.continued =>
                                evalForFuel fuel outer postResult.config
                                  cond post body
                            | FullYul.Flow.broke =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored => [normalResult restored]
                                | none => []
                            | FullYul.Flow.left =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.left
                                       config := restored }]
                                | none => []
                            | FullYul.Flow.halted =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.halted
                                       config := restored }]
                                | none => [])
                          (evalStmtFuel fuel bodyResult.config post)
                    | FullYul.Flow.broke =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored => [normalResult restored]
                        | none => []
                    | FullYul.Flow.left =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.left, config := restored }]
                        | none => []
                    | FullYul.Flow.halted =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.halted, config := restored }]
                        | none => [])
                  (evalStmtFuel fuel branchConfig body)
              else
                match restoreBlockConfig outer branchConfig with
                | some restored => [normalResult restored]
                | none => []) := by
          simp
          exact
            ⟨({ flow := FullYul.Flow.broke, config := bodyConfig } : Result),
              hBodyMem,
              by simp [hRestore]⟩
        have hFlat :
            normalResult restored ∈
              List.flatMap
                (fun (takeBranch, branchConfig) =>
                  if takeBranch then
                    List.flatMap
                      (fun bodyResult =>
                        match bodyResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            List.flatMap
                              (fun postResult =>
                                match postResult.flow with
                                | FullYul.Flow.normal
                                | FullYul.Flow.continued =>
                                    evalForFuel fuel outer postResult.config
                                      cond post body
                                | FullYul.Flow.broke =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored => [normalResult restored]
                                    | none => []
                                | FullYul.Flow.left =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.left
                                           config := restored }]
                                    | none => []
                                | FullYul.Flow.halted =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.halted
                                           config := restored }]
                                    | none => [])
                              (evalStmtFuel fuel bodyResult.config post)
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel branchConfig body)
                  else
                    match restoreBlockConfig outer branchConfig with
                    | some restored => [normalResult restored]
                    | none => [])
                (branchOn value condConfig) :=
          List.mem_flatMap.mpr
            ⟨(true, branchConfig), hBranchMemTrue, hGenerated⟩
        simpa [evalForFuel, hCond] using hFlat,
      by
        simp [eraseResult, normalResult, guidedNormalResult,
          hEraseRestored],
      by simpa [normalResult] using hSatRestored⟩

private theorem guidedEvalFor_body_left_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyGuidedConfig restoredGuided : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some { flow := FullYul.Flow.left, config := bodyGuidedConfig })
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig =
        some restoredGuided) :
    GuidedResultCovered model
      ({ flow := FullYul.Flow.left, config := restoredGuided } : GuidedResult)
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some { flow := FullYul.Flow.left, config := bodyGuidedConfig } := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨bodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatBody
  exact
    ⟨({ flow := FullYul.Flow.left, config := restored } : Result),
      by
        have hGenerated :
            ({ flow := FullYul.Flow.left, config := restored } : Result) ∈
              (if true then
                List.flatMap
                  (fun bodyResult =>
                    match bodyResult.flow with
                    | FullYul.Flow.normal
                    | FullYul.Flow.continued =>
                        List.flatMap
                          (fun postResult =>
                            match postResult.flow with
                            | FullYul.Flow.normal
                            | FullYul.Flow.continued =>
                                evalForFuel fuel outer postResult.config
                                  cond post body
                            | FullYul.Flow.broke =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored => [normalResult restored]
                                | none => []
                            | FullYul.Flow.left =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.left
                                       config := restored }]
                                | none => []
                            | FullYul.Flow.halted =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.halted
                                       config := restored }]
                                | none => [])
                          (evalStmtFuel fuel bodyResult.config post)
                    | FullYul.Flow.broke =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored => [normalResult restored]
                        | none => []
                    | FullYul.Flow.left =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.left, config := restored }]
                        | none => []
                    | FullYul.Flow.halted =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.halted, config := restored }]
                        | none => [])
                  (evalStmtFuel fuel branchConfig body)
              else
                match restoreBlockConfig outer branchConfig with
                | some restored => [normalResult restored]
                | none => []) := by
          simp
          exact
            ⟨({ flow := FullYul.Flow.left, config := bodyConfig } : Result),
              hBodyMem,
              by simp [hRestore]⟩
        have hFlat :
            ({ flow := FullYul.Flow.left, config := restored } : Result) ∈
              List.flatMap
                (fun (takeBranch, branchConfig) =>
                  if takeBranch then
                    List.flatMap
                      (fun bodyResult =>
                        match bodyResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            List.flatMap
                              (fun postResult =>
                                match postResult.flow with
                                | FullYul.Flow.normal
                                | FullYul.Flow.continued =>
                                    evalForFuel fuel outer postResult.config
                                      cond post body
                                | FullYul.Flow.broke =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored => [normalResult restored]
                                    | none => []
                                | FullYul.Flow.left =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.left
                                           config := restored }]
                                    | none => []
                                | FullYul.Flow.halted =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.halted
                                           config := restored }]
                                    | none => [])
                              (evalStmtFuel fuel bodyResult.config post)
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel branchConfig body)
                  else
                    match restoreBlockConfig outer branchConfig with
                    | some restored => [normalResult restored]
                    | none => [])
                (branchOn value condConfig) :=
          List.mem_flatMap.mpr
            ⟨(true, branchConfig), hBranchMemTrue, hGenerated⟩
        simpa [evalForFuel, hCond] using hFlat,
      by
        simp [eraseResult, hEraseRestored],
      by simpa using hSatRestored⟩

private theorem guidedEvalFor_body_halted_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyGuidedConfig restoredGuided : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some { flow := FullYul.Flow.halted, config := bodyGuidedConfig })
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig =
        some restoredGuided) :
    GuidedResultCovered model
      ({ flow := FullYul.Flow.halted, config := restoredGuided } : GuidedResult)
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some { flow := FullYul.Flow.halted, config := bodyGuidedConfig } := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨bodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hFlow, hConfig⟩
  cases hFlow
  cases hConfig
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatBody
  exact
    ⟨({ flow := FullYul.Flow.halted, config := restored } : Result),
      by
        have hGenerated :
            ({ flow := FullYul.Flow.halted, config := restored } : Result) ∈
              (if true then
                List.flatMap
                  (fun bodyResult =>
                    match bodyResult.flow with
                    | FullYul.Flow.normal
                    | FullYul.Flow.continued =>
                        List.flatMap
                          (fun postResult =>
                            match postResult.flow with
                            | FullYul.Flow.normal
                            | FullYul.Flow.continued =>
                                evalForFuel fuel outer postResult.config
                                  cond post body
                            | FullYul.Flow.broke =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored => [normalResult restored]
                                | none => []
                            | FullYul.Flow.left =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.left
                                       config := restored }]
                                | none => []
                            | FullYul.Flow.halted =>
                                match restoreBlockConfig outer postResult.config with
                                | some restored =>
                                    [{ flow := FullYul.Flow.halted
                                       config := restored }]
                                | none => [])
                          (evalStmtFuel fuel bodyResult.config post)
                    | FullYul.Flow.broke =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored => [normalResult restored]
                        | none => []
                    | FullYul.Flow.left =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.left, config := restored }]
                        | none => []
                    | FullYul.Flow.halted =>
                        match restoreBlockConfig outer bodyResult.config with
                        | some restored =>
                            [{ flow := FullYul.Flow.halted, config := restored }]
                        | none => [])
                  (evalStmtFuel fuel branchConfig body)
              else
                match restoreBlockConfig outer branchConfig with
                | some restored => [normalResult restored]
                | none => []) := by
          simp
          exact
            ⟨({ flow := FullYul.Flow.halted, config := bodyConfig } : Result),
              hBodyMem,
              by simp [hRestore]⟩
        have hFlat :
            ({ flow := FullYul.Flow.halted, config := restored } : Result) ∈
              List.flatMap
                (fun (takeBranch, branchConfig) =>
                  if takeBranch then
                    List.flatMap
                      (fun bodyResult =>
                        match bodyResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            List.flatMap
                              (fun postResult =>
                                match postResult.flow with
                                | FullYul.Flow.normal
                                | FullYul.Flow.continued =>
                                    evalForFuel fuel outer postResult.config
                                      cond post body
                                | FullYul.Flow.broke =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored => [normalResult restored]
                                    | none => []
                                | FullYul.Flow.left =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.left
                                           config := restored }]
                                    | none => []
                                | FullYul.Flow.halted =>
                                    match restoreBlockConfig outer
                                        postResult.config with
                                    | some restored =>
                                        [{ flow := FullYul.Flow.halted
                                           config := restored }]
                                    | none => [])
                              (evalStmtFuel fuel bodyResult.config post)
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer
                                bodyResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel branchConfig body)
                  else
                    match restoreBlockConfig outer branchConfig with
                    | some restored => [normalResult restored]
                    | none => [])
                (branchOn value condConfig) :=
          List.mem_flatMap.mpr
            ⟨(true, branchConfig), hBranchMemTrue, hGenerated⟩
        simpa [evalForFuel, hCond] using hFlat,
      by
        simp [eraseResult, hEraseRestored],
      by simpa using hSatRestored⟩

def loopRecurFlow (flow : FullYul.Flow) : Prop :=
  flow = FullYul.Flow.normal ∨ flow = FullYul.Flow.continued

def loopTerminalFlow (flow : FullYul.Flow) : Prop :=
  flow = FullYul.Flow.broke ∨
    flow = FullYul.Flow.left ∨
      flow = FullYul.Flow.halted

theorem loopFlow_recur_or_terminal (flow : FullYul.Flow) :
    loopRecurFlow flow ∨ loopTerminalFlow flow := by
  cases flow <;> simp [loopRecurFlow, loopTerminalFlow]

theorem loopRecurFlow_elim
    {flow : FullYul.Flow} {P : Prop}
    (hFlow : loopRecurFlow flow)
    (hNormal : flow = FullYul.Flow.normal -> P)
    (hContinued : flow = FullYul.Flow.continued -> P) :
    P := by
  rcases hFlow with hNormal' | hContinued'
  · exact hNormal hNormal'
  · exact hContinued hContinued'

theorem loopTerminalFlow_elim
    {flow : FullYul.Flow} {P : Prop}
    (hFlow : loopTerminalFlow flow)
    (hBroke : flow = FullYul.Flow.broke -> P)
    (hLeft : flow = FullYul.Flow.left -> P)
    (hHalted : flow = FullYul.Flow.halted -> P) :
    P := by
  rcases hFlow with hBroke' | hLeftOrHalted
  · exact hBroke hBroke'
  · rcases hLeftOrHalted with hLeft' | hHalted'
    · exact hLeft hLeft'
    · exact hHalted hHalted'

theorem loopRecurPairFlow_elim
    {bodyFlow postFlow : FullYul.Flow} {P : Prop}
    (hBodyFlow : loopRecurFlow bodyFlow)
    (hPostFlow : loopRecurFlow postFlow)
    (hNormalNormal :
      bodyFlow = FullYul.Flow.normal ->
      postFlow = FullYul.Flow.normal ->
      P)
    (hNormalContinued :
      bodyFlow = FullYul.Flow.normal ->
      postFlow = FullYul.Flow.continued ->
      P)
    (hContinuedNormal :
      bodyFlow = FullYul.Flow.continued ->
      postFlow = FullYul.Flow.normal ->
      P)
    (hContinuedContinued :
      bodyFlow = FullYul.Flow.continued ->
      postFlow = FullYul.Flow.continued ->
      P) :
    P :=
  loopRecurFlow_elim hBodyFlow
    (fun hBodyNormal =>
      loopRecurFlow_elim hPostFlow
        (hNormalNormal hBodyNormal)
        (hNormalContinued hBodyNormal))
    (fun hBodyContinued =>
      loopRecurFlow_elim hPostFlow
        (hContinuedNormal hBodyContinued)
        (hContinuedContinued hBodyContinued))

theorem loopRecurTerminalFlow_elim
    {bodyFlow postFlow : FullYul.Flow} {P : Prop}
    (hBodyFlow : loopRecurFlow bodyFlow)
    (hPostFlow : loopTerminalFlow postFlow)
    (hNormalBroke :
      bodyFlow = FullYul.Flow.normal ->
      postFlow = FullYul.Flow.broke ->
      P)
    (hNormalLeft :
      bodyFlow = FullYul.Flow.normal ->
      postFlow = FullYul.Flow.left ->
      P)
    (hNormalHalted :
      bodyFlow = FullYul.Flow.normal ->
      postFlow = FullYul.Flow.halted ->
      P)
    (hContinuedBroke :
      bodyFlow = FullYul.Flow.continued ->
      postFlow = FullYul.Flow.broke ->
      P)
    (hContinuedLeft :
      bodyFlow = FullYul.Flow.continued ->
      postFlow = FullYul.Flow.left ->
      P)
    (hContinuedHalted :
      bodyFlow = FullYul.Flow.continued ->
      postFlow = FullYul.Flow.halted ->
      P) :
    P :=
  loopRecurFlow_elim hBodyFlow
    (fun hBodyNormal =>
      loopTerminalFlow_elim hPostFlow
        (hNormalBroke hBodyNormal)
        (hNormalLeft hBodyNormal)
        (hNormalHalted hBodyNormal))
    (fun hBodyContinued =>
      loopTerminalFlow_elim hPostFlow
        (hContinuedBroke hBodyContinued)
        (hContinuedLeft hBodyContinued)
        (hContinuedHalted hBodyContinued))

def loopRestoredGuidedResult
    (flow : FullYul.Flow) (config : GuidedConfig) : GuidedResult :=
  match flow with
  | FullYul.Flow.broke => guidedNormalResult config
  | FullYul.Flow.left => { flow := FullYul.Flow.left, config := config }
  | FullYul.Flow.halted => { flow := FullYul.Flow.halted, config := config }
  | FullYul.Flow.normal => guidedNormalResult config
  | FullYul.Flow.continued =>
      { flow := FullYul.Flow.continued, config := config }

def loopRestoredResult (flow : FullYul.Flow) (config : Config) : Result :=
  match flow with
  | FullYul.Flow.broke => normalResult config
  | FullYul.Flow.left => { flow := FullYul.Flow.left, config := config }
  | FullYul.Flow.halted => { flow := FullYul.Flow.halted, config := config }
  | FullYul.Flow.normal => normalResult config
  | FullYul.Flow.continued =>
      { flow := FullYul.Flow.continued, config := config }

theorem erase_loopRestoredResult
    (flow : FullYul.Flow) (config : Config) :
    eraseResult (loopRestoredResult flow config) =
      loopRestoredGuidedResult flow (erasePC config) := by
  cases flow <;> rfl

theorem loopRestoredResult_satisfies
    {model : ConcreteModel} {flow : FullYul.Flow} {config : Config}
    (hSat : satisfies model config.pc) :
    satisfies model (loopRestoredResult flow config).config.pc := by
  cases flow <;> simpa [loopRestoredResult, normalResult] using hSat

private theorem evalFor_body_terminal_mem
    {fuel : Nat} {outer loopConfig condConfig branchConfig bodyConfig
      restored : Config}
    {cond : Expr} {post body : Stmt} {value : Value}
    {bodyFlow : FullYul.Flow}
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBranchMem : (true, branchConfig) ∈ branchOn value condConfig)
    (hBodyFlow : loopTerminalFlow bodyFlow)
    (hBodyMem :
      ({ flow := bodyFlow, config := bodyConfig } : Result) ∈
        evalStmtFuel fuel branchConfig body)
    (hRestore : restoreBlockConfig outer bodyConfig = some restored) :
    loopRestoredResult bodyFlow restored ∈
      evalForFuel fuel.succ outer loopConfig cond post body := by
  have hGenerated :
      loopRestoredResult bodyFlow restored ∈
        (if true then
          List.flatMap
            (fun bodyResult =>
              match bodyResult.flow with
              | FullYul.Flow.normal
              | FullYul.Flow.continued =>
                  List.flatMap
                    (fun postResult =>
                      match postResult.flow with
                      | FullYul.Flow.normal
                      | FullYul.Flow.continued =>
                          evalForFuel fuel outer postResult.config cond post body
                      | FullYul.Flow.broke =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored => [normalResult restored]
                          | none => []
                      | FullYul.Flow.left =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.left, config := restored }]
                          | none => []
                      | FullYul.Flow.halted =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.halted
                                 config := restored }]
                          | none => [])
                    (evalStmtFuel fuel bodyResult.config post)
              | FullYul.Flow.broke =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored => [normalResult restored]
                  | none => []
              | FullYul.Flow.left =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored =>
                      [{ flow := FullYul.Flow.left, config := restored }]
                  | none => []
              | FullYul.Flow.halted =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored =>
                      [{ flow := FullYul.Flow.halted, config := restored }]
                  | none => [])
            (evalStmtFuel fuel branchConfig body)
        else
          match restoreBlockConfig outer branchConfig with
          | some restored => [normalResult restored]
          | none => []) := by
    rcases hBodyFlow with hBroke | hLeftOrHalted
    · cases hBroke
      simp [loopRestoredResult]
      exact
        ⟨({ flow := FullYul.Flow.broke, config := bodyConfig } : Result),
          hBodyMem,
          by simp [hRestore]⟩
    · rcases hLeftOrHalted with hLeft | hHalted
      · cases hLeft
        simp [loopRestoredResult]
        exact
          ⟨({ flow := FullYul.Flow.left, config := bodyConfig } : Result),
            hBodyMem,
            by simp [hRestore]⟩
      · cases hHalted
        simp [loopRestoredResult]
        exact
          ⟨({ flow := FullYul.Flow.halted, config := bodyConfig } : Result),
            hBodyMem,
            by simp [hRestore]⟩
  have hFlat :
      loopRestoredResult bodyFlow restored ∈
        List.flatMap
          (fun (takeBranch, branchConfig) =>
            if takeBranch then
              List.flatMap
                (fun bodyResult =>
                  match bodyResult.flow with
                  | FullYul.Flow.normal
                  | FullYul.Flow.continued =>
                      List.flatMap
                        (fun postResult =>
                          match postResult.flow with
                          | FullYul.Flow.normal
                          | FullYul.Flow.continued =>
                              evalForFuel fuel outer postResult.config cond post body
                          | FullYul.Flow.broke =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored => [normalResult restored]
                              | none => []
                          | FullYul.Flow.left =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.left
                                     config := restored }]
                              | none => []
                          | FullYul.Flow.halted =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.halted
                                     config := restored }]
                              | none => [])
                        (evalStmtFuel fuel bodyResult.config post)
                  | FullYul.Flow.broke =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored => [normalResult restored]
                      | none => []
                  | FullYul.Flow.left =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored =>
                          [{ flow := FullYul.Flow.left, config := restored }]
                      | none => []
                  | FullYul.Flow.halted =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored =>
                          [{ flow := FullYul.Flow.halted, config := restored }]
                      | none => [])
                (evalStmtFuel fuel branchConfig body)
            else
              match restoreBlockConfig outer branchConfig with
              | some restored => [normalResult restored]
              | none => [])
          (branchOn value condConfig) :=
    List.mem_flatMap.mpr
      ⟨(true, branchConfig), hBranchMem, hGenerated⟩
  simpa [evalForFuel, hCond] using hFlat

private theorem guidedEvalFor_body_terminal_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyFlow : FullYul.Flow}
    {bodyGuidedConfig restoredGuided : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBodyFlow : loopTerminalFlow bodyFlow)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult))
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig =
        some restoredGuided) :
    GuidedResultCovered model
      (loopRestoredGuidedResult bodyFlow restoredGuided)
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult) := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨concreteBodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hConcreteBodyFlow, hBodyConfig⟩
  cases hConcreteBodyFlow
  cases hBodyConfig
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatBody
  exact
    ⟨loopRestoredResult bodyFlow restored,
      evalFor_body_terminal_mem hCond hBranchMemTrue hBodyFlow hBodyMem
        hRestore,
      by simp [erase_loopRestoredResult, hEraseRestored],
      loopRestoredResult_satisfies hSatRestored⟩

private theorem evalFor_post_terminal_mem
    {fuel : Nat} {outer bodyConfig postConfig restored : Config}
    {cond : Expr} {post body : Stmt} {postFlow : FullYul.Flow}
    (hPostFlow : loopTerminalFlow postFlow)
    (hPostMem :
      ({ flow := postFlow, config := postConfig } : Result) ∈
        evalStmtFuel fuel bodyConfig post)
    (hRestore : restoreBlockConfig outer postConfig = some restored) :
    loopRestoredResult postFlow restored ∈
      List.flatMap
        (fun postResult =>
          match postResult.flow with
          | FullYul.Flow.normal
          | FullYul.Flow.continued =>
              evalForFuel fuel outer postResult.config cond post body
          | FullYul.Flow.broke =>
              match restoreBlockConfig outer postResult.config with
              | some restored => [normalResult restored]
              | none => []
          | FullYul.Flow.left =>
              match restoreBlockConfig outer postResult.config with
              | some restored =>
                  [{ flow := FullYul.Flow.left, config := restored }]
              | none => []
          | FullYul.Flow.halted =>
              match restoreBlockConfig outer postResult.config with
              | some restored =>
                  [{ flow := FullYul.Flow.halted, config := restored }]
              | none => [])
        (evalStmtFuel fuel bodyConfig post) := by
  rcases hPostFlow with hBroke | hLeftOrHalted
  · cases hBroke
    simp [loopRestoredResult]
    exact
      ⟨({ flow := FullYul.Flow.broke, config := postConfig } : Result),
        hPostMem,
        by simp [hRestore]⟩
  · rcases hLeftOrHalted with hLeft | hHalted
    · cases hLeft
      simp [loopRestoredResult]
      exact
        ⟨({ flow := FullYul.Flow.left, config := postConfig } : Result),
          hPostMem,
          by simp [hRestore]⟩
    · cases hHalted
      simp [loopRestoredResult]
      exact
        ⟨({ flow := FullYul.Flow.halted, config := postConfig } : Result),
          hPostMem,
          by simp [hRestore]⟩

private theorem evalFor_true_body_post_mem
    {fuel : Nat} {outer loopConfig condConfig branchConfig bodyConfig : Config}
    {cond : Expr} {post body : Stmt} {value : Value}
    {bodyFlow : FullYul.Flow} {target : Result}
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBranchMem : (true, branchConfig) ∈ branchOn value condConfig)
    (hBodyFlow :
      bodyFlow = FullYul.Flow.normal ∨ bodyFlow = FullYul.Flow.continued)
    (hBodyMem :
      ({ flow := bodyFlow, config := bodyConfig } : Result) ∈
        evalStmtFuel fuel branchConfig body)
    (hPostMem :
      target ∈
        List.flatMap
          (fun postResult =>
            match postResult.flow with
            | FullYul.Flow.normal
            | FullYul.Flow.continued =>
                evalForFuel fuel outer postResult.config cond post body
            | FullYul.Flow.broke =>
                match restoreBlockConfig outer postResult.config with
                | some restored => [normalResult restored]
                | none => []
            | FullYul.Flow.left =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.left, config := restored }]
                | none => []
            | FullYul.Flow.halted =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.halted, config := restored }]
                | none => [])
          (evalStmtFuel fuel bodyConfig post)) :
    target ∈ evalForFuel fuel.succ outer loopConfig cond post body := by
  have hBodyGenerated :
      target ∈
        (if true then
          List.flatMap
            (fun bodyResult =>
              match bodyResult.flow with
              | FullYul.Flow.normal
              | FullYul.Flow.continued =>
                  List.flatMap
                    (fun postResult =>
                      match postResult.flow with
                      | FullYul.Flow.normal
                      | FullYul.Flow.continued =>
                          evalForFuel fuel outer postResult.config cond post body
                      | FullYul.Flow.broke =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored => [normalResult restored]
                          | none => []
                      | FullYul.Flow.left =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.left, config := restored }]
                          | none => []
                      | FullYul.Flow.halted =>
                          match restoreBlockConfig outer postResult.config with
                          | some restored =>
                              [{ flow := FullYul.Flow.halted
                                 config := restored }]
                          | none => [])
                    (evalStmtFuel fuel bodyResult.config post)
              | FullYul.Flow.broke =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored => [normalResult restored]
                  | none => []
              | FullYul.Flow.left =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored =>
                      [{ flow := FullYul.Flow.left, config := restored }]
                  | none => []
              | FullYul.Flow.halted =>
                  match restoreBlockConfig outer bodyResult.config with
                  | some restored =>
                      [{ flow := FullYul.Flow.halted, config := restored }]
                  | none => [])
            (evalStmtFuel fuel branchConfig body)
        else
          match restoreBlockConfig outer branchConfig with
          | some restored => [normalResult restored]
          | none => []) := by
    rcases hBodyFlow with hNormal | hContinued
    · cases hNormal
      simp
      exact
        ⟨({ flow := FullYul.Flow.normal, config := bodyConfig } : Result),
          hBodyMem,
          hPostMem⟩
    · cases hContinued
      simp
      exact
        ⟨({ flow := FullYul.Flow.continued, config := bodyConfig } : Result),
          hBodyMem,
          hPostMem⟩
  have hFlat :
      target ∈
        List.flatMap
          (fun (takeBranch, branchConfig) =>
            if takeBranch then
              List.flatMap
                (fun bodyResult =>
                  match bodyResult.flow with
                  | FullYul.Flow.normal
                  | FullYul.Flow.continued =>
                      List.flatMap
                        (fun postResult =>
                          match postResult.flow with
                          | FullYul.Flow.normal
                          | FullYul.Flow.continued =>
                              evalForFuel fuel outer postResult.config cond post body
                          | FullYul.Flow.broke =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored => [normalResult restored]
                              | none => []
                          | FullYul.Flow.left =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.left
                                     config := restored }]
                              | none => []
                          | FullYul.Flow.halted =>
                              match restoreBlockConfig outer postResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.halted
                                     config := restored }]
                              | none => [])
                        (evalStmtFuel fuel bodyResult.config post)
                  | FullYul.Flow.broke =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored => [normalResult restored]
                      | none => []
                  | FullYul.Flow.left =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored =>
                          [{ flow := FullYul.Flow.left, config := restored }]
                      | none => []
                  | FullYul.Flow.halted =>
                      match restoreBlockConfig outer bodyResult.config with
                      | some restored =>
                          [{ flow := FullYul.Flow.halted, config := restored }]
                      | none => [])
                (evalStmtFuel fuel branchConfig body)
            else
              match restoreBlockConfig outer branchConfig with
              | some restored => [normalResult restored]
              | none => [])
          (branchOn value condConfig) :=
    List.mem_flatMap.mpr
      ⟨(true, branchConfig), hBranchMem, hBodyGenerated⟩
  simpa [evalForFuel, hCond] using hFlat

private theorem guidedEvalFor_body_post_terminal_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyFlow postFlow : FullYul.Flow}
    {bodyGuidedConfig postGuidedConfig restoredGuided : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBodyFlow : loopRecurFlow bodyFlow)
    (hPostFlow : loopTerminalFlow postFlow)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult))
    (hPostGuided :
      guidedEvalStmtFuel model fuel bodyGuidedConfig post =
        some ({ flow := postFlow, config := postGuidedConfig } : GuidedResult))
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) postGuidedConfig =
        some restoredGuided) :
    GuidedResultCovered model
      (loopRestoredGuidedResult postFlow restoredGuided)
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult) := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨concreteBodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hConcreteBodyFlow, hBodyConfig⟩
  cases hConcreteBodyFlow
  cases hBodyConfig
  have hPostGuidedBody :
      guidedEvalStmtFuel model fuel (erasePC bodyConfig) post =
        some ({ flow := postFlow, config := postGuidedConfig } : GuidedResult) := by
    simpa using hPostGuided
  rcases hPost hSatBody hPostGuidedBody with
    ⟨postResult, hPostMem, hErasePost, hSatPost⟩
  rcases postResult with ⟨concretePostFlow, postConfig⟩
  simp [eraseResult] at hErasePost
  rcases hErasePost with ⟨hConcretePostFlow, hPostConfig⟩
  cases hConcretePostFlow
  cases hPostConfig
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatPost
  have hPostGenerated :
      loopRestoredResult postFlow restored ∈
        List.flatMap
          (fun postResult =>
            match postResult.flow with
            | FullYul.Flow.normal
            | FullYul.Flow.continued =>
                evalForFuel fuel outer postResult.config cond post body
            | FullYul.Flow.broke =>
                match restoreBlockConfig outer postResult.config with
                | some restored => [normalResult restored]
                | none => []
            | FullYul.Flow.left =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.left, config := restored }]
                | none => []
            | FullYul.Flow.halted =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.halted, config := restored }]
                | none => [])
          (evalStmtFuel fuel bodyConfig post) :=
    evalFor_post_terminal_mem hPostFlow hPostMem hRestore
  have hMem :
      loopRestoredResult postFlow restored ∈
        evalForFuel fuel.succ outer loopConfig cond post body :=
    evalFor_true_body_post_mem hCond hBranchMemTrue hBodyFlow hBodyMem
      hPostGenerated
  exact
    ⟨loopRestoredResult postFlow restored,
      hMem,
      by simp [erase_loopRestoredResult, hEraseRestored],
      loopRestoredResult_satisfies hSatRestored⟩

private theorem guidedEvalFor_body_post_recur_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {value : Value} {condConfig : Config}
    {bodyFlow postFlow : FullYul.Flow}
    {bodyGuidedConfig postGuidedConfig : GuidedConfig}
    {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBodyFlow :
      bodyFlow = FullYul.Flow.normal ∨ bodyFlow = FullYul.Flow.continued)
    (hPostFlow :
      postFlow = FullYul.Flow.normal ∨ postFlow = FullYul.Flow.continued)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hRecur :
      ∀ {config' guidedRecur},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC outer) (erasePC config')
              cond post body =
            some guidedRecur ->
          GuidedResultCovered model guidedRecur
            (evalForFuel fuel outer config' cond post body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult))
    (hPostGuided :
      guidedEvalStmtFuel model fuel bodyGuidedConfig post =
        some ({ flow := postFlow, config := postGuidedConfig } : GuidedResult))
    (hRecurGuided :
      guidedEvalForFuel model fuel (erasePC outer) postGuidedConfig cond post
          body =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hPc := evalExpr_preserves_pc hCond
  have hSatCond : satisfies model condConfig.pc := by
    simpa [hPc] using hSat
  rcases branchOn_guidedBool_exists_satisfies_erasePC
      (value := value) hSound hSatCond with
    ⟨branchConfig, hBranchMem, hBranchSat, hBranchErase⟩
  have hBranchMemTrue :
      (true, branchConfig) ∈ branchOn value condConfig := by
    simpa [hBool] using hBranchMem
  have hBodyGuidedBranch :
      guidedEvalStmtFuel model fuel (erasePC branchConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult) := by
    simpa [hBranchErase] using hBodyGuided
  rcases hBody hBranchSat hBodyGuidedBranch with
    ⟨bodyResult, hBodyMem, hEraseBody, hSatBody⟩
  rcases bodyResult with ⟨concreteBodyFlow, bodyConfig⟩
  simp [eraseResult] at hEraseBody
  rcases hEraseBody with ⟨hConcreteBodyFlow, hBodyConfig⟩
  cases hConcreteBodyFlow
  cases hBodyConfig
  have hPostGuidedBody :
      guidedEvalStmtFuel model fuel (erasePC bodyConfig) post =
        some ({ flow := postFlow, config := postGuidedConfig } : GuidedResult) := by
    simpa using hPostGuided
  rcases hPost hSatBody hPostGuidedBody with
    ⟨postResult, hPostMem, hErasePost, hSatPost⟩
  rcases postResult with ⟨concretePostFlow, postConfig⟩
  simp [eraseResult] at hErasePost
  rcases hErasePost with ⟨hConcretePostFlow, hPostConfig⟩
  cases hConcretePostFlow
  cases hPostConfig
  have hRecurGuidedPost :
      guidedEvalForFuel model fuel (erasePC outer) (erasePC postConfig) cond
          post body =
        some guidedResult := by
    simpa using hRecurGuided
  rcases hRecur hSatPost hRecurGuidedPost with
    ⟨result, hRecurMem, hEraseRecur, hSatRecur⟩
  have hPostGenerated :
      result ∈
        List.flatMap
          (fun postResult =>
            match postResult.flow with
            | FullYul.Flow.normal
            | FullYul.Flow.continued =>
                evalForFuel fuel outer postResult.config cond post body
            | FullYul.Flow.broke =>
                match restoreBlockConfig outer postResult.config with
                | some restored => [normalResult restored]
                | none => []
            | FullYul.Flow.left =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.left, config := restored }]
                | none => []
            | FullYul.Flow.halted =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.halted, config := restored }]
                | none => [])
          (evalStmtFuel fuel bodyConfig post) := by
    rcases hPostFlow with hNormal | hContinued
    · cases hNormal
      simp
      exact
        ⟨({ flow := FullYul.Flow.normal, config := postConfig } : Result),
          hPostMem,
          hRecurMem⟩
    · cases hContinued
      simp
      exact
        ⟨({ flow := FullYul.Flow.continued, config := postConfig } : Result),
          hPostMem,
          hRecurMem⟩
  have hMem : result ∈ evalForFuel fuel.succ outer loopConfig cond post body :=
    evalFor_true_body_post_mem hCond hBranchMemTrue hBodyFlow hBodyMem
      hPostGenerated
  exact ⟨result, hMem, hEraseRecur, hSatRecur⟩

private theorem guidedEvalFor_body_terminal_sound_of_guided
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    {value : Value} {condConfig : Config}
    {bodyFlow : FullYul.Flow}
    {bodyGuidedConfig : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBodyFlow : loopTerminalFlow bodyFlow)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult))
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  cases hRestoreGuided :
      restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig with
  | none =>
      simp [guidedEvalForFuel] at hGuided
      rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
      exact
        loopTerminalFlow_elim hBodyFlow
          (fun hBroke => by
            cases hBroke
            simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided)
          (fun hLeft => by
            cases hLeft
            simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided)
          (fun hHalted => by
            cases hHalted
            simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided)
  | some restoredGuided =>
      have hGuidedEq :
          guidedResult = loopRestoredGuidedResult bodyFlow restoredGuided := by
        simp [guidedEvalForFuel] at hGuided
        rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
        exact
          loopTerminalFlow_elim hBodyFlow
            (fun hBroke => by
              cases hBroke
              simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided
              cases hGuided
              rfl)
            (fun hLeft => by
              cases hLeft
              simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided
              cases hGuided
              rfl)
            (fun hHalted => by
              cases hHalted
              simp [hCond, hBool, hBodyGuided, hRestoreGuided] at hGuided
              cases hGuided
              rfl)
      cases hGuidedEq
      exact
        guidedEvalFor_body_terminal_sound_of (hSound := hSound)
          hSat hCond hBool hBodyFlow hBody hBodyGuided hRestoreGuided

private theorem guidedEvalFor_body_recur_sound_of_guided
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    {value : Value} {condConfig : Config}
    {bodyFlow : FullYul.Flow}
    {bodyGuidedConfig : GuidedConfig}
    (hSat : satisfies model loopConfig.pc)
    (hCond : evalExpr loopConfig cond = some (value, condConfig))
    (hBool : guidedBool model value = true)
    (hBodyFlow : loopRecurFlow bodyFlow)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hRecur :
      ∀ {config' guidedRecur},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC outer) (erasePC config')
              cond post body =
            some guidedRecur ->
          GuidedResultCovered model guidedRecur
            (evalForFuel fuel outer config' cond post body))
    (hBodyGuided :
      guidedEvalStmtFuel model fuel (erasePC condConfig) body =
        some ({ flow := bodyFlow, config := bodyGuidedConfig } : GuidedResult))
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  rcases hBodyFlow with hBodyNormal | hBodyContinued
  · cases hBodyNormal
    cases hPostEval :
        guidedEvalStmtFuel model fuel bodyGuidedConfig post with
    | none =>
        simp [guidedEvalForFuel] at hGuided
        rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
        simp [hCond, hBool, hBodyGuided, hPostEval] at hGuided
    | some guidedPost =>
        rcases guidedPost with ⟨postFlow, postGuidedConfig⟩
        rcases loopFlow_recur_or_terminal postFlow with
          hPostRecur | hPostTerminal
        · rcases hPostRecur with hPostNormal | hPostContinued
          · cases hPostNormal
            cases hRecurEval :
                guidedEvalForFuel model fuel (erasePC outer)
                  postGuidedConfig cond post body with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
            | some guidedRecur =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
                cases hGuided
                exact
                  guidedEvalFor_body_post_recur_sound_of (hSound := hSound)
                    hSat hCond hBool (by simp) (by simp) hBody hPost hRecur
                    hBodyGuided hPostEval hRecurEval
          · cases hPostContinued
            cases hRecurEval :
                guidedEvalForFuel model fuel (erasePC outer)
                  postGuidedConfig cond post body with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
            | some guidedRecur =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
                cases hGuided
                exact
                  guidedEvalFor_body_post_recur_sound_of (hSound := hSound)
                    hSat hCond hBool (by simp) (by simp) hBody hPost hRecur
                    hBodyGuided hPostEval hRecurEval
        · rcases hPostTerminal with hPostBroke | hPostLeftOrHalted
          · cases hPostBroke
            cases hRestoreGuided :
                restoreGuidedBlockConfig (erasePC outer)
                  postGuidedConfig with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRestoreGuided]
                  at hGuided
            | some restoredGuided =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRestoreGuided]
                  at hGuided
                cases hGuided
                simpa [loopRestoredGuidedResult] using
                  guidedEvalFor_body_post_terminal_sound_of
                    (hSound := hSound) hSat hCond hBool
                    (by simp [loopRecurFlow]) (by simp [loopTerminalFlow])
                    hBody hPost hBodyGuided hPostEval hRestoreGuided
          · rcases hPostLeftOrHalted with hPostLeft | hPostHalted
            · cases hPostLeft
              cases hRestoreGuided :
                  restoreGuidedBlockConfig (erasePC outer)
                    postGuidedConfig with
              | none =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
              | some restoredGuided =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
                  cases hGuided
                  simpa [loopRestoredGuidedResult] using
                    guidedEvalFor_body_post_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (by simp [loopRecurFlow])
                      (by simp [loopTerminalFlow]) hBody hPost hBodyGuided
                      hPostEval hRestoreGuided
            · cases hPostHalted
              cases hRestoreGuided :
                  restoreGuidedBlockConfig (erasePC outer)
                    postGuidedConfig with
              | none =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
              | some restoredGuided =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
                  cases hGuided
                  simpa [loopRestoredGuidedResult] using
                    guidedEvalFor_body_post_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (by simp [loopRecurFlow])
                      (by simp [loopTerminalFlow]) hBody hPost hBodyGuided
                      hPostEval hRestoreGuided
  · cases hBodyContinued
    cases hPostEval :
        guidedEvalStmtFuel model fuel bodyGuidedConfig post with
    | none =>
        simp [guidedEvalForFuel] at hGuided
        rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
        simp [hCond, hBool, hBodyGuided, hPostEval] at hGuided
    | some guidedPost =>
        rcases guidedPost with ⟨postFlow, postGuidedConfig⟩
        rcases loopFlow_recur_or_terminal postFlow with
          hPostRecur | hPostTerminal
        · rcases hPostRecur with hPostNormal | hPostContinued
          · cases hPostNormal
            cases hRecurEval :
                guidedEvalForFuel model fuel (erasePC outer)
                  postGuidedConfig cond post body with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
            | some guidedRecur =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
                cases hGuided
                exact
                  guidedEvalFor_body_post_recur_sound_of (hSound := hSound)
                    hSat hCond hBool (by simp) (by simp) hBody hPost hRecur
                    hBodyGuided hPostEval hRecurEval
          · cases hPostContinued
            cases hRecurEval :
                guidedEvalForFuel model fuel (erasePC outer)
                  postGuidedConfig cond post body with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
            | some guidedRecur =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRecurEval]
                  at hGuided
                cases hGuided
                exact
                  guidedEvalFor_body_post_recur_sound_of (hSound := hSound)
                    hSat hCond hBool (by simp) (by simp) hBody hPost hRecur
                    hBodyGuided hPostEval hRecurEval
        · rcases hPostTerminal with hPostBroke | hPostLeftOrHalted
          · cases hPostBroke
            cases hRestoreGuided :
                restoreGuidedBlockConfig (erasePC outer)
                  postGuidedConfig with
            | none =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRestoreGuided]
                  at hGuided
            | some restoredGuided =>
                simp [guidedEvalForFuel] at hGuided
                rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                simp [hCond, hBool, hBodyGuided, hPostEval, hRestoreGuided]
                  at hGuided
                cases hGuided
                simpa [loopRestoredGuidedResult] using
                  guidedEvalFor_body_post_terminal_sound_of
                    (hSound := hSound) hSat hCond hBool
                    (by simp [loopRecurFlow]) (by simp [loopTerminalFlow])
                    hBody hPost hBodyGuided hPostEval hRestoreGuided
          · rcases hPostLeftOrHalted with hPostLeft | hPostHalted
            · cases hPostLeft
              cases hRestoreGuided :
                  restoreGuidedBlockConfig (erasePC outer)
                    postGuidedConfig with
              | none =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
              | some restoredGuided =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
                  cases hGuided
                  simpa [loopRestoredGuidedResult] using
                    guidedEvalFor_body_post_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (by simp [loopRecurFlow])
                      (by simp [loopTerminalFlow]) hBody hPost hBodyGuided
                      hPostEval hRestoreGuided
            · cases hPostHalted
              cases hRestoreGuided :
                  restoreGuidedBlockConfig (erasePC outer)
                    postGuidedConfig with
              | none =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
              | some restoredGuided =>
                  simp [guidedEvalForFuel] at hGuided
                  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
                  simp [hCond, hBool, hBodyGuided, hPostEval,
                    hRestoreGuided] at hGuided
                  cases hGuided
                  simpa [loopRestoredGuidedResult] using
                    guidedEvalFor_body_post_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (by simp [loopRecurFlow])
                      (by simp [loopTerminalFlow]) hBody hPost hBodyGuided
                      hPostEval hRestoreGuided

private theorem guidedEvalFor_sound_of_exhaustive
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hRecur :
      ∀ {config' guidedRecur},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC outer) (erasePC config')
              cond post body =
            some guidedRecur ->
          GuidedResultCovered model guidedRecur
            (evalForFuel fuel outer config' cond post body))
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hGuidedOrig := hGuided
  simp [guidedEvalForFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
  cases hCond : evalExpr loopConfig cond with
  | none =>
      simp [hCond] at hGuided
  | some evaluatedCond =>
      rcases evaluatedCond with ⟨value, condConfig⟩
      simp [hCond] at hGuided
      cases hBool : guidedBool model value
      · exact
          guidedEvalFor_false_sound_of_cond
            (hSound := hSound) hSat hCond hBool hGuidedOrig
      · cases hBodyEval :
            guidedEvalStmtFuel model fuel (erasePC condConfig) body with
        | none =>
            simp [hBool, hBodyEval] at hGuided
        | some guidedBody =>
            rcases guidedBody with ⟨bodyFlow, bodyGuidedConfig⟩
            cases bodyFlow
            · cases hPostEval :
                  guidedEvalStmtFuel model fuel bodyGuidedConfig post with
              | none =>
                  simp [hBool, hBodyEval, hPostEval] at hGuided
              | some guidedPost =>
                  rcases guidedPost with ⟨postFlow, postGuidedConfig⟩
                  cases postFlow
                  · cases hRecurEval :
                        guidedEvalForFuel model fuel (erasePC outer)
                          postGuidedConfig cond post body with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                    | some guidedRecur =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_recur_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inl rfl) (Or.inl rfl) hBody hPost hRecur
                            hBodyEval hPostEval hRecurEval
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inl rfl) (Or.inl rfl) hBody hPost
                            hBodyEval hPostEval hRestore
                  · cases hRecurEval :
                        guidedEvalForFuel model fuel (erasePC outer)
                          postGuidedConfig cond post body with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                    | some guidedRecur =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_recur_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inl rfl) (Or.inr rfl) hBody hPost hRecur
                            hBodyEval hPostEval hRecurEval
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inl rfl) (Or.inr (Or.inl rfl)) hBody hPost
                            hBodyEval hPostEval
                            hRestore
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inl rfl) (Or.inr (Or.inr rfl)) hBody hPost
                            hBodyEval hPostEval
                            hRestore
            · cases hRestore :
                  restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig with
              | none =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
              | some restoredGuided =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
                  cases hGuided
                  exact
                    guidedEvalFor_body_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool (Or.inl rfl)
                      hBody hBodyEval hRestore
            · cases hPostEval :
                  guidedEvalStmtFuel model fuel bodyGuidedConfig post with
              | none =>
                  simp [hBool, hBodyEval, hPostEval] at hGuided
              | some guidedPost =>
                  rcases guidedPost with ⟨postFlow, postGuidedConfig⟩
                  cases postFlow
                  · cases hRecurEval :
                        guidedEvalForFuel model fuel (erasePC outer)
                          postGuidedConfig cond post body with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                    | some guidedRecur =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_recur_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inr rfl) (Or.inl rfl) hBody hPost hRecur
                            hBodyEval hPostEval hRecurEval
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inr rfl) (Or.inl rfl) hBody hPost
                            hBodyEval hPostEval hRestore
                  · cases hRecurEval :
                        guidedEvalForFuel model fuel (erasePC outer)
                          postGuidedConfig cond post body with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                    | some guidedRecur =>
                        simp [hBool, hBodyEval, hPostEval, hRecurEval] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_recur_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inr rfl) (Or.inr rfl) hBody hPost hRecur
                            hBodyEval hPostEval hRecurEval
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inr rfl) (Or.inr (Or.inl rfl)) hBody hPost
                            hBodyEval hPostEval
                            hRestore
                  · cases hRestore :
                        restoreGuidedBlockConfig (erasePC outer)
                          postGuidedConfig with
                    | none =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                    | some restoredGuided =>
                        simp [hBool, hBodyEval, hPostEval, hRestore] at hGuided
                        cases hGuided
                        exact
                          guidedEvalFor_body_post_terminal_sound_of
                            (hSound := hSound) hSat hCond hBool
                            (Or.inr rfl) (Or.inr (Or.inr rfl)) hBody hPost
                            hBodyEval hPostEval
                            hRestore
            · cases hRestore :
                  restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig with
              | none =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
              | some restoredGuided =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
                  cases hGuided
                  exact
                    guidedEvalFor_body_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (Or.inr (Or.inl rfl)) hBody hBodyEval hRestore
            · cases hRestore :
                  restoreGuidedBlockConfig (erasePC outer) bodyGuidedConfig with
              | none =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
              | some restoredGuided =>
                  simp [hBool, hBodyEval, hRestore] at hGuided
                  cases hGuided
                  exact
                    guidedEvalFor_body_terminal_sound_of
                      (hSound := hSound) hSat hCond hBool
                      (Or.inr (Or.inr rfl)) hBody hBodyEval hRestore

private theorem guidedEvalFor_sound_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hRecur :
      ∀ {config' guidedRecur},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC outer) (erasePC config')
              cond post body =
            some guidedRecur ->
          GuidedResultCovered model guidedRecur
            (evalForFuel fuel outer config' cond post body))
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) := by
  have hGuidedOrig := hGuided
  simp [guidedEvalForFuel] at hGuided
  rw [guidedEvalExpr_erasePC_eq loopConfig cond] at hGuided
  cases hCond : evalExpr loopConfig cond with
  | none =>
      simp [hCond] at hGuided
  | some evaluatedCond =>
      rcases evaluatedCond with ⟨value, condConfig⟩
      simp [hCond] at hGuided
      cases hBool : guidedBool model value
      · exact
          guidedEvalFor_false_sound_of_cond
            (hSound := hSound) hSat hCond hBool hGuidedOrig
      · cases hBodyGuided :
            guidedEvalStmtFuel model fuel (erasePC condConfig) body with
        | none =>
            simp [hBool, hBodyGuided] at hGuided
        | some guidedBody =>
            rcases guidedBody with ⟨bodyFlow, bodyGuidedConfig⟩
            rcases loopFlow_recur_or_terminal bodyFlow with
              hBodyRecur | hBodyTerminal
            · exact
                guidedEvalFor_body_recur_sound_of_guided
                  (hSound := hSound) hSat hCond hBool hBodyRecur hBody
                  hPost hRecur hBodyGuided hGuidedOrig
            · exact
                guidedEvalFor_body_terminal_sound_of_guided
                  (hSound := hSound) hSat hCond hBool hBodyTerminal hBody
                  hBodyGuided hGuidedOrig

theorem guidedEvalFor_sound_of_compositional
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hBody :
      ∀ {config' guidedBody},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') body =
            some guidedBody ->
          GuidedResultCovered model guidedBody
            (evalStmtFuel fuel config' body))
    (hPost :
      ∀ {config' guidedPost},
        satisfies model config'.pc ->
          guidedEvalStmtFuel model fuel (erasePC config') post =
            some guidedPost ->
          GuidedResultCovered model guidedPost
            (evalStmtFuel fuel config' post))
    (hRecur :
      ∀ {config' guidedRecur},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC outer) (erasePC config')
              cond post body =
            some guidedRecur ->
          GuidedResultCovered model guidedRecur
            (evalForFuel fuel outer config' cond post body))
    (hGuided :
      guidedEvalForFuel model fuel.succ (erasePC outer) (erasePC loopConfig)
        cond post body = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel.succ outer loopConfig cond post body) :=
  guidedEvalFor_sound_of (hSound := hSound) hSat hBody hPost hRecur hGuided

private theorem evalStmt_forLoop_prelude_normal_mem
    {fuel : Nat} {config preConfig : Config}
    {pre : Stmt} {cond : Expr} {post body : Stmt}
    {target : Result}
    (hPreMem : normalResult preConfig ∈ evalStmtFuel fuel config pre)
    (hLoopMem : target ∈ evalForFuel fuel config preConfig cond post body) :
    target ∈
      evalStmtFuel fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body) := by
  change target ∈
    List.flatMap
      (fun preResult =>
        match preResult.flow with
        | FullYul.Flow.normal =>
            evalForFuel fuel config preResult.config cond post body
        | _ =>
            match withRestoredConfig config preResult with
            | some restored => [restored]
            | none => [])
      (evalStmtFuel fuel config pre)
  exact
    List.mem_flatMap.mpr
    ⟨normalResult preConfig, hPreMem, hLoopMem⟩

private theorem evalStmt_forLoop_prelude_restored_mem
    {fuel : Nat} {config preConfig restored : Config}
    {pre : Stmt} {cond : Expr} {post body : Stmt} {flow : FullYul.Flow}
    (hFlow : flow ≠ FullYul.Flow.normal)
    (hPreMem :
      ({ flow := flow, config := preConfig } : Result) ∈
        evalStmtFuel fuel config pre)
    (hRestore : restoreBlockConfig config preConfig = some restored) :
    ({ flow := flow, config := restored } : Result) ∈
      evalStmtFuel fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body) := by
  change ({ flow := flow, config := restored } : Result) ∈
    List.flatMap
      (fun preResult =>
        match preResult.flow with
        | FullYul.Flow.normal =>
            evalForFuel fuel config preResult.config cond post body
        | _ =>
            match withRestoredConfig config preResult with
            | some restored => [restored]
            | none => [])
      (evalStmtFuel fuel config pre)
  exact
    List.mem_flatMap.mpr
    ⟨({ flow := flow, config := preConfig } : Result),
      hPreMem,
      by
        cases flow
        · exact False.elim (hFlow rfl)
        · unfold withRestoredConfig
          rw [hRestore]
          simp
        · unfold withRestoredConfig
          rw [hRestore]
          simp
        · unfold withRestoredConfig
          rw [hRestore]
          simp
        · unfold withRestoredConfig
          rw [hRestore]
          simp⟩

private theorem guidedEvalStmt_forLoop_prelude_restored_sound_of
    {model : ConcreteModel} {fuel : Nat} {config preConfig : Config}
    {restoredGuided : GuidedConfig}
    {pre : Stmt} {cond : Expr} {post body : Stmt} {flow : FullYul.Flow}
    (hFlow : flow ≠ FullYul.Flow.normal)
    (hPreMem :
      ({ flow := flow, config := preConfig } : Result) ∈
        evalStmtFuel fuel config pre)
    (hSatPre : satisfies model preConfig.pc)
    (hRestoreGuided :
      restoreGuidedBlockConfig (erasePC config) (erasePC preConfig) =
        some restoredGuided) :
    GuidedResultCovered model
      ({ flow := flow, config := restoredGuided } : GuidedResult)
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body)) := by
  rcases restoreBlockConfig_of_restoreGuidedBlockConfig_erasePC
      hRestoreGuided with
    ⟨restored, hRestore, hEraseRestored⟩
  have hSatRestored : satisfies model restored.pc := by
    have hPath := (restoreBlockConfig_preserves_path_and_evm hRestore).1
    simpa [hPath] using hSatPre
  exact
    ⟨({ flow := flow, config := restored } : Result),
      evalStmt_forLoop_prelude_restored_mem hFlow hPreMem hRestore,
      by simp [eraseResult, hEraseRestored],
      hSatRestored⟩

private theorem guidedEvalStmt_forLoop_prelude_non_normal_sound_of
    {model : ConcreteModel} {fuel : Nat} {config preConfig : Config}
    {pre : Stmt} {cond : Expr} {post body : Stmt}
    {flow : FullYul.Flow} {guidedResult : GuidedResult}
    (hFlow : flow ≠ FullYul.Flow.normal)
    (hPreEval :
      guidedEvalStmtFuel model fuel (erasePC config) pre =
        some
          ({ flow := flow, config := erasePC preConfig } : GuidedResult))
    (hPreMem :
      ({ flow := flow, config := preConfig } : Result) ∈
        evalStmtFuel fuel config pre)
    (hSatPre : satisfies model preConfig.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.forLoop pre cond post body) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body)) := by
  cases flow
  · exact False.elim (hFlow rfl)
  all_goals
    simp [guidedEvalStmtFuel, hPreEval] at hGuided
    cases hRestoreGuided :
        restoreGuidedBlockConfig (erasePC config) (erasePC preConfig) with
    | none =>
        simp [withRestoredGuidedConfig, hRestoreGuided] at hGuided
    | some restoredGuided =>
        simp [withRestoredGuidedConfig, hRestoreGuided] at hGuided
        cases hGuided
        exact
          guidedEvalStmt_forLoop_prelude_restored_sound_of hFlow
            hPreMem hSatPre hRestoreGuided

theorem guidedEvalStmt_forLoop_sound_of
    {model : ConcreteModel}
    {fuel : Nat} {config : Config}
    {pre : Stmt} {cond : Expr} {post body : Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hPre :
      ∀ {guidedPre},
        satisfies model config.pc ->
          guidedEvalStmtFuel model fuel (erasePC config) pre =
            some guidedPre ->
          GuidedResultCovered model guidedPre
            (evalStmtFuel fuel config pre))
    (hLoop :
      ∀ {config' guidedLoop},
        satisfies model config'.pc ->
          guidedEvalForFuel model fuel (erasePC config) (erasePC config')
              cond post body =
            some guidedLoop ->
          GuidedResultCovered model guidedLoop
            (evalForFuel fuel config config' cond post body))
    (hGuided :
      guidedEvalStmtFuel model fuel.succ (erasePC config)
        (FullYul.Stmt.forLoop pre cond post body) = some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel.succ config
        (FullYul.Stmt.forLoop pre cond post body)) := by
  cases hPreEval : guidedEvalStmtFuel model fuel (erasePC config) pre with
  | none =>
      simp [guidedEvalStmtFuel, hPreEval] at hGuided
  | some guidedPre =>
      rcases guidedPre with ⟨preFlow, preGuidedConfig⟩
      have hPreCovered :
          GuidedResultCovered model
            ({ flow := preFlow, config := preGuidedConfig } : GuidedResult)
            (evalStmtFuel fuel config pre) :=
        hPre hSat hPreEval
      rcases hPreCovered with ⟨preResult, hPreMem, hErasePre, hSatPre⟩
      rcases preResult with ⟨concretePreFlow, preConfig⟩
      simp [eraseResult] at hErasePre
      rcases hErasePre with ⟨hConcretePreFlow, hPreConfig⟩
      cases hConcretePreFlow
      cases hPreConfig
      by_cases hPreFlowNormal : preFlow = FullYul.Flow.normal
      · cases hPreFlowNormal
        simp [guidedEvalStmtFuel, hPreEval] at hGuided
        rcases hLoop hSatPre hGuided with
          ⟨result, hLoopMem, hEraseLoop, hSatLoop⟩
        exact
          ⟨result,
            evalStmt_forLoop_prelude_normal_mem hPreMem hLoopMem,
            hEraseLoop,
            hSatLoop⟩
      · exact
          guidedEvalStmt_forLoop_prelude_non_normal_sound_of
            hPreFlowNormal hPreEval hPreMem hSatPre hGuided

def GuidedStmtSoundAt (model : ConcreteModel) (fuel : Nat) : Prop :=
  ∀ {config : Config} {stmt : Stmt} {guidedResult : GuidedResult},
    satisfies model config.pc ->
      guidedEvalStmtFuel model fuel (erasePC config) stmt =
        some guidedResult ->
      GuidedResultCovered model guidedResult (evalStmtFuel fuel config stmt)

def GuidedBlockSoundAt (model : ConcreteModel) (fuel : Nat) : Prop :=
  ∀ {config : Config} {stmts : List Stmt} {guidedResult : GuidedResult},
    satisfies model config.pc ->
      guidedEvalBlockFuel model fuel (erasePC config) stmts =
        some guidedResult ->
      GuidedResultCovered model guidedResult (evalBlockFuel fuel config stmts)

def GuidedForSoundAt (model : ConcreteModel) (fuel : Nat) : Prop :=
  ∀ {outer loopConfig : Config} {cond : Expr} {post body : Stmt}
      {guidedResult : GuidedResult},
    satisfies model loopConfig.pc ->
      guidedEvalForFuel model fuel (erasePC outer) (erasePC loopConfig)
          cond post body =
        some guidedResult ->
      GuidedResultCovered model guidedResult
        (evalForFuel fuel outer loopConfig cond post body)

def GuidedFunctionSoundAt (model : ConcreteModel) (fuel : Nat) : Prop :=
  ∀ {config : Config} {fnName : FullYul.Name} {args values : List Value}
      {guidedConfig : GuidedConfig},
    satisfies model config.pc ->
      guidedEvalFunctionFuel model fuel (erasePC config) fnName args =
        some (values, guidedConfig) ->
      ∃ config',
        (values, config') ∈ evalFunctionFuel fuel config fnName args ∧
          erasePC config' = guidedConfig ∧
          satisfies model config'.pc

theorem guidedStmtSoundAt_succ_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat}
    (hStmt : GuidedStmtSoundAt model fuel)
    (hBlock : GuidedBlockSoundAt model fuel)
    (hFor : GuidedForSoundAt model fuel)
    (hFunction : GuidedFunctionSoundAt model fuel) :
    GuidedStmtSoundAt model fuel.succ := by
  intro config stmt guidedResult hSat hGuided
  cases stmt with
  | skip =>
      exact guidedEvalStmt_skip_sound hSat hGuided
  | expr expr =>
      exact guidedEvalStmt_expr_sound hSat hGuided
  | let1 name init =>
      cases init with
      | none =>
          exact guidedEvalStmt_let1_default_sound hSat hGuided
      | some init =>
          exact guidedEvalStmt_let1_init_sound hSat hGuided
  | letMany names init =>
      cases init with
      | none =>
          exact guidedEvalStmt_letMany_default_sound hSat hGuided
      | some init =>
          exact guidedEvalStmt_letMany_init_sound hSat hGuided
  | funDef fnName params returns body =>
      exact guidedEvalStmt_funDef_sound hSat hGuided
  | assign name expr =>
      exact guidedEvalStmt_assign_sound hSat hGuided
  | assignMany names exprs =>
      exact guidedEvalStmt_assignMany_sound hSat hGuided
  | letCall names fnName args =>
      exact
        guidedEvalStmt_letCall_sound_of hSat
          (by
            intro configAfterArgs argValues returnValues guidedAfter hSatArgs
              hGuidedFunction
            exact hFunction hSatArgs hGuidedFunction)
          hGuided
  | assignCall names fnName args =>
      exact
        guidedEvalStmt_assignCall_sound_of hSat
          (by
            intro configAfterArgs argValues returnValues guidedAfter hSatArgs
              hGuidedFunction
            exact hFunction hSatArgs hGuidedFunction)
          hGuided
  | seq first second =>
      exact
        guidedEvalStmt_seq_sound_of hSat
          (by
            intro guidedFirst hSatFirst hGuidedFirst
            exact hStmt hSatFirst hGuidedFirst)
          (by
            intro config' guidedSecond hSatSecond hGuidedSecond
            exact hStmt hSatSecond hGuidedSecond)
          hGuided
  | block stmts =>
      exact
        guidedEvalStmt_block_sound_of hSat
          (by
            intro guidedBlock hSatBlock hGuidedBlock
            exact hBlock hSatBlock hGuidedBlock)
          hGuided
  | ifThen cond body =>
      exact
        guidedEvalStmt_ifThen_sound_of hSound hSat
          (by
            intro config' guidedBody hSatBody hGuidedBody
            exact hStmt hSatBody hGuidedBody)
          hGuided
  | switch discr cases defaultBranch =>
      exact
        guidedEvalStmt_switch_sound_of hSound hSat
          (by
            intro config' branch guidedBranch hSatBranch hGuidedBranch
            exact hStmt hSatBranch hGuidedBranch)
          hGuided
  | forLoop pre cond post body =>
      exact
        guidedEvalStmt_forLoop_sound_of hSat
          (by
            intro guidedPre hSatPre hGuidedPre
            exact hStmt hSatPre hGuidedPre)
          (by
            intro config' guidedLoop hSatLoop hGuidedLoop
            exact hFor hSatLoop hGuidedLoop)
          hGuided
  | «break» =>
      exact guidedEvalStmt_break_sound hSat hGuided
  | «continue» =>
      exact guidedEvalStmt_continue_sound hSat hGuided
  | «leave» =>
      exact guidedEvalStmt_leave_sound hSat hGuided

theorem guidedBlockSoundAt_succ_of
    {model : ConcreteModel} {fuel : Nat}
    (hStmt : GuidedStmtSoundAt model fuel)
    (hBlock : GuidedBlockSoundAt model fuel) :
    GuidedBlockSoundAt model fuel.succ := by
  intro config stmts guidedResult hSat hGuided
  cases stmts with
  | nil =>
      exact guidedEvalBlock_nil_sound hSat hGuided
  | cons stmt rest =>
      exact
        guidedEvalBlock_cons_sound_of hSat
          (by
            intro guidedStmt hSatStmt hGuidedStmt
            exact hStmt hSatStmt hGuidedStmt)
          (by
            intro config' guidedRest hSatRest hGuidedRest
            exact hBlock hSatRest hGuidedRest)
          hGuided

theorem guidedForSoundAt_succ_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat}
    (hStmt : GuidedStmtSoundAt model fuel)
    (hFor : GuidedForSoundAt model fuel) :
    GuidedForSoundAt model fuel.succ := by
  intro outer loopConfig cond post body guidedResult hSat hGuided
  exact
    guidedEvalFor_sound_of_compositional (hSound := hSound) hSat
      (by
        intro config' guidedBody hSatBody hGuidedBody
        exact hStmt hSatBody hGuidedBody)
      (by
        intro config' guidedPost hSatPost hGuidedPost
        exact hStmt hSatPost hGuidedPost)
      (by
        intro config' guidedRecur hSatRecur hGuidedRecur
        exact hFor hSatRecur hGuidedRecur)
      hGuided

theorem guidedFunctionSoundAt_succ_of
    {model : ConcreteModel} {fuel : Nat}
    (hStmt : GuidedStmtSoundAt model fuel) :
    GuidedFunctionSoundAt model fuel.succ := by
  intro config fnName args values guidedConfig hSat hGuided
  exact
    guidedEvalFunctionFuel_sound_of_body hSat
      (by
        intro fn callEnv guidedBody hLookup hInit callConfig hSatCall
          hGuidedBody
        exact hStmt hSatCall hGuidedBody)
      hGuided

theorem guidedSoundAt_zero (model : ConcreteModel) :
    GuidedStmtSoundAt model 0 ∧
      GuidedBlockSoundAt model 0 ∧
      GuidedForSoundAt model 0 ∧
      GuidedFunctionSoundAt model 0 := by
  constructor
  · intro config stmt guidedResult hSat hGuided
    simp [guidedEvalStmtFuel] at hGuided
  constructor
  · intro config stmts guidedResult hSat hGuided
    simp [guidedEvalBlockFuel] at hGuided
  constructor
  · intro outer loopConfig cond post body guidedResult hSat hGuided
    simp [guidedEvalForFuel] at hGuided
  · intro config fnName args values guidedConfig hSat hGuided
    simp [guidedEvalFunctionFuel] at hGuided

theorem guidedSoundAt_succ_of
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat}
    (hSoundAt :
      GuidedStmtSoundAt model fuel ∧
        GuidedBlockSoundAt model fuel ∧
        GuidedForSoundAt model fuel ∧
        GuidedFunctionSoundAt model fuel) :
    GuidedStmtSoundAt model fuel.succ ∧
      GuidedBlockSoundAt model fuel.succ ∧
      GuidedForSoundAt model fuel.succ ∧
      GuidedFunctionSoundAt model fuel.succ := by
  rcases hSoundAt with ⟨hStmt, hBlock, hFor, hFunction⟩
  exact
    ⟨ guidedStmtSoundAt_succ_of hSound hStmt hBlock hFor hFunction
    , guidedBlockSoundAt_succ_of hStmt hBlock
    , guidedForSoundAt_succ_of hSound hStmt hFor
    , guidedFunctionSoundAt_succ_of hStmt ⟩

theorem guidedSoundAt_all
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    (fuel : Nat) :
    GuidedStmtSoundAt model fuel ∧
      GuidedBlockSoundAt model fuel ∧
      GuidedForSoundAt model fuel ∧
      GuidedFunctionSoundAt model fuel := by
  induction fuel with
  | zero =>
      exact guidedSoundAt_zero model
  | succ fuel ih =>
      exact guidedSoundAt_succ_of hSound ih

theorem guidedEvalStmtFuel_sound
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {config : Config} {stmt : Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel (erasePC config) stmt =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel config stmt) :=
  (guidedSoundAt_all hSound fuel).1 hSat hGuided

theorem guidedEvalBlockFuel_sound
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {config : Config} {stmts : List Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalBlockFuel model fuel (erasePC config) stmts =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalBlockFuel fuel config stmts) :=
  (guidedSoundAt_all hSound fuel).2.1 hSat hGuided

theorem guidedEvalForFuel_sound
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hGuided :
      guidedEvalForFuel model fuel (erasePC outer) (erasePC loopConfig)
          cond post body =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel outer loopConfig cond post body) :=
  (guidedSoundAt_all hSound fuel).2.2.1 hSat hGuided

theorem guidedEvalFunctionFuel_sound
    {model : ConcreteModel} (hSound : KnownEqSoundForModel model)
    {fuel : Nat} {config : Config} {fnName : FullYul.Name}
    {args values : List Value} {guidedConfig : GuidedConfig}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalFunctionFuel model fuel (erasePC config) fnName args =
        some (values, guidedConfig)) :
    ∃ config',
      (values, config') ∈ evalFunctionFuel fuel config fnName args ∧
        erasePC config' = guidedConfig ∧
        satisfies model config'.pc :=
  (guidedSoundAt_all hSound fuel).2.2.2 hSat hGuided

theorem guidedEvalStmtFuel_sound_of_hash_injective
    {model : ConcreteModel} (hHash : HashInjectiveForModel model)
    {fuel : Nat} {config : Config} {stmt : Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalStmtFuel model fuel (erasePC config) stmt =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalStmtFuel fuel config stmt) :=
  guidedEvalStmtFuel_sound (knownEqSoundForModel_of_hash_injective hHash)
    hSat hGuided

theorem guidedEvalBlockFuel_sound_of_hash_injective
    {model : ConcreteModel} (hHash : HashInjectiveForModel model)
    {fuel : Nat} {config : Config} {stmts : List Stmt}
    {guidedResult : GuidedResult}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalBlockFuel model fuel (erasePC config) stmts =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalBlockFuel fuel config stmts) :=
  guidedEvalBlockFuel_sound (knownEqSoundForModel_of_hash_injective hHash)
    hSat hGuided

theorem guidedEvalForFuel_sound_of_hash_injective
    {model : ConcreteModel} (hHash : HashInjectiveForModel model)
    {fuel : Nat} {outer loopConfig : Config} {cond : Expr}
    {post body : Stmt} {guidedResult : GuidedResult}
    (hSat : satisfies model loopConfig.pc)
    (hGuided :
      guidedEvalForFuel model fuel (erasePC outer) (erasePC loopConfig)
          cond post body =
        some guidedResult) :
    GuidedResultCovered model guidedResult
      (evalForFuel fuel outer loopConfig cond post body) :=
  guidedEvalForFuel_sound (knownEqSoundForModel_of_hash_injective hHash)
    hSat hGuided

theorem guidedEvalFunctionFuel_sound_of_hash_injective
    {model : ConcreteModel} (hHash : HashInjectiveForModel model)
    {fuel : Nat} {config : Config} {fnName : FullYul.Name}
    {args values : List Value} {guidedConfig : GuidedConfig}
    (hSat : satisfies model config.pc)
    (hGuided :
      guidedEvalFunctionFuel model fuel (erasePC config) fnName args =
        some (values, guidedConfig)) :
    ∃ config',
      (values, config') ∈ evalFunctionFuel fuel config fnName args ∧
        erasePC config' = guidedConfig ∧
        satisfies model config'.pc :=
  guidedEvalFunctionFuel_sound
    (knownEqSoundForModel_of_hash_injective hHash) hSat hGuided

theorem Config.empty_satisfies (model : ConcreteModel) :
    satisfies model Config.empty.pc := by
  intro constraint hMem
  simp [Config.empty] at hMem

theorem guidedEvalFunctionFuel_restores_caller_frame
    {model : ConcreteModel} {fuel : Nat} {config afterConfig : GuidedConfig}
    {fnName : FullYul.Name} {args values : List Value}
    (h : guidedEvalFunctionFuel model fuel config fnName args =
      some (values, afterConfig)) :
    afterConfig.env = config.env ∧ afterConfig.funcs = config.funcs := by
  cases fuel with
  | zero =>
      simp [guidedEvalFunctionFuel] at h
  | succ fuel =>
      simp [guidedEvalFunctionFuel] at h
      repeat
        first
        | split at h
        | contradiction
        | cases h; constructor <;> rfl

theorem addConstraint_concrete_false_rejected :
    addConstraint? (Constraint.iszero (FullYul.Value.word 7)) Config.empty = none := by
  rfl

theorem evalStmtFuel_zero (config : Config) (stmt : Stmt) :
    evalStmtFuel 0 config stmt = [] := by
  rfl

theorem evalBlockFuel_zero (config : Config) (stmts : List Stmt) :
    evalBlockFuel 0 config stmts = [] := by
  rfl

theorem evalForFuel_zero
    (outer loopConfig : Config) (cond : Expr) (post body : Stmt) :
    evalForFuel 0 outer loopConfig cond post body = [] := by
  rfl

structure LoopSummary
    (outer : Config) (cond : Expr) (post body : Stmt)
    (headInv bodyInv postInv : Config -> Prop)
    (resultOK : Result -> Prop) : Prop where
  condTrue :
    ∀ {loopConfig value condConfig branchConfig},
      headInv loopConfig ->
        evalExpr loopConfig cond = some (value, condConfig) ->
          (true, branchConfig) ∈ branchOn value condConfig ->
            bodyInv branchConfig
  condFalse :
    ∀ {loopConfig value condConfig branchConfig restored},
      headInv loopConfig ->
        evalExpr loopConfig cond = some (value, condConfig) ->
          (false, branchConfig) ∈ branchOn value condConfig ->
            restoreBlockConfig outer branchConfig = some restored ->
              resultOK (normalResult restored)
  bodyRecur :
    ∀ {fuel branchConfig bodyResult},
      bodyInv branchConfig ->
        bodyResult ∈ evalStmtFuel fuel branchConfig body ->
          loopRecurFlow bodyResult.flow ->
            postInv bodyResult.config
  bodyTerminal :
    ∀ {fuel branchConfig bodyResult restored},
      bodyInv branchConfig ->
        bodyResult ∈ evalStmtFuel fuel branchConfig body ->
          loopTerminalFlow bodyResult.flow ->
            restoreBlockConfig outer bodyResult.config = some restored ->
              resultOK (loopRestoredResult bodyResult.flow restored)
  postRecur :
    ∀ {fuel postConfig postResult},
      postInv postConfig ->
        postResult ∈ evalStmtFuel fuel postConfig post ->
          loopRecurFlow postResult.flow ->
            headInv postResult.config
  postTerminal :
    ∀ {fuel postConfig postResult restored},
      postInv postConfig ->
        postResult ∈ evalStmtFuel fuel postConfig post ->
          loopTerminalFlow postResult.flow ->
            restoreBlockConfig outer postResult.config = some restored ->
              resultOK (loopRestoredResult postResult.flow restored)

theorem LoopSummary.postPhase_resultOK
    {outer : Config} {cond : Expr} {post body : Stmt}
    {headInv bodyInv postInv : Config -> Prop}
    {resultOK : Result -> Prop}
    (summary : LoopSummary outer cond post body
      headInv bodyInv postInv resultOK)
    {fuel : Nat} {postConfig : Config} {result : Result}
    (hLoop :
      ∀ {loopConfig : Config} {result : Result},
        headInv loopConfig ->
          result ∈ evalForFuel fuel outer loopConfig cond post body ->
            resultOK result)
    (hPostInv : postInv postConfig)
    (hMem :
      result ∈
        List.flatMap
          (fun postResult =>
            match postResult.flow with
            | FullYul.Flow.normal
            | FullYul.Flow.continued =>
                evalForFuel fuel outer postResult.config cond post body
            | FullYul.Flow.broke =>
                match restoreBlockConfig outer postResult.config with
                | some restored => [normalResult restored]
                | none => []
            | FullYul.Flow.left =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.left, config := restored }]
                | none => []
            | FullYul.Flow.halted =>
                match restoreBlockConfig outer postResult.config with
                | some restored =>
                    [{ flow := FullYul.Flow.halted, config := restored }]
                | none => [])
          (evalStmtFuel fuel postConfig post)) :
    resultOK result := by
  rcases List.mem_flatMap.mp hMem with
    ⟨postResult, hPostMem, hAfterPostMem⟩
  cases hPostFlow : postResult.flow
  · have hHeadNext :
        headInv postResult.config :=
      summary.postRecur hPostInv hPostMem
        (by simp [loopRecurFlow, hPostFlow])
    exact hLoop hHeadNext (by simpa [hPostFlow] using hAfterPostMem)
  · cases hRestore : restoreBlockConfig outer postResult.config with
    | none =>
        simp [hPostFlow, hRestore] at hAfterPostMem
    | some restored =>
        have hResult :
            result = loopRestoredResult postResult.flow restored := by
          simpa [hPostFlow, hRestore, loopRestoredResult]
            using hAfterPostMem
        rw [hResult]
        exact
          summary.postTerminal hPostInv hPostMem
            (by simp [loopTerminalFlow, hPostFlow]) hRestore
  · have hHeadNext :
        headInv postResult.config :=
      summary.postRecur hPostInv hPostMem
        (by simp [loopRecurFlow, hPostFlow])
    exact hLoop hHeadNext (by simpa [hPostFlow] using hAfterPostMem)
  · cases hRestore : restoreBlockConfig outer postResult.config with
    | none =>
        simp [hPostFlow, hRestore] at hAfterPostMem
    | some restored =>
        have hResult :
            result = loopRestoredResult postResult.flow restored := by
          simpa [hPostFlow, hRestore, loopRestoredResult]
            using hAfterPostMem
        rw [hResult]
        exact
          summary.postTerminal hPostInv hPostMem
            (by simp [loopTerminalFlow, hPostFlow]) hRestore
  · cases hRestore : restoreBlockConfig outer postResult.config with
    | none =>
        simp [hPostFlow, hRestore] at hAfterPostMem
    | some restored =>
        have hResult :
            result = loopRestoredResult postResult.flow restored := by
          simpa [hPostFlow, hRestore, loopRestoredResult]
            using hAfterPostMem
        rw [hResult]
        exact
          summary.postTerminal hPostInv hPostMem
            (by simp [loopTerminalFlow, hPostFlow]) hRestore

theorem LoopSummary.evalForFuel_resultOK
    {outer : Config} {cond : Expr} {post body : Stmt}
    {headInv bodyInv postInv : Config -> Prop}
    {resultOK : Result -> Prop}
    (summary : LoopSummary outer cond post body
      headInv bodyInv postInv resultOK)
    {fuel : Nat} {loopConfig : Config} {result : Result}
    (hHead : headInv loopConfig)
    (hMem : result ∈ evalForFuel fuel outer loopConfig cond post body) :
    resultOK result := by
  induction fuel generalizing loopConfig result with
  | zero =>
      simp [evalForFuel] at hMem
  | succ fuel ih =>
      cases hCond : evalExpr loopConfig cond with
      | none =>
          simp [evalForFuel, hCond] at hMem
      | some evaluatedCond =>
          rcases evaluatedCond with ⟨value, condConfig⟩
          have hFlat :
              result ∈
                List.flatMap
                  (fun (takeBranch, branchConfig) =>
                    if takeBranch then
                      List.flatMap
                        (fun bodyResult =>
                          match bodyResult.flow with
                          | FullYul.Flow.normal
                          | FullYul.Flow.continued =>
                              List.flatMap
                                (fun postResult =>
                                  match postResult.flow with
                                  | FullYul.Flow.normal
                                  | FullYul.Flow.continued =>
                                      evalForFuel fuel outer postResult.config
                                        cond post body
                                  | FullYul.Flow.broke =>
                                      match restoreBlockConfig outer
                                          postResult.config with
                                      | some restored => [normalResult restored]
                                      | none => []
                                  | FullYul.Flow.left =>
                                      match restoreBlockConfig outer
                                          postResult.config with
                                      | some restored =>
                                          [{ flow := FullYul.Flow.left
                                             config := restored }]
                                      | none => []
                                  | FullYul.Flow.halted =>
                                      match restoreBlockConfig outer
                                          postResult.config with
                                      | some restored =>
                                          [{ flow := FullYul.Flow.halted
                                             config := restored }]
                                      | none => [])
                                (evalStmtFuel fuel bodyResult.config post)
                          | FullYul.Flow.broke =>
                              match restoreBlockConfig outer
                                  bodyResult.config with
                              | some restored => [normalResult restored]
                              | none => []
                          | FullYul.Flow.left =>
                              match restoreBlockConfig outer
                                  bodyResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.left
                                     config := restored }]
                              | none => []
                          | FullYul.Flow.halted =>
                              match restoreBlockConfig outer
                                  bodyResult.config with
                              | some restored =>
                                  [{ flow := FullYul.Flow.halted
                                     config := restored }]
                              | none => [])
                        (evalStmtFuel fuel branchConfig body)
                    else
                      match restoreBlockConfig outer branchConfig with
                      | some restored => [normalResult restored]
                      | none => [])
                  (branchOn value condConfig) := by
            simpa [evalForFuel, hCond] using hMem
          rcases List.mem_flatMap.mp hFlat with
            ⟨branch, hBranchMem, hBranchResultMem⟩
          rcases branch with ⟨takeBranch, branchConfig⟩
          cases takeBranch
          · cases hRestore : restoreBlockConfig outer branchConfig with
            | none =>
                simp [hRestore] at hBranchResultMem
            | some restored =>
                have hResult :
                    result = normalResult restored := by
                  simpa [hRestore] using hBranchResultMem
                rw [hResult]
                exact summary.condFalse hHead hCond hBranchMem hRestore
          · have hBodyInv :
                bodyInv branchConfig :=
              summary.condTrue hHead hCond hBranchMem
            rcases List.mem_flatMap.mp hBranchResultMem with
              ⟨bodyResult, hBodyMem, hAfterBodyMem⟩
            cases hBodyFlow : bodyResult.flow
            · have hPostInv :
                  postInv bodyResult.config :=
                summary.bodyRecur hBodyInv hBodyMem
                  (by simp [loopRecurFlow, hBodyFlow])
              have hPostFlat :
                  result ∈
                    List.flatMap
                      (fun postResult =>
                        match postResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            evalForFuel fuel outer postResult.config
                              cond post body
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel bodyResult.config post) := by
                simpa [hBodyFlow] using hAfterBodyMem
              exact
                summary.postPhase_resultOK
                  (by
                    intro loopConfig result hHead hMem
                    exact ih hHead hMem)
                  hPostInv hPostFlat
            · cases hRestore : restoreBlockConfig outer bodyResult.config with
              | none =>
                  simp [hBodyFlow, hRestore] at hAfterBodyMem
              | some restored =>
                  have hResult :
                      result = loopRestoredResult bodyResult.flow restored := by
                    simpa [hBodyFlow, hRestore, loopRestoredResult]
                      using hAfterBodyMem
                  rw [hResult]
                  exact
                    summary.bodyTerminal hBodyInv hBodyMem
                      (by simp [loopTerminalFlow, hBodyFlow]) hRestore
            · have hPostInv :
                  postInv bodyResult.config :=
                summary.bodyRecur hBodyInv hBodyMem
                  (by simp [loopRecurFlow, hBodyFlow])
              have hPostFlat :
                  result ∈
                    List.flatMap
                      (fun postResult =>
                        match postResult.flow with
                        | FullYul.Flow.normal
                        | FullYul.Flow.continued =>
                            evalForFuel fuel outer postResult.config
                              cond post body
                        | FullYul.Flow.broke =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored => [normalResult restored]
                            | none => []
                        | FullYul.Flow.left =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.left
                                   config := restored }]
                            | none => []
                        | FullYul.Flow.halted =>
                            match restoreBlockConfig outer postResult.config with
                            | some restored =>
                                [{ flow := FullYul.Flow.halted
                                   config := restored }]
                            | none => [])
                      (evalStmtFuel fuel bodyResult.config post) := by
                simpa [hBodyFlow] using hAfterBodyMem
              exact
                summary.postPhase_resultOK
                  (by
                    intro loopConfig result hHead hMem
                    exact ih hHead hMem)
                  hPostInv hPostFlat
            · cases hRestore : restoreBlockConfig outer bodyResult.config with
              | none =>
                  simp [hBodyFlow, hRestore] at hAfterBodyMem
              | some restored =>
                  have hResult :
                      result = loopRestoredResult bodyResult.flow restored := by
                    simpa [hBodyFlow, hRestore, loopRestoredResult]
                      using hAfterBodyMem
                  rw [hResult]
                  exact
                    summary.bodyTerminal hBodyInv hBodyMem
                      (by simp [loopTerminalFlow, hBodyFlow]) hRestore
            · cases hRestore : restoreBlockConfig outer bodyResult.config with
              | none =>
                  simp [hBodyFlow, hRestore] at hAfterBodyMem
              | some restored =>
                  have hResult :
                      result = loopRestoredResult bodyResult.flow restored := by
                    simpa [hBodyFlow, hRestore, loopRestoredResult]
                      using hAfterBodyMem
                  rw [hResult]
                  exact
                    summary.bodyTerminal hBodyInv hBodyMem
                      (by simp [loopTerminalFlow, hBodyFlow]) hRestore

theorem evalFunctionFuel_zero
    (config : Config) (name : FullYul.Name) (args : List Value) :
    evalFunctionFuel 0 config name args = [] := by
  rfl

theorem guidedEvalStmtFuel_zero
    (model : ConcreteModel) (config : GuidedConfig) (stmt : Stmt) :
    guidedEvalStmtFuel model 0 config stmt = none := by
  rfl

theorem guidedEvalBlockFuel_zero
    (model : ConcreteModel) (config : GuidedConfig) (stmts : List Stmt) :
    guidedEvalBlockFuel model 0 config stmts = none := by
  rfl

theorem guidedEvalForFuel_zero
    (model : ConcreteModel) (outer loopConfig : GuidedConfig)
    (cond : Expr) (post body : Stmt) :
    guidedEvalForFuel model 0 outer loopConfig cond post body = none := by
  rfl

theorem guidedEvalFunctionFuel_zero
    (model : ConcreteModel) (config : GuidedConfig)
    (name : FullYul.Name) (args : List Value) :
    guidedEvalFunctionFuel model 0 config name args = none := by
  rfl

theorem branchOn_symbolic_word_forks :
    branchOn (FullYul.Value.calldataWord 0) Config.empty =
      [ (true,
          { Config.empty with
            pc := [Constraint.nonzero (FullYul.Value.calldataWord 0)] })
      , (false,
          { Config.empty with
            pc := [Constraint.iszero (FullYul.Value.calldataWord 0)] }) ] := by
  rfl

theorem evalIf_concrete_true_single_path :
    evalStmtFuel 4 { Config.empty with env := [(0, FullYul.Value.word 0)] }
        (FullYul.Stmt.ifThen (FullYul.Expr.value (FullYul.Value.word 1))
          (FullYul.Stmt.assign 0
            (FullYul.Expr.value (FullYul.Value.word 7)))) =
      [ normalResult { Config.empty with env := [(0, FullYul.Value.word 7)] } ] := by
  rfl

theorem evalIf_symbolic_condition_forks :
    evalStmtFuel 4 { Config.empty with
        env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
        (FullYul.Stmt.ifThen (FullYul.Expr.var 0)
          (FullYul.Stmt.assign 1
            (FullYul.Expr.value (FullYul.Value.word 7)))) =
      [ normalResult
          { Config.empty with
            pc := [Constraint.nonzero (FullYul.Value.calldataWord 0)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 7)] }
      , normalResult
          { Config.empty with
            pc := [Constraint.iszero (FullYul.Value.calldataWord 0)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] } ] := by
  rfl

theorem evalSwitch_concrete_default_single_path :
    evalStmtFuel 4 { Config.empty with env := [(0, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.value (FullYul.Value.word 2))
          [(FullYul.Value.word 1,
            FullYul.Stmt.assign 0
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          (some
            (FullYul.Stmt.assign 0
              (FullYul.Expr.value (FullYul.Value.word 9))))) =
      [ normalResult { Config.empty with env := [(0, FullYul.Value.word 9)] } ] := by
  rfl

theorem evalSwitch_concrete_no_default_no_match_falls_through :
    evalStmtFuel 4 { Config.empty with env := [(0, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.value (FullYul.Value.word 2))
          [(FullYul.Value.word 1,
            FullYul.Stmt.assign 0
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          none) =
      [ normalResult { Config.empty with env := [(0, FullYul.Value.word 0)] } ] := by
  rfl

theorem evalSwitch_symbolic_case_and_default_fork :
    evalStmtFuel 4 { Config.empty with
        env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.var 0)
          [(FullYul.Value.word 7,
            FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          (some
            (FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 9))))) =
      [ normalResult
          { Config.empty with
            pc := [Constraint.eq
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 7)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 7)] }
      , normalResult
          { Config.empty with
            pc := [Constraint.ne
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 7)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 9)] } ] := by
  rfl

theorem evalSwitch_symbolic_case_and_no_default_fork :
    evalStmtFuel 4 { Config.empty with
        env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.var 0)
          [(FullYul.Value.word 7,
            FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          none) =
      [ normalResult
          { Config.empty with
            pc := [Constraint.eq
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 7)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 7)] }
      , normalResult
          { Config.empty with
            pc := [Constraint.ne
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 7)]
            env :=
              [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] } ] := by
  rfl

theorem evalFunDef_then_assignCall_updates_caller :
    let fnBody :=
      FullYul.Stmt.assign 1 (FullYul.Expr.var 0)
    evalStmtFuel 7 { Config.empty with env := [(2, FullYul.Value.word 0)] }
        (FullYul.Stmt.seq
          (FullYul.Stmt.funDef 10 [0] [1] fnBody)
          (FullYul.Stmt.assignCall [2] 10
            [FullYul.Expr.value (FullYul.Value.word 7)])) =
      [ normalResult
          { Config.empty with
            env := [(2, FullYul.Value.word 7)]
            funcs :=
              [(10, { params := [0], returns := [1], body := fnBody })] } ] := by
  rfl

theorem evalAssignCall_symbolic_function_forks :
    let fnBody :=
      FullYul.Stmt.ifThen (FullYul.Expr.var 0)
        (FullYul.Stmt.assign 1
          (FullYul.Expr.value (FullYul.Value.word 7)))
    let fn : FullYul.FunctionDef :=
      { params := [0], returns := [1], body := fnBody }
    evalStmtFuel 6
        { Config.empty with
          env := [(2, FullYul.Value.word 0)]
          funcs := [(10, fn)] }
        (FullYul.Stmt.assignCall [2] 10
          [FullYul.Expr.value (FullYul.Value.calldataWord 0)]) =
      [ normalResult
          { Config.empty with
            pc := [Constraint.nonzero (FullYul.Value.calldataWord 0)]
            env := [(2, FullYul.Value.word 7)]
            funcs := [(10, fn)] }
      , normalResult
          { Config.empty with
            pc := [Constraint.iszero (FullYul.Value.calldataWord 0)]
            env := [(2, FullYul.Value.word 0)]
            funcs := [(10, fn)] } ] := by
  rfl

theorem guidedBool_calldata0_nonzero :
    guidedBool (ConcreteModel.withCalldata0 7)
        (FullYul.Value.calldataWord 0) = true := by
  rfl

theorem guidedBool_calldata0_zero :
    guidedBool (ConcreteModel.withCalldata0 0)
        (FullYul.Value.calldataWord 0) = false := by
  rfl

theorem symbolicIf_true_path_guided_by_model :
    let init : Config :=
      { Config.empty with
        env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
    let stmt : Stmt :=
      FullYul.Stmt.ifThen (FullYul.Expr.var 0)
        (FullYul.Stmt.assign 1
          (FullYul.Expr.value (FullYul.Value.word 7)))
    let path : Result :=
      normalResult
        { Config.empty with
          pc := [Constraint.nonzero (FullYul.Value.calldataWord 0)]
          env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 7)] }
    path ∈ evalStmtFuel 4 init stmt ∧
      satisfies (ConcreteModel.withCalldata0 7) path.config.pc ∧
      guidedEvalStmtFuel (ConcreteModel.withCalldata0 7) 4 (erasePC init) stmt =
        some (eraseResult path) := by
  dsimp
  constructor
  · rw [evalIf_symbolic_condition_forks]
    simp
  constructor
  · intro constraint h
    cases h with
    | head =>
        unfold holdsConstraint interpValue ConcreteModel.withCalldata0
          ConcreteModel.zero norm wordModulus
        decide
    | tail _ htail => cases htail
  · rfl

theorem symbolicIf_false_path_guided_by_model :
    let init : Config :=
      { Config.empty with
        env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
    let stmt : Stmt :=
      FullYul.Stmt.ifThen (FullYul.Expr.var 0)
        (FullYul.Stmt.assign 1
          (FullYul.Expr.value (FullYul.Value.word 7)))
    let path : Result :=
      normalResult
        { Config.empty with
          pc := [Constraint.iszero (FullYul.Value.calldataWord 0)]
          env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
    path ∈ evalStmtFuel 4 init stmt ∧
      satisfies (ConcreteModel.withCalldata0 0) path.config.pc ∧
      guidedEvalStmtFuel (ConcreteModel.withCalldata0 0) 4 (erasePC init) stmt =
        some (eraseResult path) := by
  dsimp
  constructor
  · rw [evalIf_symbolic_condition_forks]
    simp
  constructor
  · intro constraint h
    cases h with
    | head =>
        unfold holdsConstraint interpValue ConcreteModel.withCalldata0
          ConcreteModel.zero norm wordModulus
        decide
    | tail _ htail => cases htail
  · rfl

theorem guidedSwitch_symbolic_case_model :
    guidedEvalStmtFuel (ConcreteModel.withCalldata0 7) 4
        { GuidedConfig.empty with
          env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.var 0)
          [(FullYul.Value.word 7,
            FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          (some
            (FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 9))))) =
      some (guidedNormalResult
          { GuidedConfig.empty with
            env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 7)] }) := by
  rfl

theorem guidedSwitch_symbolic_default_model :
    guidedEvalStmtFuel (ConcreteModel.withCalldata0 8) 4
        { GuidedConfig.empty with
          env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 0)] }
        (FullYul.Stmt.switch (FullYul.Expr.var 0)
          [(FullYul.Value.word 7,
            FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 7)))]
          (some
            (FullYul.Stmt.assign 1
              (FullYul.Expr.value (FullYul.Value.word 9))))) =
      some (guidedNormalResult
          { GuidedConfig.empty with
            env := [(0, FullYul.Value.calldataWord 0), (1, FullYul.Value.word 9)] }) := by
  rfl

theorem evalStmt_builtin_mstore_updates_symbolic_evm :
    evalStmtFuel 3 Config.empty
        (FullYul.Stmt.expr
          (FullYul.Expr.builtin Evm.Builtin.mstore
            [ FullYul.Expr.value (FullYul.Value.word 0)
            , FullYul.Expr.value (FullYul.Value.dataOffset 1) ])) =
      [normalResult
        { Config.empty with
          evm :=
            { FullYul.EvmState.empty with
              memoryVersion := 1
              msize := 32
              memoryWords := [(0, FullYul.Value.dataOffset 1)] } }] := by
  rfl

theorem guidedStmt_builtin_mstore_updates_symbolic_evm :
    guidedEvalStmtFuel ConcreteModel.zero 3 (erasePC Config.empty)
        (FullYul.Stmt.expr
          (FullYul.Expr.builtin Evm.Builtin.mstore
            [ FullYul.Expr.value (FullYul.Value.word 0)
            , FullYul.Expr.value (FullYul.Value.dataOffset 1) ])) =
      some (guidedNormalResult
        { GuidedConfig.empty with
          evm :=
            { FullYul.EvmState.empty with
              memoryVersion := 1
              msize := 32
              memoryWords := [(0, FullYul.Value.dataOffset 1)] } }) := by
  rfl

theorem evalStmt_builtin_return_halts_and_stops_sequence :
    evalStmtFuel 4 Config.empty
        (FullYul.Stmt.seq
          (FullYul.Stmt.expr
            (FullYul.Expr.builtin Evm.Builtin.returnOp
              [ FullYul.Expr.value (FullYul.Value.word 0)
              , FullYul.Expr.value (FullYul.Value.word 0) ]))
          (FullYul.Stmt.expr
            (FullYul.Expr.builtin Evm.Builtin.sstore
              [ FullYul.Expr.value (FullYul.Value.word 0)
              , FullYul.Expr.value (FullYul.Value.word 7) ]))) =
      [ { flow := FullYul.Flow.halted
          config :=
            { Config.empty with
              evm :=
                { FullYul.EvmState.empty with
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := FullYul.SymbolicBytes.memorySnapshot 0 0 0 } } } } ] := by
  rfl

theorem guidedStmt_builtin_return_halts_and_stops_sequence :
    guidedEvalStmtFuel ConcreteModel.zero 4 (erasePC Config.empty)
        (FullYul.Stmt.seq
          (FullYul.Stmt.expr
            (FullYul.Expr.builtin Evm.Builtin.returnOp
              [ FullYul.Expr.value (FullYul.Value.word 0)
              , FullYul.Expr.value (FullYul.Value.word 0) ]))
          (FullYul.Stmt.expr
            (FullYul.Expr.builtin Evm.Builtin.sstore
              [ FullYul.Expr.value (FullYul.Value.word 0)
              , FullYul.Expr.value (FullYul.Value.word 7) ]))) =
      some
        { flow := FullYul.Flow.halted
          config :=
            { GuidedConfig.empty with
              evm :=
                { FullYul.EvmState.empty with
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := FullYul.SymbolicBytes.memorySnapshot 0 0 0 } } } } := by
  rfl

theorem evalStmt_builtin_call_records_symbolic_event :
    evalStmtFuel 3 Config.empty
        (FullYul.Stmt.expr
          (FullYul.Expr.builtin Evm.Builtin.callOp
            [ FullYul.Expr.value (FullYul.Value.word 0)
            , FullYul.Expr.value (FullYul.Value.word 1)
            , FullYul.Expr.value (FullYul.Value.word 2)
            , FullYul.Expr.value (FullYul.Value.word 3)
            , FullYul.Expr.value (FullYul.Value.word 4)
            , FullYul.Expr.value (FullYul.Value.word 5)
            , FullYul.Expr.value (FullYul.Value.word 6) ])) =
      [normalResult
        { Config.empty with
          evm :=
            { FullYul.EvmState.empty with
              memoryBytes :=
                FullYul.ObjectMemory.write FullYul.ObjectMemory.empty 5
                  (FullYul.SymbolicBytes.returndataSnapshot 1 0 6)
              memoryVersion := 1
              returndata := FullYul.SymbolicBytes.callReturnData 1
              returndataVersion := 1
              msize := 32
              externalActions := [Evm.Builtin.callOp]
              externalEvents :=
                [ { id := 1
                    op := Evm.Builtin.callOp
                    args :=
                      [ FullYul.Value.word 0, FullYul.Value.word 1
                      , FullYul.Value.word 2, FullYul.Value.word 3
                      , FullYul.Value.word 4, FullYul.Value.word 5
                      , FullYul.Value.word 6 ]
                    result := FullYul.Value.callSuccess 1
                    returndata := FullYul.SymbolicBytes.callReturnData 1 } ]
              nextExternalId := 2 } }] := by
  rfl

theorem evalStmt_multi_output_verbatim_letMany :
    evalStmtFuel 4 Config.empty
        (FullYul.Stmt.letMany [0, 1]
          (some
            [FullYul.Expr.builtin (Evm.Builtin.verbatimOp 1 2)
              [FullYul.Expr.value (FullYul.Value.word 7)]])) =
      [normalResult
        { Config.empty with
          env :=
            [ (1, FullYul.Value.callSuccess 2)
            , (0, FullYul.Value.callSuccess 1) ]
          evm :=
            { FullYul.EvmState.empty with
              externalActions := [Evm.Builtin.verbatimOp 1 2]
              externalEvents :=
                [ { id := 1
                    op := Evm.Builtin.verbatimOp 1 2
                    args := [FullYul.Value.word 7]
                    result := FullYul.Value.callSuccess 1
                    returndata := FullYul.SymbolicBytes.empty },
                  { id := 2
                    op := Evm.Builtin.verbatimOp 1 2
                    args := [FullYul.Value.word 7]
                    result := FullYul.Value.callSuccess 2
                    returndata := FullYul.SymbolicBytes.empty } ]
              nextExternalId := 3 } }] := by
  rfl

theorem guidedStmt_multi_output_verbatim_letMany :
    guidedEvalStmtFuel ConcreteModel.zero 4 GuidedConfig.empty
        (FullYul.Stmt.letMany [0, 1]
          (some
            [FullYul.Expr.builtin (Evm.Builtin.verbatimOp 1 2)
              [FullYul.Expr.value (FullYul.Value.word 7)]])) =
      some
        (guidedNormalResult
          { GuidedConfig.empty with
            env :=
              [ (1, FullYul.Value.callSuccess 2)
              , (0, FullYul.Value.callSuccess 1) ]
            evm :=
              { FullYul.EvmState.empty with
                externalActions := [Evm.Builtin.verbatimOp 1 2]
                externalEvents :=
                  [ { id := 1
                      op := Evm.Builtin.verbatimOp 1 2
                      args := [FullYul.Value.word 7]
                      result := FullYul.Value.callSuccess 1
                      returndata := FullYul.SymbolicBytes.empty },
                    { id := 2
                      op := Evm.Builtin.verbatimOp 1 2
                      args := [FullYul.Value.word 7]
                      result := FullYul.Value.callSuccess 2
                      returndata := FullYul.SymbolicBytes.empty } ]
                nextExternalId := 3 } }) := by
  rfl

theorem evalIf_symbolic_eq_builtin_forks :
    evalStmtFuel 4 { Config.empty with env := [(0, FullYul.Value.word 0)] }
      (FullYul.Stmt.ifThen
        (FullYul.Expr.builtin Evm.Builtin.eqOp
          [ FullYul.Expr.value (FullYul.Value.calldataWord 0)
          , FullYul.Expr.value (FullYul.Value.word 0) ])
        (FullYul.Stmt.assign 0
          (FullYul.Expr.value (FullYul.Value.word 7)))) =
    [ normalResult
        { Config.empty with
          pc := [Constraint.nonzero
            (FullYul.Value.binaryBuiltin Evm.Builtin.eqOp
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 0))]
          env := [(0, FullYul.Value.word 7)] }
    , normalResult
        { Config.empty with
          pc := [Constraint.iszero
            (FullYul.Value.binaryBuiltin Evm.Builtin.eqOp
              (FullYul.Value.calldataWord 0) (FullYul.Value.word 0))]
          env := [(0, FullYul.Value.word 0)] } ] := by
  rfl

end SymYul
end SolidCoreYulCore
