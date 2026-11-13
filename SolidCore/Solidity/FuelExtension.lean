import SolidCore.Solidity.Checked

/-!
# Fuel extension for the source interpreter, along every path

`FuelMonotonicity.lean` proves that a call tree with no reachable `outOfFuel` leaf is the tree
at every higher fuel. That needs the whole tree, for every answer at every request, to be free of
`outOfFuel`, which a successful fold under one responder does not give: the fold follows one path.

This module proves the unconditional, per-path form. `SolI.Ext lo hi` says `hi` is `lo` with some
of its `outOfFuel` leaves replaced by arbitrary trees, and every evaluator of the statement cluster
at fuel `n` is `Ext`-below itself at any fuel `m ≥ n` (`Stmt.eval_fuel_ext` and its siblings). A
fold that ends anywhere but `outOfFuel` ends the same way on an extension (`SolI.Ext.runWith`), so
`FunctionDef.call?` (`FunctionDef.call?_fuel_mono`) and the checked contract's call and
construction are fuel-monotone: a result a fuel gives is the result every higher fuel gives.
Running out of fuel therefore never produces a result of its own; it only withholds one.

The induction is `FuelMonotonicity.lean`'s, arm for arm, with `SolI.Ext.bind` in place of
`SolI.bind_fuel_congr`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace SolidCore
namespace Solidity
namespace Source

open EvmCompiler.Simulation (Interaction Answer Query)

/-- `hi` is `lo` with some of its `outOfFuel` leaves replaced. -/
inductive SolI.Ext {α : Type} : SolI α → SolI α → Prop
  | stop (hi : SolI α) : SolI.Ext (.done (.error .outOfFuel)) hi
  | done (r : Except SolidityFailure α) : SolI.Ext (.done r) (.done r)
  | request {q : Query} {k k' : Answer q → SolI α} :
      (∀ a, SolI.Ext (k a) (k' a)) → SolI.Ext (.request q k) (.request q k')

theorem SolI.Ext.refl {α : Type} : ∀ (t : SolI α), SolI.Ext t t
  | .done r => .done r
  | .request _ k => .request fun a => SolI.Ext.refl (k a)

theorem SolI.Ext.bind {α β : Type} {t t' : SolI α} {k k' : α → SolI β}
    (h : SolI.Ext t t') (hk : ∀ v, SolI.Ext (k v) (k' v)) :
    SolI.Ext (t >>= k) (t' >>= k') := by
  induction h with
  | stop hi => exact .stop _
  | done r =>
    cases r with
    | ok v => exact hk v
    | error e => exact .done _
  | request _ ih => exact .request fun a => ih a

theorem SolI.Ext.bind_refl {α β : Type} {t t' : SolI α} {k : α → SolI β}
    (h : SolI.Ext t t') : SolI.Ext (t >>= k) (t' >>= k) :=
  h.bind fun v => SolI.Ext.refl (k v)

theorem SolI.Ext.map {α β : Type} {t t' : SolI α} {f : α → β}
    (h : SolI.Ext t t') : SolI.Ext (f <$> t) (f <$> t') :=
  h.bind fun v => SolI.Ext.refl _

/-- Close an `Ext` goal from an `Ext` fact about its prefix. -/
macro "ext_close " h:term : tactic =>
  `(tactic| first
    | exact $h
    | exact SolI.Ext.bind_refl $h
    | exact SolI.Ext.map $h)

/-- `Stmt.evalList` is fuel-monotone at any pair of fuels at which `Stmt.eval`
    is (the list evaluator passes its fuel through unchanged). -/
private theorem evalList_ext_of (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt)) :
    ∀ (table : FunctionTable) (context : Context) (stmts : List Stmt)
      (runtime : Runtime),
      SolI.Ext (Stmt.evalList n table context runtime stmts) (Stmt.evalList m table context runtime stmts) := by
  intro table context stmts
  induction stmts with
  | nil => intro runtime; simp only [Stmt.evalList]; exact SolI.Ext.refl _
  | cons s rest ihRest =>
    intro runtime
    simp only [Stmt.evalList]
    refine SolI.Ext.bind (hEval _ _ _ _) ?_
    intro v
    cases v with
    | normal runtime' => exact ihRest runtime'
    | returned runtime' values => exact SolI.Ext.refl _
    | selfdestructed runtime' => exact SolI.Ext.refl _
    | reverted runtime' err => exact SolI.Ext.refl _
    | broke runtime' => exact SolI.Ext.refl _
    | continued runtime' => exact SolI.Ext.refl _

private theorem evalWhile_ext_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt))
    (hWhile : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.Ext (Stmt.evalWhile n table context runtime cond body) (Stmt.evalWhile m table context runtime cond body)) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.Ext (Stmt.evalWhile (n + 1) table context runtime cond body) (Stmt.evalWhile (m + 1) table context runtime cond body) := by
  intro table context runtime cond body
  simp only [Stmt.evalWhile]
  refine SolI.Ext.bind (SolI.Ext.refl _) ?_
  intro v
  cases v with
  | error err => exact SolI.Ext.refl _
  | ok p =>
    obtain ⟨value, runtime'⟩ := p
    try simp only []
    cases hw : value.expectWord with
    | error err => exact SolI.Ext.refl _
    | ok word =>
      try simp only []
      cases ht : wordTruthy word with
      | false => exact SolI.Ext.refl _
      | true =>
        refine SolI.Ext.bind (hEval _ _ _ _) ?_
        intro w
        cases w with
        | normal r2 => exact hWhile _ _ _ _ _
        | continued r2 => exact hWhile _ _ _ _ _
        | returned r2 vs => exact SolI.Ext.refl _
        | selfdestructed r2 => exact SolI.Ext.refl _
        | reverted r2 e => exact SolI.Ext.refl _
        | broke r2 => exact SolI.Ext.refl _

private theorem evalDoWhile_ext_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt))
    (hDoWhile : ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.Ext (Stmt.evalDoWhile n table context runtime body cond) (Stmt.evalDoWhile m table context runtime body cond)) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (body : Stmt) (cond : Expr),
      SolI.Ext (Stmt.evalDoWhile (n + 1) table context runtime body cond) (Stmt.evalDoWhile (m + 1) table context runtime body cond) := by
  intro table context runtime body cond
  simp only [Stmt.evalDoWhile]
  refine SolI.Ext.bind (hEval _ _ _ _) ?_
  intro v
  cases v with
  | returned r' vs => exact SolI.Ext.refl _
  | selfdestructed r' => exact SolI.Ext.refl _
  | reverted r' e => exact SolI.Ext.refl _
  | broke r' => exact SolI.Ext.refl _
  | normal runtime' =>
    try simp only []
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro w
    cases w with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨value, runtime''⟩ := p
      try simp only [Bool.false_eq_true, if_true, if_false]
      cases hword : value.expectWord with
      | error e => exact SolI.Ext.refl _
      | ok word =>
        try simp only [Bool.false_eq_true, if_true, if_false]
        cases ht : wordTruthy word with
        | false => exact SolI.Ext.refl _
        | true =>
          exact hDoWhile _ _ _ _ _
  | continued runtime' =>
    try simp only []
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro w
    cases w with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨value, runtime''⟩ := p
      try simp only [Bool.false_eq_true, if_true, if_false]
      cases hword : value.expectWord with
      | error e => exact SolI.Ext.refl _
      | ok word =>
        try simp only [Bool.false_eq_true, if_true, if_false]
        cases ht : wordTruthy word with
        | false => exact SolI.Ext.refl _
        | true =>
          exact hDoWhile _ _ _ _ _

private theorem evalFor_ext_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt))
    (hFor : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.Ext (Stmt.evalFor n table context runtime cond post body) (Stmt.evalFor m table context runtime cond post body)) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.Ext (Stmt.evalFor (n + 1) table context runtime cond post body) (Stmt.evalFor (m + 1) table context runtime cond post body) := by
  intro table context runtime cond post body
  simp only [Stmt.evalFor]
  refine SolI.Ext.bind (SolI.Ext.refl _) ?_
  intro v
  cases v with
  | error err => exact SolI.Ext.refl _
  | ok p =>
    obtain ⟨value, runtime'⟩ := p
    try simp only []
    cases hw : value.expectWord with
    | error err => exact SolI.Ext.refl _
    | ok word =>
      try simp only []
      cases ht : wordTruthy word with
      | false => exact SolI.Ext.refl _
      | true =>
        refine SolI.Ext.bind (hEval _ _ _ _) ?_
        intro w
        cases w with
        | returned r2 vs => exact SolI.Ext.refl _
        | selfdestructed r2 => exact SolI.Ext.refl _
        | reverted r2 e => exact SolI.Ext.refl _
        | broke r2 => exact SolI.Ext.refl _
        | normal r2 =>
          try simp only []
          refine SolI.Ext.bind (hEval _ _ _ _) ?_
          intro u
          cases u with
          | normal posted => exact hFor _ _ _ _ _ _
          | returned r3 vs => exact SolI.Ext.refl _
          | selfdestructed r3 => exact SolI.Ext.refl _
          | reverted r3 e => exact SolI.Ext.refl _
          | broke r3 => exact SolI.Ext.refl _
          | continued r3 => exact SolI.Ext.refl _
        | continued r2 =>
          try simp only []
          refine SolI.Ext.bind (hEval _ _ _ _) ?_
          intro u
          cases u with
          | normal posted => exact hFor _ _ _ _ _ _
          | returned r3 vs => exact SolI.Ext.refl _
          | selfdestructed r3 => exact SolI.Ext.refl _
          | reverted r3 e => exact SolI.Ext.refl _
          | broke r3 => exact SolI.Ext.refl _
          | continued r3 => exact SolI.Ext.refl _

set_option maxHeartbeats 1600000 in
/-- One fuel layer of `Stmt.eval`, given monotonicity of the whole cluster at
    the previous fuel. One `case` per fuel-dependent statement arm; every
    fuel-free arm is discharged by the unfolding `simp` itself. -/
private theorem eval_ext_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt))
    (hList : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmts : List Stmt),
      SolI.Ext (Stmt.evalList n table context runtime stmts) (Stmt.evalList m table context runtime stmts))
    (hWhile : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.Ext (Stmt.evalWhile n table context runtime cond body) (Stmt.evalWhile m table context runtime cond body))
    (hDoWhile : ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.Ext (Stmt.evalDoWhile n table context runtime body cond) (Stmt.evalDoWhile m table context runtime body cond))
    (hFor : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.Ext (Stmt.evalFor n table context runtime cond post body) (Stmt.evalFor m table context runtime cond post body)) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.Ext (Stmt.eval (n + 1) table context runtime stmt) (Stmt.eval (m + 1) table context runtime stmt) := by
  intro table context runtime stmt
  cases stmt <;> simp only [Stmt.eval] <;> try exact SolI.Ext.refl _
  case block body =>
    ext_close (hList _ _ _ _)
  case captureReturn returnNames body =>
    ext_close (hEval _ _ _ _)
  case internalCall targets callee args =>
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro v
    cases v with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨argValues, runtime'⟩ := p
      try simp only []
      cases hlk : table.lookup? callee with
      | none => exact SolI.Ext.refl _
      | some fn =>
        try simp only []
        cases hen : internalCallEnter? fn argValues runtime' with
        | none => exact SolI.Ext.refl _
        | some pr =>
          obtain ⟨calleeRuntime, savedLocals⟩ := pr
          try simp only []
          ext_close (hEval _ _ _ _)
  case internalCallPtr targets fnExpr args =>
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro v
    cases v with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨value, runtimeFn⟩ := p
      cases value <;> try exact SolI.Ext.refl _
      case internalFunction id =>
        try simp only []
        refine SolI.Ext.bind (SolI.Ext.refl _) ?_
        intro w
        cases w with
        | error err => exact SolI.Ext.refl _
        | ok q =>
          obtain ⟨argValues, runtime'⟩ := q
          try simp only [Bool.false_eq_true, if_true, if_false]
          cases hlk : table.lookupById? id with
          | none => exact SolI.Ext.refl _
          | some fn =>
            try simp only [Bool.false_eq_true, if_true, if_false]
            cases hen : internalCallEnter? fn argValues runtime' with
            | none => exact SolI.Ext.refl _
            | some pr =>
              obtain ⟨calleeRuntime, savedLocals⟩ := pr
              try simp only [Bool.false_eq_true, if_true, if_false]
              ext_close (hEval _ _ _ _)
  case ifElse cond thenBranch elseBranch =>
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro v
    cases v with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨value, runtime'⟩ := p
      try simp only []
      cases hw : value.expectWord with
      | error err => exact SolI.Ext.refl _
      | ok word =>
        try simp only []
        cases ht : wordTruthy word with
        | false =>
            exact hEval _ _ _ _
        | true =>
            exact hEval _ _ _ _
  case «switch» discr cs defaultBranch =>
    refine SolI.Ext.bind (SolI.Ext.refl _) ?_
    intro v
    cases v with
    | error err => exact SolI.Ext.refl _
    | ok p =>
      obtain ⟨value, runtime'⟩ := p
      try simp only []
      cases hw : value.expectWord with
      | error err => exact SolI.Ext.refl _
      | ok word =>
        try simp only []
        cases hb : Stmt.findSwitchBranch? word cs with
        | some branch =>
            cases defaultBranch with
            | some d => exact hEval _ _ _ _
            | none => exact hEval _ _ _ _
        | none =>
            cases defaultBranch with
            | some branch => exact hEval _ _ _ _
            | none => exact SolI.Ext.refl _
  case whileLoop cond body =>
    exact hWhile _ _ _ _ _
  case doWhile body cond =>
    exact hDoWhile _ _ _ _ _
  case forLoop init cond post body =>
    refine SolI.Ext.bind (hEval _ _ _ _) ?_
    intro v
    cases v with
    | returned r' vs => exact SolI.Ext.refl _
    | selfdestructed r' => exact SolI.Ext.refl _
    | reverted r' e => exact SolI.Ext.refl _
    | broke r' => exact SolI.Ext.refl _
    | continued r' => exact SolI.Ext.refl _
    | normal initialized =>
      try simp only []
      ext_close (hFor _ _ _ _ _ _)
  case tryExternalCall kind targetExpr calldataExpr valueExpr gasExprOpt
      gasFirst checkTargetCode rets retCleanups successBody catchClauses =>
    cases h1 : targetExpr.evalWithRuntimeByContext context runtime with
    | error err => exact SolI.Ext.refl _
    | ok p1 =>
      obtain ⟨targetValue, runtime'⟩ := p1
      try simp only []
      cases h2 : targetValue.expectWord with
      | error err => exact SolI.Ext.refl _
      | ok target =>
        try simp only []
        -- New eval order (gap EO1): the call options (value/gas ordered by
        -- `gasFirst`) are evaluated BEFORE the calldata argument. Split the
        -- options result FIRST, thread its runtime (`runtimeOpts`) into the
        -- calldata evaluation, then the calldata, `asBytes?`, and finally the
        -- missingCode `if` + the two bind branches.
        split
        next value gasOpt runtimeOpts heq =>
          try simp only []
          cases h3 : calldataExpr.evalWithRuntimeByContext context runtimeOpts with
          | error err => exact SolI.Ext.refl _
          | ok p2 =>
            obtain ⟨calldataValue, runtime'''⟩ := p2
            try simp only []
            cases h4 : calldataValue.asBytes? with
            | none => exact SolI.Ext.refl _
            | some calldata =>
              try simp only []
              -- gap A1/A3: the `extcodesize` existence guard now reverts the
              -- caller UNCATCHABLY *before* the CALL.  Split it: the missing-code
              -- branch is a fuel-free `Result.reverted` (closed by `simp` as a
              -- reflexivity goal), so only the has-code branch — which performs
              -- the CALL — carries the fuel-dependent continuation.
              split <;> (try exact SolI.Ext.refl _)
              refine SolI.Ext.bind (SolI.Ext.refl _) ?_
              intro w
              obtain ⟨callResult, adoptedState⟩ := w
              try simp only [Bool.false_eq_true, if_true, if_false]
              cases hs : callResult.success with
              | false =>
                try simp only [Bool.false_eq_true, if_true, if_false]
                cases hcm : TryCatchClause.findMatch?
                    (callResult.output.map normByte) catchClauses with
                | none => exact SolI.Ext.refl _
                | some fb =>
                  obtain ⟨frame, body⟩ := fb
                  try simp only [Bool.false_eq_true, if_true, if_false]
                  ext_close (hEval _ _ _ _)
              | true =>
                try simp only [Bool.false_eq_true, if_true, if_false]
                -- TC-OOM1: the success-return decode now uses the Except view so
                -- an oversized dynamic length propagates Panic(0x41) uncaught.
                -- `Except.error` (empty OR 0x41) is a fuel-free `Result.reverted`;
                -- only `Except.ok` carries the fuel-dependent success body.
                cases habi : abiDecodeValuesExcept? (rets.map BindingDecl.ty)
                    (callResult.output.map normByte) with
                | error revertData => exact SolI.Ext.refl _
                | ok decoded =>
                  try simp only [Bool.false_eq_true, if_true, if_false]
                  cases hacc : AbiCleanups.acceptOrUnspecified
                      retCleanups decoded with
                  | false => exact SolI.Ext.refl _
                  | true =>
                    try simp only [Bool.false_eq_true, if_true, if_false]
                    cases hbind : BindingDecl.bindArgs? rets decoded with
                    | none => exact SolI.Ext.refl _
                    | some frame =>
                      try simp only [Bool.false_eq_true, if_true, if_false]
                      ext_close (hEval _ _ _ _)
        next runtimeFailed err heq => exact SolI.Ext.refl _
  case tryContractCreate contractName ctorArgsExpr valueExpr saltExprOpt
      valueBeforeSalt rets successBody catchClauses =>
    -- New eval order (gap DIV-CREATE-1/2): the creation options (value/salt
    -- ordered by `valueBeforeSalt`) are evaluated BEFORE the constructor args.
    -- Split the options result FIRST, thread its runtime (`runtimeOpts`) into
    -- the args evaluation, then `asBytes?`, and finally the two bind branches.
    split
    next value saltOpt runtimeOpts heq =>
      try simp only []
      cases h1 : ctorArgsExpr.evalWithRuntimeByContext context runtimeOpts with
      | error err => exact SolI.Ext.refl _
      | ok p1 =>
        obtain ⟨argsValue, runtime'''⟩ := p1
        try simp only []
        cases h2 : argsValue.asBytes? with
        | none => exact SolI.Ext.refl _
        | some constructorArgs =>
          try simp only []
          refine SolI.Ext.bind (SolI.Ext.refl _) ?_
          intro w
          obtain ⟨createResult, adoptedState⟩ := w
          try simp only [Bool.false_eq_true, if_true, if_false]
          cases hs : createResult.success with
          | false =>
            try simp only [Bool.false_eq_true, if_true, if_false]
            cases hcm : TryCatchClause.findMatch?
                (createResult.output.map normByte) catchClauses with
            | none => exact SolI.Ext.refl _
            | some fb =>
              obtain ⟨frame, body⟩ := fb
              try simp only [Bool.false_eq_true, if_true, if_false]
              ext_close (hEval _ _ _ _)
          | true =>
            simp only [Bool.false_eq_true, if_true, if_false]
            cases hB : BindingDecl.bindArgs? rets
                (if rets.isEmpty then [] else [Value.word createResult.address]) with
            | none => exact SolI.Ext.refl _
            | some frame =>
              simp only []
              ext_close (hEval _ _ _ _)
    next runtimeErr err heq => exact SolI.Ext.refl _
  case checked body =>
    exact hEval _ _ _ _
  case unchecked body =>
    exact hEval _ _ _ _

/-! ### The mutual induction -/

private theorem fuelExtAll (n : Nat) :
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (stmt : Stmt),
      SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt)) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (stmts : List Stmt),
      SolI.Ext (Stmt.evalList n table context runtime stmts)
        (Stmt.evalList m table context runtime stmts)) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (cond : Expr) (body : Stmt),
      SolI.Ext (Stmt.evalWhile n table context runtime cond body)
        (Stmt.evalWhile m table context runtime cond body)) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.Ext (Stmt.evalDoWhile n table context runtime body cond)
        (Stmt.evalDoWhile m table context runtime body cond)) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.Ext (Stmt.evalFor n table context runtime cond post body)
        (Stmt.evalFor m table context runtime cond post body)) := by
  induction n with
  | zero =>
    have hEval0 : ∀ m, 0 ≤ m → ∀ (table : FunctionTable) (context : Context)
        (runtime : Runtime) (stmt : Stmt),
        SolI.Ext (Stmt.eval 0 table context runtime stmt) (Stmt.eval m table context runtime stmt) := by
      intro m _ table context runtime stmt
      simp only [Stmt.eval]
      exact .stop _
    refine ⟨hEval0, ?_, ?_, ?_, ?_⟩
    · intro m hm table context runtime stmts
      exact evalList_ext_of 0 m
        (fun tb c r s => hEval0 m hm tb c r s)
        table context stmts runtime
    · intro m hm table context runtime cond body
      simp only [Stmt.evalWhile]
      exact .stop _
    · intro m hm table context runtime body cond
      simp only [Stmt.evalDoWhile]
      exact .stop _
    · intro m hm table context runtime cond post body
      simp only [Stmt.evalFor]
      exact .stop _
  | succ n ihn =>
    obtain ⟨ihEval, ihList, ihWhile, ihDoWhile, ihFor⟩ := ihn
    have hEvalS : ∀ m, n + 1 ≤ m → ∀ (table : FunctionTable)
        (context : Context) (runtime : Runtime) (stmt : Stmt),
        SolI.Ext (Stmt.eval (n + 1) table context runtime stmt)
          (Stmt.eval m table context runtime stmt) := by
      intro m hm table context runtime stmt
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact eval_ext_step n m'
          (fun tb c r s => ihEval m' hm' tb c r s)
          (fun tb c r ss => ihList m' hm' tb c r ss)
          (fun tb c r cd bd => ihWhile m' hm' tb c r cd bd)
          (fun tb c r bd cd => ihDoWhile m' hm' tb c r bd cd)
          (fun tb c r cd ps bd => ihFor m' hm' tb c r cd ps bd)
          table context runtime stmt
    refine ⟨hEvalS, ?_, ?_, ?_, ?_⟩
    · intro m hm table context runtime stmts
      exact evalList_ext_of (n + 1) m
        (fun tb c r s => hEvalS m hm tb c r s)
        table context stmts runtime
    · intro m hm table context runtime cond body
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalWhile_ext_step n m'
          (fun tb c r s => ihEval m' hm' tb c r s)
          (fun tb c r cd bd => ihWhile m' hm' tb c r cd bd)
          table context runtime cond body
    · intro m hm table context runtime body cond
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalDoWhile_ext_step n m'
          (fun tb c r s => ihEval m' hm' tb c r s)
          (fun tb c r bd cd => ihDoWhile m' hm' tb c r bd cd)
          table context runtime body cond
    · intro m hm table context runtime cond post body
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalFor_ext_step n m'
          (fun tb c r s => ihEval m' hm' tb c r s)
          (fun tb c r cd ps bd => ihFor m' hm' tb c r cd ps bd)
          table context runtime cond post body

/-- **Fuel extension, statements.** -/
theorem Stmt.eval_fuel_ext {n m : Nat} (hnm : n ≤ m) (table : FunctionTable) (context : Context)
    (runtime : Runtime) (stmt : Stmt) :
    SolI.Ext (Stmt.eval n table context runtime stmt) (Stmt.eval m table context runtime stmt) :=
  (fuelExtAll n).1 m hnm table context runtime stmt


/-! ### Folding an extension -/

/-- A fold that does not end in `outOfFuel` ends the same way on every extension. -/
theorem SolI.Ext.runWith {α : Type} {responder : ScriptedResponder} {t t' : SolI α}
    (h : SolI.Ext t t') {r : Except ResponderFailure α} (hrun : SolI.runWith responder t = r)
    (hr : r ≠ .error (.solidity .outOfFuel)) : SolI.runWith responder t' = r := by
  induction h generalizing r with
  | stop hi =>
    simp only [SolI.runWith] at hrun
    exact absurd hrun.symm hr
  | done r' => exact hrun
  | request hk ih =>
    rename_i q k k'
    cases q with
    | resource res =>
      simp only [SolI.runWith] at hrun ⊢
      exact ih _ hrun hr
    | external world req =>
      cases req with
      | call request =>
        simp only [SolI.runWith] at hrun ⊢
        cases ha : responder.answerCall? world request <;> simp only [ha] at hrun ⊢
        · cases hp : precompileAnswerCall? world request <;> simp only [hp] at hrun ⊢
          · exact hrun
          · exact ih _ hrun hr
        · exact ih _ hrun hr
      | create request =>
        simp only [SolI.runWith] at hrun ⊢
        cases ha : responder.answerCreate? world request <;> simp only [ha] at hrun ⊢
        · exact hrun
        · exact ih _ hrun hr

/-- An ok fold is the fold of every extension. -/
theorem SolI.Ext.runWith_ok {α : Type} {responder : ScriptedResponder} {t t' : SolI α}
    (h : SolI.Ext t t') {a : α} (hrun : SolI.runWith responder t = .ok a) :
    SolI.runWith responder t' = .ok a :=
  h.runWith hrun (by simp)


/-! ### The public seams -/

theorem FunctionDef.evalBodyEntry_fuel_ext {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {tree : SolI Result}
    (h : FunctionDef.evalBodyEntry n table context function state args = some tree) :
    ∃ tree', FunctionDef.evalBodyEntry m table context function state args = some tree' ∧
      SolI.Ext tree tree' := by
  simp only [FunctionDef.evalBodyEntry] at h ⊢
  cases hacc : function.acceptsValue context.value with
  | false =>
    simp only [hacc, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    exact ⟨tree, h, SolI.Ext.refl _⟩
  | true =>
    simp only [hacc, ite_true] at h ⊢
    cases hframe : function.initialFrame? args with
    | none =>
      rw [hframe] at h
      simp at h
    | some frame =>
      simp only [hframe] at h ⊢
      injection h with h
      subst h
      exact ⟨_, rfl, by ext_close (Stmt.eval_fuel_ext hnm _ _ _ _)⟩

theorem FunctionDef.call_fuel_ext {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {tree : SolI CallResult}
    (h : FunctionDef.call n table context function state args = some tree) :
    ∃ tree', FunctionDef.call m table context function state args = some tree' ∧
      SolI.Ext tree tree' := by
  unfold FunctionDef.call at h ⊢
  cases hentry : FunctionDef.evalBodyEntry n table context function state args with
  | none =>
    rw [hentry] at h
    simp at h
  | some t0 =>
    rw [hentry] at h
    obtain ⟨t1, h1, hx⟩ := FunctionDef.evalBodyEntry_fuel_ext hnm hentry
    rw [h1]
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hx.map⟩

/-- **A finished call is the call at every higher fuel.** -/
theorem FunctionDef.call?_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {r : CallResult}
    (h : FunctionDef.call? n table context function state args = some r) :
    FunctionDef.call? m table context function state args = some r := by
  unfold FunctionDef.call? at h ⊢
  cases hc : FunctionDef.call n table context function state args with
  | none =>
    rw [hc] at h
    simp at h
  | some t =>
    rw [hc] at h
    obtain ⟨t', hc', hx⟩ := FunctionDef.call_fuel_ext hnm hc
    rw [hc']
    simp only [Option.bind_some] at h ⊢
    cases hrun : SolI.runWith [] t with
    | error e =>
      rw [hrun] at h
      simp at h
    | ok a =>
      rw [hrun] at h
      rw [hx.runWith_ok hrun]
      exact h


namespace ABI

theorem Contract.callFallbackAtFromWithContext?_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : Contract} {base : Context} {state : State} {self sender value : Word}
    {calldata : Bytes} {r : AbiCallResult}
    (h : Contract.callFallbackAtFromWithContext? n contract base state self sender value calldata
      = some r) :
    Contract.callFallbackAtFromWithContext? m contract base state self sender value calldata
      = some r := by
  unfold Contract.callFallbackAtFromWithContext? at h ⊢
  split at h
  next function hf =>
    try simp only [hf]
    cases hargs : FunctionDef.fallbackArgs? function calldata <;>
      simp only [hargs, Option.bind_some, Option.bind_none, Option.bind_eq_bind] at h ⊢
    · cases h
    · split at h
      next hacc =>
        try simp only [hacc, ite_true]
        try dsimp only at h ⊢
        split at h
        next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
        next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
        next => cases h
      next hacc =>
        try simp only [hacc]
        exact h
  next hf =>
    try simp only [hf]
    exact h


theorem Contract.callReceiveOrFallbackAtFromWithContext?_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : Contract} {base : Context} {state : State} {self sender value : Word}
    {calldata : Bytes} {r : AbiCallResult}
    (h : Contract.callReceiveOrFallbackAtFromWithContext? n contract base state self sender value
      calldata = some r) :
    Contract.callReceiveOrFallbackAtFromWithContext? m contract base state self sender value
      calldata = some r := by
  unfold Contract.callReceiveOrFallbackAtFromWithContext? at h ⊢
  split at h
  next hempty =>
    try simp only [hempty, ite_true]
    split at h
    next function hf =>
      try simp only [hf]
      split at h
      next hacc =>
        try simp only [hacc, ite_true]
        dsimp only at h ⊢
        split at h
        next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
        next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
        next => cases h
      next hacc =>
        try simp only [hacc]
        exact h
    next hf =>
      try simp only [hf]
      exact Contract.callFallbackAtFromWithContext?_fuel_mono hnm h
  next hempty =>
    try simp only [hempty]
    exact Contract.callFallbackAtFromWithContext?_fuel_mono hnm h

/-- **ABI dispatch is fuel-monotone**: a result the dispatcher gives at some fuel, it gives at
every higher fuel, from any base context (whose self-dispatch hook, if any, does not depend on
the fuel). -/
theorem Contract.callCalldataAtFromWithContext?_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : Contract} {base : Context} {state : State} {self sender value : Word}
    {calldata : Bytes} {r : AbiCallResult}
    (h : Contract.callCalldataAtFromWithContext? n contract base state self sender value calldata
      = some r) :
    Contract.callCalldataAtFromWithContext? m contract base state self sender value calldata
      = some r := by
  unfold Contract.callCalldataAtFromWithContext? at h ⊢
  split at h
  next selector hsel =>
    try simp only [hsel]
    split at h
    next function hfind =>
      try simp only [hfind]
      split at h
      next args hdec =>
        try simp only [hdec]
        split at h
        next hacc =>
          try simp only [hacc, ite_true]
          dsimp only at h ⊢
          split at h
          next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
          next heq => rw [FunctionDef.call?_fuel_mono hnm heq]; exact h
          next => cases h
        next hacc =>
          try simp only [hacc]
          exact h
      next revert hdec =>
        try simp only [hdec]
        exact h
    next hfind =>
      try simp only [hfind]
      exact Contract.callFallbackAtFromWithContext?_fuel_mono hnm h
  next hsel =>
    try simp only [hsel]
    exact Contract.callReceiveOrFallbackAtFromWithContext?_fuel_mono hnm h

end ABI

end Source
end Solidity
end SolidCore

/--
info: 'SolidCore.Solidity.Source.FunctionDef.call?_fuel_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Solidity.Source.FunctionDef.call?_fuel_mono
