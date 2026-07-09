/-
# Fuel monotonicity for the source interpreter

## Design

The statement proved here, for every fuel-indexed evaluator of the statement
cluster (`Stmt.eval` / `Stmt.evalList` / `Stmt.evalWhile` / `Stmt.evalDoWhile`
/ `Stmt.evalFor`) and for the public seams built on them (`FunctionDef.call`,
`Contract.call`, `Contract.callTransaction`, and the `Checked.lean` tree entry
points `constructFromTree` / `constructTree` / `constructWithContextTree` /
`callTree` / `callTransactionTree`):

> If evaluation at fuel `n` produces a tree with **no reachable `outOfFuel`
> leaf** (for every possible answer at every request node), then evaluation at
> any fuel `m ≥ n` produces **the same tree, up to `Eq`**.

Why this exact shape:

* **"Not truncated" is `SolI.NoFuelStop`**, defined as
  `Interaction.AllDone (· ≠ .error outOfFuel)` — the frozen shared-alphabet
  predicate quantifying over *every* answer at *every* request. This is the
  strongest tree-level form: it makes the conclusion an exact tree equality
  rather than a pointwise per-responder statement, and any per-responder or
  folded corollary (`SolI.runWith`, `SolI.runFromContext`,
  `SolI.queryTranscript`, …) follows by rewriting with the equality.
  A weaker "the fold under one particular responder is not `outOfFuel`"
  hypothesis would not support exact tree equality (other branches could still
  truncate and change under more fuel), and exact tree equality is what the
  future lowering composition wants: `ForwardRel.trans`'s `hReflect` side
  condition needs "target out-of-fuel implies source already truncated", whose
  contrapositive workhorse is precisely "source not truncated at `n` ⇒ the
  source tree is fuel-stable above `n`".

* **Exact `Eq` on trees is attainable** because the interpreter's trees embed
  no fuel-dependent structure outside the recursion itself: expression
  evaluation (`Expr.evalWithRuntimeOrderFuel` and the whole expression/lvalue
  cluster) runs on its *own structural fuel* computed from the expression
  (`Expr.orderFuel expr + 1` etc.), independent of the statement fuel, and
  expression-fuel exhaustion is a `revert`, not `outOfFuel`. So the statement
  fuel is the *only* fuel parameter of the semantics, and it enters the tree
  only through the five statement-cluster evaluators. This is also why the
  mutual induction below is over the statement cluster only — that IS the
  whole fuel-indexed cluster; the expression evaluators are fuel-closed
  prefixes shared verbatim by both sides of the equality.

* **Coverage.** The mutual induction covers every arm of `Stmt.eval`
  (including `internalCall` / `internalCallPtr` recursion into function
  bodies, `tryExternalCall` / `tryContractCreate` success and catch bodies,
  and the three loop evaluators), and the corollaries cover the seams named
  above. The folded `?` adapters (`FunctionDef.call?`, `Contract.call?`, the
  ABI dispatch `Contract.callCalldata*?` family) are *consumers* of the trees:
  on a non-truncated tree they agree between fuels by rewriting with these
  equalities, so no separate statement is made for them.

## Proof structure

One step lemma per eval function (`eval_mono_step`, `evalList_mono_of`,
`evalWhile_mono_step`, `evalDoWhile_mono_step`, `evalFor_mono_step`), each
taking the needed monotonicity facts at the *previous* fuel as hypotheses, and
one plain induction on the low fuel (`fuelMonoAll`) tying them together. The
step lemmas share one tactic vocabulary: unfold one fuel layer
(`simp only [Stmt.eval…]`), rewrite fuel-independent *prefixes* through binds
(`SolI.NoFuelStop.of_bind` + the induction hypothesis), and push pointwise
into *continuations* with `SolI.bind_fuel_congr`, which turns
"`bind t kHi = bind t kLo`" into "`kHi = kLo` at every non-truncated leaf of
`t`" via the frozen `AllDone.bind_inv` / `AllDone.bind_congr`. This structure
is per-arm and per-function, so interpreter edits localize: a new statement
arm adds one `case` to `eval_mono_step` and nothing else.
-/
import SolidCore.Solidity.Checked

-- The step lemmas share one ite/match-reducing `simp only` vocabulary across
-- many arms; at some arms a given lemma is a no-op, which is intentional.
set_option linter.unusedSimpArgs false

namespace SolidCore
namespace Solidity
namespace Source

open EvmCompiler.Simulation (Interaction)

/-- A `SolI` tree is fuel-complete: no reachable terminal leaf is `outOfFuel`,
    for **every** possible answer at every request node. This is the formal
    "not truncated" of the fuel-monotonicity theorems below. -/
def SolI.NoFuelStop {α : Type} (tree : SolI α) : Prop :=
  Interaction.AllDone
    (fun outcome => outcome ≠ .error SolidityFailure.outOfFuel) tree

theorem SolI.NoFuelStop.outOfFuel_absurd {α : Type}
    (h : SolI.NoFuelStop (throw SolidityFailure.outOfFuel : SolI α)) :
    False := by
  have h' : Interaction.AllDone
      (fun outcome => outcome ≠ .error SolidityFailure.outOfFuel)
      (Interaction.done (Except.error SolidityFailure.outOfFuel) : SolI α) := h
  cases h' with
  | done hp => exact hp rfl

/-- A bound tree with no reachable `outOfFuel` leaf has a fuel-complete
    prefix. -/
theorem SolI.NoFuelStop.of_bind {α β : Type} {t : SolI α} {k : α → SolI β}
    (h : SolI.NoFuelStop (t >>= k)) : SolI.NoFuelStop t := by
  refine Interaction.AllDone.mono
    (Interaction.AllDone.bind_inv (next := k) h) ?_
  intro outcome hout
  cases outcome with
  | error err =>
      intro hEq
      have herr : err = SolidityFailure.outOfFuel := by injection hEq
      exact hout (by rw [herr])
  | ok v => simp

theorem SolI.NoFuelStop.of_map {α β : Type} {t : SolI α} {f : α → β}
    (h : SolI.NoFuelStop (f <$> t)) : SolI.NoFuelStop t :=
  SolI.NoFuelStop.of_bind
    (show SolI.NoFuelStop (t >>= fun v => pure (f v)) from h)

/-- The workhorse congruence: two binds over the same fuel-independent prefix
    are equal when the continuations agree at every non-truncated leaf the
    prefix can reach. -/
theorem SolI.bind_fuel_congr {α β : Type} {t : SolI α} {kHi kLo : α → SolI β}
    (h : SolI.NoFuelStop (t >>= kLo))
    (hk : ∀ v, SolI.NoFuelStop (kLo v) → kHi v = kLo v) :
    (t >>= kHi) = (t >>= kLo) := by
  show Interaction.bind t kHi = Interaction.bind t kLo
  exact Interaction.AllDone.bind_congr
    (Interaction.AllDone.bind_inv h) (fun v hv => hk v hv)

/-! ### Step lemmas, one per evaluator of the statement cluster -/

/-- `Stmt.evalList` is fuel-monotone at any pair of fuels at which `Stmt.eval`
    is (the list evaluator passes its fuel through unchanged). -/
private theorem evalList_mono_of (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt) :
    ∀ (table : FunctionTable) (context : Context) (stmts : List Stmt)
      (runtime : Runtime),
      SolI.NoFuelStop (Stmt.evalList n table context runtime stmts) →
      Stmt.evalList m table context runtime stmts
        = Stmt.evalList n table context runtime stmts := by
  intro table context stmts
  induction stmts with
  | nil => intro runtime _; simp only [Stmt.evalList]
  | cons s rest ihRest =>
    intro runtime hnf
    simp only [Stmt.evalList] at hnf ⊢
    rw [hEval _ _ _ _ hnf.of_bind]
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | normal runtime' => exact ihRest runtime' hv
    | returned runtime' values => rfl
    | selfdestructed runtime' => rfl
    | reverted runtime' err => rfl
    | broke runtime' => rfl
    | continued runtime' => rfl

private theorem evalWhile_mono_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt)
    (hWhile : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalWhile n table context runtime cond body) →
      Stmt.evalWhile m table context runtime cond body
        = Stmt.evalWhile n table context runtime cond body) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalWhile (n + 1) table context runtime cond body) →
      Stmt.evalWhile (m + 1) table context runtime cond body
        = Stmt.evalWhile (n + 1) table context runtime cond body := by
  intro table context runtime cond body hnf
  simp only [Stmt.evalWhile] at hnf ⊢
  refine SolI.bind_fuel_congr hnf ?_
  intro v hv
  cases v with
  | error err => rfl
  | ok p =>
    obtain ⟨value, runtime'⟩ := p
    try simp only [] at hv ⊢
    cases hw : value.expectWord with
    | error err => rfl
    | ok word =>
      rw [hw] at hv
      try simp only [] at hv ⊢
      cases ht : wordTruthy word with
      | false => rfl
      | true =>
        rw [ht] at hv
        rw [hEval _ _ _ _ hv.of_bind]
        refine SolI.bind_fuel_congr hv ?_
        intro w hw2
        cases w with
        | normal r2 => exact hWhile _ _ _ _ _ hw2
        | continued r2 => exact hWhile _ _ _ _ _ hw2
        | returned r2 vs => rfl
        | selfdestructed r2 => rfl
        | reverted r2 e => rfl
        | broke r2 => rfl

private theorem evalDoWhile_mono_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt)
    (hDoWhile : ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.NoFuelStop (Stmt.evalDoWhile n table context runtime body cond) →
      Stmt.evalDoWhile m table context runtime body cond
        = Stmt.evalDoWhile n table context runtime body cond) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (body : Stmt) (cond : Expr),
      SolI.NoFuelStop (Stmt.evalDoWhile (n + 1) table context runtime body cond) →
      Stmt.evalDoWhile (m + 1) table context runtime body cond
        = Stmt.evalDoWhile (n + 1) table context runtime body cond := by
  intro table context runtime body cond hnf
  simp only [Stmt.evalDoWhile] at hnf ⊢
  rw [hEval _ _ _ _ hnf.of_bind]
  refine SolI.bind_fuel_congr hnf ?_
  intro v hv
  cases v with
  | returned r' vs => rfl
  | selfdestructed r' => rfl
  | reverted r' e => rfl
  | broke r' => rfl
  | normal runtime' =>
    try simp only [] at hv ⊢
    refine SolI.bind_fuel_congr hv ?_
    intro w hw
    cases w with
    | error err => rfl
    | ok p =>
      obtain ⟨value, runtime''⟩ := p
      try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
      cases hword : value.expectWord with
      | error e => rfl
      | ok word =>
        rw [hword] at hw
        try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
        cases ht : wordTruthy word with
        | false => rfl
        | true =>
          rw [ht] at hw
          exact hDoWhile _ _ _ _ _ hw
  | continued runtime' =>
    try simp only [] at hv ⊢
    refine SolI.bind_fuel_congr hv ?_
    intro w hw
    cases w with
    | error err => rfl
    | ok p =>
      obtain ⟨value, runtime''⟩ := p
      try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
      cases hword : value.expectWord with
      | error e => rfl
      | ok word =>
        rw [hword] at hw
        try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
        cases ht : wordTruthy word with
        | false => rfl
        | true =>
          rw [ht] at hw
          exact hDoWhile _ _ _ _ _ hw

private theorem evalFor_mono_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt)
    (hFor : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalFor n table context runtime cond post body) →
      Stmt.evalFor m table context runtime cond post body
        = Stmt.evalFor n table context runtime cond post body) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.NoFuelStop
        (Stmt.evalFor (n + 1) table context runtime cond post body) →
      Stmt.evalFor (m + 1) table context runtime cond post body
        = Stmt.evalFor (n + 1) table context runtime cond post body := by
  intro table context runtime cond post body hnf
  simp only [Stmt.evalFor] at hnf ⊢
  refine SolI.bind_fuel_congr hnf ?_
  intro v hv
  cases v with
  | error err => rfl
  | ok p =>
    obtain ⟨value, runtime'⟩ := p
    try simp only [] at hv ⊢
    cases hw : value.expectWord with
    | error err => rfl
    | ok word =>
      rw [hw] at hv
      try simp only [] at hv ⊢
      cases ht : wordTruthy word with
      | false => rfl
      | true =>
        rw [ht] at hv
        rw [hEval _ _ _ _ hv.of_bind]
        refine SolI.bind_fuel_congr hv ?_
        intro w hw2
        cases w with
        | returned r2 vs => rfl
        | selfdestructed r2 => rfl
        | reverted r2 e => rfl
        | broke r2 => rfl
        | normal r2 =>
          try simp only [] at hw2 ⊢
          rw [hEval _ _ _ _ hw2.of_bind]
          refine SolI.bind_fuel_congr hw2 ?_
          intro u hu
          cases u with
          | normal posted => exact hFor _ _ _ _ _ _ hu
          | returned r3 vs => rfl
          | selfdestructed r3 => rfl
          | reverted r3 e => rfl
          | broke r3 => rfl
          | continued r3 => rfl
        | continued r2 =>
          try simp only [] at hw2 ⊢
          rw [hEval _ _ _ _ hw2.of_bind]
          refine SolI.bind_fuel_congr hw2 ?_
          intro u hu
          cases u with
          | normal posted => exact hFor _ _ _ _ _ _ hu
          | returned r3 vs => rfl
          | selfdestructed r3 => rfl
          | reverted r3 e => rfl
          | broke r3 => rfl
          | continued r3 => rfl

set_option maxHeartbeats 1600000 in
/-- One fuel layer of `Stmt.eval`, given monotonicity of the whole cluster at
    the previous fuel. One `case` per fuel-dependent statement arm; every
    fuel-free arm is discharged by the unfolding `simp` itself. -/
private theorem eval_mono_step (n m : Nat)
    (hEval : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt)
    (hList : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmts : List Stmt),
      SolI.NoFuelStop (Stmt.evalList n table context runtime stmts) →
      Stmt.evalList m table context runtime stmts
        = Stmt.evalList n table context runtime stmts)
    (hWhile : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalWhile n table context runtime cond body) →
      Stmt.evalWhile m table context runtime cond body
        = Stmt.evalWhile n table context runtime cond body)
    (hDoWhile : ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.NoFuelStop (Stmt.evalDoWhile n table context runtime body cond) →
      Stmt.evalDoWhile m table context runtime body cond
        = Stmt.evalDoWhile n table context runtime body cond)
    (hFor : ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalFor n table context runtime cond post body) →
      Stmt.evalFor m table context runtime cond post body
        = Stmt.evalFor n table context runtime cond post body) :
    ∀ (table : FunctionTable) (context : Context) (runtime : Runtime)
      (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval (n + 1) table context runtime stmt) →
      Stmt.eval (m + 1) table context runtime stmt
        = Stmt.eval (n + 1) table context runtime stmt := by
  intro table context runtime stmt hnf
  cases stmt <;> simp only [Stmt.eval] at hnf ⊢
  case block body =>
    rw [hList _ _ _ _ hnf.of_bind]
  case captureReturn returnNames body =>
    rw [hEval _ _ _ _ hnf.of_bind]
  case internalCall targets callee args =>
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | error err => rfl
    | ok p =>
      obtain ⟨argValues, runtime'⟩ := p
      try simp only [] at hv ⊢
      cases hlk : table.lookup? callee with
      | none => rfl
      | some fn =>
        rw [hlk] at hv
        try simp only [] at hv ⊢
        cases hen : internalCallEnter? fn argValues runtime' with
        | none => rfl
        | some pr =>
          obtain ⟨calleeRuntime, savedLocals⟩ := pr
          rw [hen] at hv
          try simp only [] at hv ⊢
          rw [hEval _ _ _ _ hv.of_bind]
  case internalCallPtr targets fnExpr args =>
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | error err => rfl
    | ok p =>
      obtain ⟨value, runtimeFn⟩ := p
      cases value <;> try rfl
      case internalFunction id =>
        try simp only [] at hv ⊢
        refine SolI.bind_fuel_congr hv ?_
        intro w hw
        cases w with
        | error err => rfl
        | ok q =>
          obtain ⟨argValues, runtime'⟩ := q
          try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
          cases hlk : table.lookupById? id with
          | none => rfl
          | some fn =>
            rw [hlk] at hw
            try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
            cases hen : internalCallEnter? fn argValues runtime' with
            | none => rfl
            | some pr =>
              obtain ⟨calleeRuntime, savedLocals⟩ := pr
              rw [hen] at hw
              try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
              rw [hEval _ _ _ _ hw.of_bind]
  case ifElse cond thenBranch elseBranch =>
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | error err => rfl
    | ok p =>
      obtain ⟨value, runtime'⟩ := p
      try simp only [] at hv ⊢
      cases hw : value.expectWord with
      | error err => rfl
      | ok word =>
        rw [hw] at hv
        try simp only [] at hv ⊢
        cases ht : wordTruthy word with
        | false =>
            rw [ht] at hv
            exact hEval _ _ _ _ hv
        | true =>
            rw [ht] at hv
            exact hEval _ _ _ _ hv
  case «switch» discr cs defaultBranch =>
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | error err => rfl
    | ok p =>
      obtain ⟨value, runtime'⟩ := p
      try simp only [] at hv ⊢
      cases hw : value.expectWord with
      | error err => rfl
      | ok word =>
        rw [hw] at hv
        try simp only [] at hv ⊢
        cases hb : Stmt.findSwitchBranch? word cs with
        | some branch =>
            rw [hb] at hv
            cases defaultBranch with
            | some d => exact hEval _ _ _ _ hv
            | none => exact hEval _ _ _ _ hv
        | none =>
            rw [hb] at hv
            cases defaultBranch with
            | some branch => exact hEval _ _ _ _ hv
            | none => rfl
  case whileLoop cond body =>
    exact hWhile _ _ _ _ _ hnf
  case doWhile body cond =>
    exact hDoWhile _ _ _ _ _ hnf
  case forLoop init cond post body =>
    rw [hEval _ _ _ _ hnf.of_bind]
    refine SolI.bind_fuel_congr hnf ?_
    intro v hv
    cases v with
    | returned r' vs => rfl
    | selfdestructed r' => rfl
    | reverted r' e => rfl
    | broke r' => rfl
    | continued r' => rfl
    | normal initialized =>
      try simp only [] at hv ⊢
      rw [hFor _ _ _ _ _ _ hv.of_bind]
  case tryExternalCall kind targetExpr calldataExpr valueExpr gasExprOpt
      gasFirst checkTargetCode rets retCleanups successBody catchClauses =>
    cases h1 : targetExpr.evalWithRuntimeByContext context runtime with
    | error err => rfl
    | ok p1 =>
      obtain ⟨targetValue, runtime'⟩ := p1
      rw [h1] at hnf
      try simp only [] at hnf ⊢
      cases h2 : targetValue.expectWord with
      | error err => rfl
      | ok target =>
        rw [h2] at hnf
        try simp only [] at hnf ⊢
        -- New eval order (gap EO1): the call options (value/gas ordered by
        -- `gasFirst`) are evaluated BEFORE the calldata argument. Split the
        -- options result FIRST, thread its runtime (`runtimeOpts`) into the
        -- calldata evaluation, then the calldata, `asBytes?`, and finally the
        -- missingCode `if` + the two bind branches.
        split
        next value gasOpt runtimeOpts heq =>
          rw [heq] at hnf
          try simp only [] at hnf ⊢
          cases h3 : calldataExpr.evalWithRuntimeByContext context runtimeOpts with
          | error err => rfl
          | ok p2 =>
            obtain ⟨calldataValue, runtime'''⟩ := p2
            rw [h3] at hnf
            try simp only [] at hnf ⊢
            cases h4 : calldataValue.asBytes? with
            | none => rfl
            | some calldata =>
              rw [h4] at hnf
              try simp only [] at hnf ⊢
              -- gap A1/A3: the `extcodesize` existence guard now reverts the
              -- caller UNCATCHABLY *before* the CALL.  Split it: the missing-code
              -- branch is a fuel-free `Result.reverted` (closed by `simp` as a
              -- reflexivity goal), so only the has-code branch — which performs
              -- the CALL — carries the fuel-dependent continuation.
              split <;> rename_i hmc <;>
                simp only [hmc, Bool.false_eq_true, if_true, if_false] at hnf ⊢
              refine SolI.bind_fuel_congr hnf ?_
              intro w hw
              obtain ⟨callResult, adoptedState⟩ := w
              try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
              cases hs : callResult.success with
              | false =>
                rw [hs] at hw
                try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                cases hcm : TryCatchClause.findMatch?
                    (callResult.output.map normByte) catchClauses with
                | none => rfl
                | some fb =>
                  obtain ⟨frame, body⟩ := fb
                  rw [hcm] at hw
                  try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                  rw [hEval _ _ _ _ hw.of_bind]
              | true =>
                rw [hs] at hw
                try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                cases habi : abiDecodeValues? (rets.map BindingDecl.ty)
                    (callResult.output.map normByte) with
                | none => rfl
                | some decoded =>
                  rw [habi] at hw
                  try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                  cases hacc : AbiCleanups.acceptOrUnspecified
                      retCleanups decoded with
                  | false => rfl
                  | true =>
                    rw [hacc] at hw
                    try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                    cases hbind : BindingDecl.bindArgs? rets decoded with
                    | none => rfl
                    | some frame =>
                      rw [hbind] at hw
                      try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                      rw [hEval _ _ _ _ hw.of_bind]
        next runtimeFailed err heq => rfl
  case tryContractCreate contractName ctorArgsExpr valueExpr saltExprOpt
      rets successBody catchClauses =>
    cases h1 : ctorArgsExpr.evalWithRuntimeByContext context runtime with
    | error err => rfl
    | ok p1 =>
      obtain ⟨argsValue, runtime'⟩ := p1
      rw [h1] at hnf
      try simp only [] at hnf ⊢
      cases h2 : argsValue.asBytes? with
      | none => rfl
      | some constructorArgs =>
        rw [h2] at hnf
        try simp only [] at hnf ⊢
        cases h3 : valueExpr.evalWithRuntimeByContext context runtime' with
        | error err => rfl
        | ok p2 =>
          obtain ⟨valueValue, runtime''⟩ := p2
          rw [h3] at hnf
          try simp only [] at hnf ⊢
          cases h4 : valueValue.expectWord with
          | error err => rfl
          | ok value =>
            rw [h4] at hnf
            try simp only [] at hnf ⊢
            split
            next saltOpt runtime''' heq =>
              rw [heq] at hnf
              try simp only [] at hnf ⊢
              refine SolI.bind_fuel_congr hnf ?_
              intro w hw
              obtain ⟨createResult, adoptedState⟩ := w
              try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
              cases hs : createResult.success with
              | false =>
                rw [hs] at hw
                try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                cases hcm : TryCatchClause.findMatch?
                    (createResult.output.map normByte) catchClauses with
                | none => rfl
                | some fb =>
                  obtain ⟨frame, body⟩ := fb
                  rw [hcm] at hw
                  try simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                  rw [hEval _ _ _ _ hw.of_bind]
              | true =>
                rw [hs] at hw
                simp only [Bool.false_eq_true, if_true, if_false] at hw ⊢
                cases hB : BindingDecl.bindArgs? rets
                    (if rets.isEmpty then [] else [Value.word createResult.address]) with
                | none => rfl
                | some frame =>
                  rw [hB] at hw
                  simp only [] at hw ⊢
                  rw [hEval _ _ _ _ hw.of_bind]
            next err heq => rfl
  case checked body =>
    exact hEval _ _ _ _ hnf
  case unchecked body =>
    exact hEval _ _ _ _ hnf

/-! ### The mutual fuel induction -/

private theorem fuelMonoAll (n : Nat) :
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (stmt : Stmt),
      SolI.NoFuelStop (Stmt.eval n table context runtime stmt) →
      Stmt.eval m table context runtime stmt
        = Stmt.eval n table context runtime stmt) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (stmts : List Stmt),
      SolI.NoFuelStop (Stmt.evalList n table context runtime stmts) →
      Stmt.evalList m table context runtime stmts
        = Stmt.evalList n table context runtime stmts) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (cond : Expr) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalWhile n table context runtime cond body) →
      Stmt.evalWhile m table context runtime cond body
        = Stmt.evalWhile n table context runtime cond body) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (body : Stmt) (cond : Expr),
      SolI.NoFuelStop (Stmt.evalDoWhile n table context runtime body cond) →
      Stmt.evalDoWhile m table context runtime body cond
        = Stmt.evalDoWhile n table context runtime body cond) ∧
    (∀ m, n ≤ m → ∀ (table : FunctionTable) (context : Context)
      (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt),
      SolI.NoFuelStop (Stmt.evalFor n table context runtime cond post body) →
      Stmt.evalFor m table context runtime cond post body
        = Stmt.evalFor n table context runtime cond post body) := by
  induction n with
  | zero =>
    have hEval0 : ∀ m, 0 ≤ m → ∀ (table : FunctionTable) (context : Context)
        (runtime : Runtime) (stmt : Stmt),
        SolI.NoFuelStop (Stmt.eval 0 table context runtime stmt) →
        Stmt.eval m table context runtime stmt
          = Stmt.eval 0 table context runtime stmt := by
      intro m _ table context runtime stmt hnf
      simp only [Stmt.eval] at hnf
      exact hnf.outOfFuel_absurd.elim
    refine ⟨hEval0, ?_, ?_, ?_, ?_⟩
    · intro m hm table context runtime stmts hnf
      exact evalList_mono_of 0 m
        (fun tb c r s h => hEval0 m hm tb c r s h)
        table context stmts runtime hnf
    · intro m hm table context runtime cond body hnf
      simp only [Stmt.evalWhile] at hnf
      exact hnf.outOfFuel_absurd.elim
    · intro m hm table context runtime body cond hnf
      simp only [Stmt.evalDoWhile] at hnf
      exact hnf.outOfFuel_absurd.elim
    · intro m hm table context runtime cond post body hnf
      simp only [Stmt.evalFor] at hnf
      exact hnf.outOfFuel_absurd.elim
  | succ n ihn =>
    obtain ⟨ihEval, ihList, ihWhile, ihDoWhile, ihFor⟩ := ihn
    have hEvalS : ∀ m, n + 1 ≤ m → ∀ (table : FunctionTable)
        (context : Context) (runtime : Runtime) (stmt : Stmt),
        SolI.NoFuelStop (Stmt.eval (n + 1) table context runtime stmt) →
        Stmt.eval m table context runtime stmt
          = Stmt.eval (n + 1) table context runtime stmt := by
      intro m hm table context runtime stmt hnf
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact eval_mono_step n m'
          (fun tb c r s h => ihEval m' hm' tb c r s h)
          (fun tb c r ss h => ihList m' hm' tb c r ss h)
          (fun tb c r cd bd h => ihWhile m' hm' tb c r cd bd h)
          (fun tb c r bd cd h => ihDoWhile m' hm' tb c r bd cd h)
          (fun tb c r cd ps bd h => ihFor m' hm' tb c r cd ps bd h)
          table context runtime stmt hnf
    refine ⟨hEvalS, ?_, ?_, ?_, ?_⟩
    · intro m hm table context runtime stmts hnf
      exact evalList_mono_of (n + 1) m
        (fun tb c r s h => hEvalS m hm tb c r s h)
        table context stmts runtime hnf
    · intro m hm table context runtime cond body hnf
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalWhile_mono_step n m'
          (fun tb c r s h => ihEval m' hm' tb c r s h)
          (fun tb c r cd bd h => ihWhile m' hm' tb c r cd bd h)
          table context runtime cond body hnf
    · intro m hm table context runtime body cond hnf
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalDoWhile_mono_step n m'
          (fun tb c r s h => ihEval m' hm' tb c r s h)
          (fun tb c r bd cd h => ihDoWhile m' hm' tb c r bd cd h)
          table context runtime body cond hnf
    · intro m hm table context runtime cond post body hnf
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ m' =>
        have hm' : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact evalFor_mono_step n m'
          (fun tb c r s h => ihEval m' hm' tb c r s h)
          (fun tb c r cd ps bd h => ihFor m' hm' tb c r cd ps bd h)
          table context runtime cond post body hnf

/-! ### Public statements -/

/-- **Fuel monotonicity, statements.** A non-truncated evaluation is
    fuel-stable: any fuel `m ≥ n` produces the identical tree. -/
theorem Stmt.eval_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {runtime : Runtime}
    {stmt : Stmt}
    (hnf : SolI.NoFuelStop (Stmt.eval n table context runtime stmt)) :
    Stmt.eval m table context runtime stmt
      = Stmt.eval n table context runtime stmt :=
  (fuelMonoAll n).1 m hnm table context runtime stmt hnf

theorem Stmt.evalList_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {runtime : Runtime}
    {stmts : List Stmt}
    (hnf : SolI.NoFuelStop (Stmt.evalList n table context runtime stmts)) :
    Stmt.evalList m table context runtime stmts
      = Stmt.evalList n table context runtime stmts :=
  (fuelMonoAll n).2.1 m hnm table context runtime stmts hnf

theorem Stmt.evalWhile_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {runtime : Runtime}
    {cond : Expr} {body : Stmt}
    (hnf : SolI.NoFuelStop (Stmt.evalWhile n table context runtime cond body)) :
    Stmt.evalWhile m table context runtime cond body
      = Stmt.evalWhile n table context runtime cond body :=
  (fuelMonoAll n).2.2.1 m hnm table context runtime cond body hnf

theorem Stmt.evalDoWhile_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {runtime : Runtime}
    {body : Stmt} {cond : Expr}
    (hnf : SolI.NoFuelStop (Stmt.evalDoWhile n table context runtime body cond)) :
    Stmt.evalDoWhile m table context runtime body cond
      = Stmt.evalDoWhile n table context runtime body cond :=
  (fuelMonoAll n).2.2.2.1 m hnm table context runtime body cond hnf

theorem Stmt.evalFor_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {runtime : Runtime}
    {cond : Expr} {post : Stmt} {body : Stmt}
    (hnf : SolI.NoFuelStop
      (Stmt.evalFor n table context runtime cond post body)) :
    Stmt.evalFor m table context runtime cond post body
      = Stmt.evalFor n table context runtime cond post body :=
  (fuelMonoAll n).2.2.2.2 m hnm table context runtime cond post body hnf

/-! ### Corollaries at the public seams -/

theorem FunctionDef.evalBodyEntry_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {tree : SolI Result}
    (h : FunctionDef.evalBodyEntry n table context function state args
      = some tree)
    (hnf : SolI.NoFuelStop tree) :
    FunctionDef.evalBodyEntry m table context function state args
      = some tree := by
  simp only [FunctionDef.evalBodyEntry] at h ⊢
  cases hacc : function.acceptsValue context.value with
  | false =>
    rw [hacc] at h
    exact h
  | true =>
    rw [hacc] at h
    cases hframe : function.initialFrame? args with
    | none =>
      rw [hframe] at h
      simp at h
    | some frame =>
      rw [hframe] at h
      try simp only [] at h ⊢
      injection h with h
      subst h
      rw [Stmt.eval_fuel_mono hnm hnf]
      simp

theorem FunctionDef.call_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {table : FunctionTable} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {tree : SolI CallResult}
    (h : FunctionDef.call n table context function state args = some tree)
    (hnf : SolI.NoFuelStop tree) :
    FunctionDef.call m table context function state args = some tree := by
  unfold FunctionDef.call at h ⊢
  cases hentry : FunctionDef.evalBodyEntry n table context function state args
      with
  | none =>
    rw [hentry] at h
    simp at h
  | some t0 =>
    rw [hentry] at h
    have htree : Functor.map (function.callBodyResult state) t0 = tree := by
      simpa using h
    have hnf0 : SolI.NoFuelStop t0 :=
      SolI.NoFuelStop.of_map (f := function.callBodyResult state)
        (by rw [htree]; exact hnf)
    rw [FunctionDef.evalBodyEntry_fuel_mono hnm hentry hnf0]
    simpa using htree

theorem Contract.call_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : Contract} {target : CallTarget} {state : State}
    {args : List Value} {tree : SolI CallResult}
    (h : Contract.call n contract target state args = some tree)
    (hnf : SolI.NoFuelStop tree) :
    Contract.call m contract target state args = some tree := by
  unfold Contract.call at h ⊢
  cases hres : contract.resolveCallFunction? target args with
  | none =>
    rw [hres] at h
    simp at h
  | some function =>
    rw [hres] at h
    exact FunctionDef.call_fuel_mono hnm h hnf

theorem Contract.callTransaction_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : Contract} {target : CallTarget} {state : State}
    {args : List Value} {tree : SolI CallResult}
    (h : Contract.callTransaction n contract target state args = some tree)
    (hnf : SolI.NoFuelStop tree) :
    Contract.callTransaction m contract target state args = some tree := by
  unfold Contract.callTransaction at h ⊢
  cases hcall : Contract.call n contract target state.clearTransient args with
  | none =>
    rw [hcall] at h
    simp at h
  | some t0 =>
    rw [hcall] at h
    have htree : Functor.map CallResult.clearTransient t0 = tree := by
      simpa using h
    have hnf0 : SolI.NoFuelStop t0 :=
      SolI.NoFuelStop.of_map (f := CallResult.clearTransient)
        (by rw [htree]; exact hnf)
    rw [Contract.call_fuel_mono hnm hcall hnf0]
    simpa using htree

end Source

namespace TypeCheck

open SolidCore.Solidity.Source (SolI FunctionDef Contract)

/-! ### Corollaries at the `Checked.lean` tree entry points -/

theorem CheckedContract.constructFromTree_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : CheckedContract} {state : CoreState} {sender value : Word}
    {args : List CoreValue} {tree : SolI CoreCallResult}
    (h : CheckedContract.constructFromTree n contract state sender value args
      = some tree)
    (hnf : Source.SolI.NoFuelStop tree) :
    CheckedContract.constructFromTree m contract state sender value args
      = some tree := by
  unfold CheckedContract.constructFromTree at h ⊢
  cases hc : CheckedProgram.constructorFunctionFor? contract.program
      contract.decl with
  | none =>
    rw [hc] at h
    simp at h
  | some ctor =>
    rw [hc] at h
    exact Source.FunctionDef.call_fuel_mono hnm h hnf

theorem CheckedContract.constructWithContextTree_fuel_mono {n m : Nat}
    (hnm : n ≤ m)
    {contract : CheckedContract} {context : CoreContext} {state : CoreState}
    {sender value : Word} {args : List CoreValue} {tree : SolI CoreCallResult}
    (h : CheckedContract.constructWithContextTree n contract context state
      sender value args = some tree)
    (hnf : Source.SolI.NoFuelStop tree) :
    CheckedContract.constructWithContextTree m contract context state
      sender value args = some tree := by
  unfold CheckedContract.constructWithContextTree at h ⊢
  cases hc : CheckedProgram.constructorFunctionFor? contract.program
      contract.decl with
  | none =>
    rw [hc] at h
    simp at h
  | some ctor =>
    rw [hc] at h
    exact Source.FunctionDef.call_fuel_mono hnm h hnf

theorem CheckedContract.constructTree_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : CheckedContract} {state : CoreState} {args : List CoreValue}
    {tree : SolI CoreCallResult}
    (h : CheckedContract.constructTree n contract state args = some tree)
    (hnf : Source.SolI.NoFuelStop tree) :
    CheckedContract.constructTree m contract state args = some tree :=
  CheckedContract.constructFromTree_fuel_mono hnm h hnf

/-- **Fuel monotonicity at the composition seam** (`callTree`): a
    non-truncated call tree at fuel `n` is the tree at every fuel `m ≥ n`. -/
theorem CheckedContract.callTree_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : CheckedContract} {target : CallTarget} {state : CoreState}
    {args : List CoreValue} {tree : SolI CoreCallResult}
    (h : CheckedContract.callTree n contract target state args = some tree)
    (hnf : Source.SolI.NoFuelStop tree) :
    CheckedContract.callTree m contract target state args = some tree :=
  Source.Contract.call_fuel_mono hnm h hnf

theorem CheckedContract.callTransactionTree_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : CheckedContract} {target : CallTarget} {state : CoreState}
    {args : List CoreValue} {tree : SolI CoreCallResult}
    (h : CheckedContract.callTransactionTree n contract target state args
      = some tree)
    (hnf : Source.SolI.NoFuelStop tree) :
    CheckedContract.callTransactionTree m contract target state args
      = some tree :=
  Source.Contract.callTransaction_fuel_mono hnm h hnf

end TypeCheck

end Solidity
end SolidCore
