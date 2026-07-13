# STMT_DISPATCH_UNIFY_DESIGN — one env-threaded statement recursion

Branch `rearch/stmt-dispatch-unify`, base `403390d` (main = WS1 landed).
Successor to `LOWERING_UNIFY_DESIGN.md` §3c (which recorded the dispatch
collapse as residual debt) and `ENV_LOWERING_DESIGN.md` (R2). This branch
performs the *structural* unification only: the two parallel statement
lowerings become one env-threaded recursion with an OPTIONAL env, with
**zero observable behavior change** — every emitted `Core` is byte-identical,
every acceptance verdict unchanged.

## 1. The two current signatures

Env-free (early mutual block, lines ~4381–7321, structural
`(sizeOf, k)` termination; the PRIMARY lowering for importer/getter/
constructor synthesis and the acceptance-preserving fallback everywhere):

```
Stmt.toCore?           (storageNames : List Name) : Stmt -> Option CoreStmt
Stmt.listToCore?       (storageNames : List Name) : List Stmt -> Option (List CoreStmt)
CatchClause.toCore?    (storageNames : List Name) (clause : CatchClause) : Option CoreTryCatchClause
CatchClause.listToCore? (storageNames : List Name) : List CatchClause -> Option (List CoreTryCatchClause)
```

Env-aware (giant fuel mutual block, lines ~14511–20587, 32 members,
lexicographic `(internalFuel, size, k)` termination, no `decreasing_by`):

```
Stmt.toCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (stmt : Stmt) : Option CoreStmt
```
plus `Stmt.listToCoreWithInternalCallsWithRefs?`,
`CatchClause.toCoreWithInternalCalls?`, `CatchClause.listToCoreWithInternalCalls?`.

Dependency is strictly one-directional: env-aware → env-free (155 textual
`Stmt.toCore?` occurrences: 1 default re-dispatch arm, the rest
acceptance-preserving `| none =>` fallbacks and synthesis PRIMARY uses).
The env-free family never calls the env-aware family.

A third layer sits *between* them in the file: the modifier-expansion
middle family, env-free-statement-dependent and called FROM the giant block
(`functionExpandModifiersToCoreWithInternalCalls?` → `modifierApplyToCoreWithEnv?`
→ `Stmt.toCoreReplacingModifierPlaceholder?` → `Stmt.toCore?`). Any physical
move of the env-free bodies must carry this family along. A fourth cluster
(`functionExpandModifiers?`, `modifierApplyToCore?`,
`functionExpandModifiersToCore?`) is DEAD (self-references only, verified
repo-wide) and is deleted.

## 2. The unified signature

Env-optionality is an `Option` of a context bundle:

```
structure StmtLoweringCtx where
  storageRefEnv : StorageRefEnv
  env : TypeEnv
  externalCallKindEnv : ExternalCallKindEnv
  modifiers : List SourceModifierDecl
  functions : List FunctionDecl
  freeFunctions : List FunctionDecl
  returnTys : List Ty

def Stmt.lowerCore? (internalFuel : Nat) (ctx? : Option StmtLoweringCtx)
    (storageNames : List Name) (stmt : Stmt) : Option CoreStmt :=
  match ctx? with
  | some ctx => -- env-AWARE: the toCoreWithInternalCalls? dispatch, VERBATIM
  | none     => -- env-FREE: the toCore? arms, VERBATIM (fuel/ctx never read)
```

plus `Stmt.listLowerCore?`, `CatchClause.lowerCore?`,
`CatchClause.listLowerCore?` with the same `ctx?` threading.

Both old entry points become thin wrapper MEMBERS of the same mutual block,
keeping their exact names and signatures (so all ~180 call sites in
`Interface.lean`, the witnesses, and the synthesis paths are textually
untouched):

```
Stmt.toCore? storageNames stmt            := Stmt.lowerCore? 0 none storageNames stmt
Stmt.toCoreWithInternalCalls? fuel … stmt := Stmt.lowerCore? fuel (some ⟨…⟩) storageNames stmt
```

(8 wrappers total: the 4 env-free names + the 4 env-aware names.)
The `none` mode ignores `internalFuel` entirely (the env-free body is
fuel-free), so the wrapper's `0` is inert.

## 3. Equivalence argument

This is a pure code-motion refactor; no arm body is edited:

- `env = some ctx` reproduces `Stmt.toCoreWithInternalCalls?`: the some-branch
  IS the old dispatcher body, moved verbatim (its 8 parameters restored by
  destructuring `ctx`). Its internal calls still go through the OLD NAMES,
  which are now identity wrappers over the unified recursion.
- `env = none` reproduces `Stmt.toCore?`: the none-branch IS the old env-free
  body, moved verbatim; its recursive calls (`Stmt.toCore?`,
  `Stmt.listToCore?`, `CatchClause.listToCore?`) also route through the
  identity wrappers.
- The old mutual-recursion knot (env-aware ↔ env-free via fallbacks) becomes
  self-recursion of ONE function under the two `ctx?` modes.

Since every body is verbatim and every wrapper is an identity delegation,
emitted core is definitionally unchanged — the differential/lane/witness
runs below are confirmation, not the argument.

## 4. Arm migration map

- env-AWARE-only arms: 89 merged arms / 117 `| Stmt.*` patterns → the
  `some` branch (verbatim). The single literal re-dispatch arm
  (`| other => Stmt.toCore? storageNames other`) remains textually the same
  but is now a self-recursion into the `none` mode of the SAME function.
- env-FREE-only arms: ~34 arms → the `none` branch (verbatim); they serve
  both as none-mode PRIMARY and as the some-mode fallback target.
- shared arms: none exist to merge — WS1 §3c measured that the two paths
  share no arm bodies (the env-aware arms do hoisting/env work the env-free
  arms don't); the duplication being deleted is the *second recursion knot*
  and the standalone env-free defs, not arm text.

## 5. Termination plan (the actual engineering content)

The env-free family terminates structurally; the giant block terminates on
`(internalFuel, size, k)`. Merging them creates ~155 new in-knot edges, all
of the shape "same fuel, same statement, env-aware → env-free". These cannot
decrease on fuel or size, so the measure gains a LAYER slot; k values are
doubled to open odd slots for the unified fns between wrappers and existing
members:

- New measure shape, all block members: `(fuel, layer, size, 2·k_old)`.
- Layers: env-aware members = 3; `modifierApplyToCoreWithEnv?` = 2;
  `Stmt.toCoreReplacingModifierPlaceholder?` family +
  `modifierParamBindingsToCoreWithEnv?` = 1; env-free mode/wrappers = 0.
- `Stmt.lowerCore?` measure:
  `(internalFuel, match ctx? with | some _ => 3 | none => 0, sizeOf stmt, 9)`;
  list/catch/catch-list unified fns at k = 7/5/7.
- Wrappers: env-aware names keep the old dispatcher slots
  `(fuel, 3, size, {10,8,6,8})`; env-free names get `(0, 0, size, {10,8,6,8})`.

Edge audit (every class of in-knot edge):
- aware → free fallback (same fuel/stmt): fuel =, layer 3→0 ✓.
- helper → env-free wrapper: fuel strict when fuel>0, else layer 3→0 ✓.
- none-mode self-recursion: fuel =, layer =, size strict (structural) ✓.
- some-mode edges: identical to today's block obligations with an equal
  layer component inserted and k doubled (order-preserving) ✓.
- wrapper → unified: everything equal, k 10→9 / 8→7 / 6→5 ✓.
- block → `modifierApplyToCoreWithEnv?` `(0,2,0,·)`: fuel strict or layer 3→2 ✓.
- modifierApply → placeholder-replace `(0,1,sizeOf stmt,·)`: layer 2→1 ✓
  (this is the edge that forces layer 2: the replaced body's size is
  unrelated to the caller's arguments).
- placeholder-replace → env-free wrapper (incl. the same-size
  `| other => Stmt.toCore? …` default): layer 1→0 ✓.

## 6. Stages

- Stage 0: this note.
- Stage 1: measure widening only — insert `3` layer slot + double k in all 32
  block `termination_by` clauses. No behavior surface at all. Build green.
- Stage 2: delete the dead env-free modifier cluster; move the middle family
  (`Stmt.toCoreReplacingModifierPlaceholder?` mutual,
  `modifierParamBindingsToCoreWithEnv?`, `modifierApplyToCoreWithEnv?`) into
  the giant block with layer-1/2 measures. Bodies verbatim. Build green.
- Stage 3: the unification — add `StmtLoweringCtx`, the 4 unified fns
  (bodies = the 8 old bodies moved verbatim), the 8 wrappers; delete the 4
  env-free defs from the early mutual block. Build green + differential.
- Stage 4: self-gate lanes, doc updates.

## 7. Verification

- Full `lake build` (~1147 jobs) incl. FuelMonotonicity + AdoptionLaws (WS1
  measured 0 references to the lowering family in both — expect NO change)
  and every witness `#guard` (Witness/Interface.lean pins `Stmt.toCore?`
  outputs directly).
- Emitted-core differential: `#eval`-repr dumps of lowered fixture contracts
  captured at base vs post-Stage-3; byte-identical required.
- Acceptance differential on representative accept/reject fixtures.
- Sequential self-gate lanes: openzeppelin-erc20, openzeppelin-access-control,
  reference-assignments, reference-delete, storage-counter,
  cond-narrow-cleanup, builtin-arg-residue, lowering-unify-audit + getter/
  constructor/call-position lanes. Full 265-case replay is the orchestrator's.
