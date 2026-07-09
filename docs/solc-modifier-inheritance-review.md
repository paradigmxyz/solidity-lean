# solc modifier / inheritance / dispatch review (Fable adversarial pass)

Scope: modifiers, inheritance/dispatch, constructor semantics, overload resolution.
Method: deep read of solc 0.8.35 source (`/Users/dan/Projects/solidity-src`,
pin 47b9dedd), cross-checked against the pinned binary and — for the two
confirmed items — **run end-to-end under `forge` with the default (legacy)
codegen**, which is the corpus ground truth (default `foundry.toml` sets no
`via_ir`; only `tests/forge-harness/reference-via-ir-memory-storage` opts in).

## Confirmed divergences

### DIV-CTOR-1 — base-constructor ARGUMENT evaluation order (HIGH, confidence: confirmed)

**Repro**
```solidity
contract A {
    uint public trace;
    function r(uint n) internal returns (uint) { trace = trace * 10 + n; return n; }
    constructor(uint) { r(1); }
}
contract B is A { constructor(uint) A(r(2)) { r(3); } }
contract D is B { constructor() B(r(4)) { r(5); } }
// deploy D, read trace
```

**solc**: `trace == 42135` (verified: `forge test`, legacy codegen; also matches
`--ir`). Execution order = `r(4), r(2), r(1), r(3), r(5)`.
Source: `ContractCompiler::appendBaseConstructor` evaluates the args a contract
supplies to its base *then* recurses into the base
(`ContractCompiler.cpp:264-283`); the recursion at
`ContractCompiler.cpp:641-645` runs before the body at line 655. Net: each
derived contract evaluates its base's args (descending, derived→base), all
bodies run ascending (base→derived). The `--ir` path is identical
(`IRGenerator.cpp:899-907`: `<evalBaseArguments>; <nextConstructor>; <initStateVariables>; <body>`).

**solidity-lean**: `trace == 21435`. Execution order = `r(2), r(1), r(4), r(3), r(5)`.
`ContractDecl.constructorFunctionFromOrders?` assembles one piece per contract
in **storageOrder (base→derived)** and concatenates them
(`Interface.lean:20459-20483`). Each *base* piece is
`initStmts ++ [block(baseArgCore ++ [bodyCore])]`
(`ContractDecl.constructorBodyForDeployment?`, `Interface.lean:19755-19760`),
where `baseArgCore` binds *that base's* incoming args
(`baseConstructorArgsForDeployment?`, `Interface.lean:20469-20471`). So the args
B supplies to A (`r(2)`) are evaluated at A's position — first — instead of in
B's frame during descent. This reorders every side-effecting base-constructor
argument relative to the constructor bodies.

**Classification**: wrong-observable (miscompile). Diverges from BOTH legacy and
via-ir codegens, so unambiguous.

### DIV-CTOR-2 — inline state-variable initializers vs base constructor bodies (MEDIUM-HIGH, confidence: confirmed vs legacy)

**Repro**
```solidity
contract A2 {
    uint public trace;
    constructor() { trace = trace * 10 + 1; }
}
contract D2 is A2 {
    uint public y = setY();
    function setY() internal returns (uint) { trace = trace * 10 + 9; return 0; }
    constructor() { trace = trace * 10 + 2; }
}
// deploy D2, read trace
```

**solc (legacy / corpus default)**: `trace == 912` (verified: `forge test`).
`ContractCompiler::appendInitAndConstructorCode` runs `initializeStateVariables`
for **all** contracts (base→derived) *before* any constructor body
(`ContractCompiler.cpp:155-160`). So D2's `y = setY()` (which touches `trace`)
runs before A2's constructor body: inits give `trace=9`, then A2 body `→91`,
then D2 body `→912`.

**Note on codegen split**: the `--ir` / `--via-ir` path instead interleaves —
each contract's `initStateVariables` runs after the base ctor call but before
its own body (`IRGenerator.cpp:899-907`), giving `trace == 192`. So this item
diverges from the **legacy** codegen only. Because the corpus validates against
the legacy default, it is a real divergence there.

**solidity-lean**: `trace == 192` (matches via-ir, not legacy). Same root as
DIV-CTOR-1: each contract's `initStmts` are emitted inside that contract's
base-first piece (`Interface.lean:19754-19760`), so D2's initializer runs
immediately before D2's body rather than being hoisted ahead of every
constructor body.

**Classification**: wrong-observable vs legacy corpus ground truth.

**Combined root cause**: `ContractDecl.constructorFunctionFromOrders?`
(`Interface.lean:20459-20483`) + `constructorBodyForDeployment?`
(`Interface.lean:19673-19760`). A faithful legacy lowering must (a) hoist all
`initStmts` (base→derived) ahead of every constructor body, and (b) evaluate
base-ctor args in the supplying (derived) contract during descent, not attached
to the callee base's piece.

## Checked, no divergence found

- **Modifier argument eval timing / order** (`modifierApply?`,
  `functionExpandModifiersToCore?`, `Interface.lean:9767-9874`): args are bound
  as prefix statements at the head of each modifier's body block, and modifiers
  nest left-to-right, matching solc (args of modifier k evaluated when its body
  is entered, in declaration order). No divergence.
- **Multiple `_` placeholders**: `Stmt.toCoreReplacingModifierPlaceholder?`
  (`Interface.lean:7573-7681`) recurses through control flow and substitutes the
  inner body at *every* placeholder, so the body runs once per `_`. Matches solc.
- **Zero `_` placeholders**: no substitution occurs, the inner body is dropped,
  modifier body runs alone and named returns keep their defaults. Matches solc.
- **`super.f()` dispatch**: `rewriteSuperCalls` +
  `contextualSuperHelpersFor?` (`Interface.lean:333-476`, `18556-18571`) resolve
  `super` against `afterName?(dispatchOrder, currentContract)`, i.e. the next
  definition after the current contract in the **most-derived** contract's C3
  order — correct dynamic super semantics.
- **C3 linearization** (`dispatchOrderWithFuel?` / `mergeLinearizationsWithFuel?`,
  `Interface.lean:18843-18907`): equivalent to solc `cThreeMerge`
  (`NameAndTypeResolver.cpp:422-497`) including the reversed-direct-bases
  ordering. (Already mined as DL1; re-confirmed equivalent.)

## Not fully audited (no claim)

- **Overload resolution** among same-named functions: solidity-lean keys the
  function table by ABI-canonical signature (`Interface.lean:8046-8118`), which
  disambiguates overloads, but I did not exhaustively verify the
  most-specific-match / implicit-conversion tie-break against
  `TypeChecker`/`overloadedFunctions`. Candidate for a follow-up pass.
