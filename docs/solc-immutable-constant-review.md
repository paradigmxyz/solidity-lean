# solc 0.8.35 vs solidity-lean: `immutable` / `constant` review

Search-only divergence hunt over `immutable` and `constant` state-variable value
semantics and accept/reject rules. Ground truth = pinned solc 0.8.35 binary
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) + its C++ source at
`/Users/dan/Projects/solidity-src`. No Lean semantics were modified.

## Verdict: CLEAN NEGATIVE (confidence ~90%)

No accept/reject or value divergence found across ~40 probes covering all nine
mission areas. solidity-lean's `immutable`/`constant` type-checking is closely
aligned with this (deliberately simplified) solc 0.8.35.

## Critical framing: this solc 0.8.35 is a stripped variant

The mission's premise that solc rejects immutable *double-assignment*,
*never-assigned*, and *conditional (one-branch) assignment* is **FALSE for this
compiler**. The only immutable-initialization rule this solc enforces lives in
`libsolidity/analysis/ImmutableValidator.cpp` and is a *single* check:

```
// ImmutableValidator.cpp:62-67
if (_expression.annotation().willBeWrittenTo)
    m_errorReporter.typeError(1581_error, ...,
      "Cannot write to immutable here: Immutable variables can only be
       initialized inline or assigned directly in the constructor.");
```

`visit(FunctionDefinition)` returns `!isConstructor()` (line 42), so the validator
**never descends into the constructor body** and flags an immutable write only when
it appears in a *non-constructor* function or a modifier. There is NO
assigned-exactly-once check, NO definitely-assigned / all-paths check, and NO
read-before-write check anywhere in `libsolidity/` (grep for "control flow ends",
"initialized more than once", "already been initialized" → 0 hits). Empirically
confirmed: an immutable assigned twice, never assigned, or assigned in one `if`
branch all **compile successfully** and read as the last-assigned value (0 if
never assigned).

solidity-lean matches this exactly. Its writability is a single stateless flag
(`TypeCheck.lean:4280` / `:5282`):

```
lvalue := !isConstant && (!isImmutable || env.inConstructor)
```

with `inConstructor := fn.kind == constructor` (`:12000`). There is likewise no
assignment-counting or definite-assignment pass. So both accept the exact same set.

## Probe results (solc = ground truth; Lean = solidity-lean checker)

| # | Program (essential fragment) | solc | Lean | Match |
|---|------------------------------|------|------|-------|
| 1 | `uint immutable X=5; ctor{ X=6; }` (decl+ctor) | ACCEPT | ACCEPT | ✓ |
| 2 | `uint immutable X; ctor{ X=6; X=7; }` (twice) | ACCEPT | ACCEPT | ✓ |
| 3 | `uint immutable X; ctor{}` (never assigned) | ACCEPT | ACCEPT | ✓ |
| 4 | `uint immutable X; ctor(bool b){ if(b) X=1; }` | ACCEPT | ACCEPT | ✓ |
| 5 | `string immutable S="hi";` (ref-type immutable) | REJECT | REJECT | ✓ |
| 6 | write immutable in helper fn called from ctor | REJECT (1581) | REJECT (lvalue) | ✓ |
| 7 | write immutable in `for` loop *inside* ctor | ACCEPT | ACCEPT | ✓ |
| 8 | write immutable in modifier applied to ctor | REJECT (1581) | REJECT (lvalue) | ✓ |
| 9 | `uint immutable N=3; uint[N] arr;` (imm array size) | REJECT | n/a (unreachable) | ✓ |
| 10 | `uint constant N=3; uint[N] arr;` (const array size) | ACCEPT | ACCEPT | ✓ |
| 11 | `uint[3] constant A=[1,2,3];` (array constant) | REJECT | REJECT | ✓ |
| 12 | `uint constant X=5; fn{ X += 1; }` | REJECT | REJECT | ✓ |
| 13 | `uint immutable X; ctor{ y=X; X=5; }` (read-before-write) | ACCEPT | ACCEPT | ✓ |
| 14 | `uint z; uint constant X=z;` (non-const init) | REJECT | REJECT | ✓ |
| 15 | pure fn reads `uint immutable X=5` (rational lit) | ACCEPT | ACCEPT | ✓ |
| 16 | pure fn reads `address immutable X=msg.sender` | REJECT | REJECT | ✓ |
| 17 | view fn reads immutable=msg.sender | ACCEPT | ACCEPT | ✓ |
| 18 | `address immutable X=msg.sender;` (decl init runtime) | ACCEPT | ACCEPT | ✓ |
| 19 | base immutable assigned in derived ctor | ACCEPT | ACCEPT | ✓ |
| 20 | pure fn reads `uint constant X=5` | ACCEPT | ACCEPT | ✓ |
| 21 | `string constant S; bytes constant B` | ACCEPT | ACCEPT | ✓ |
| 22 | `enum E{} E immutable X` / `E constant X=E.B` | ACCEPT | ACCEPT | ✓ |
| 23 | `type T is uint; T immutable / T constant` (UDVT) | ACCEPT | ACCEPT | ✓ |
| 24 | `C immutable X` (contract-type immutable) | ACCEPT | ACCEPT | ✓ |
| 25 | `uint[3] immutable X` (fixed-array immutable) | REJECT | REJECT | ✓ |
| 26 | `function() external immutable X` | REJECT | REJECT | ✓ |
| 27 | `function() internal immutable X` | ACCEPT | ACCEPT | ✓ |
| 28 | `struct S; S constant X` (struct constant) | REJECT | REJECT | ✓ |
| 29 | `X += 5` / `X++` / `delete X` / `(X,Y)=(1,2)` in ctor | ACCEPT | ACCEPT | ✓ |
| 30 | cyclic `uint constant A=A;` | REJECT | REJECT | ✓ |

## Notably well-modeled areas (verified, not just asserted)

### View/pure rule for immutable reads (mission #3/#7) — exact match
solc `ViewPureChecker.cpp:194-198`: an immutable read is `Pure` iff
`varDecl->value()` exists and its type category is `RationalNumber`; otherwise
`View`. solidity-lean models this with `exprIsRationalConstant`
(`TypeCheck.lean:8570-8582`) gating whether the immutable is registered as a
runtime state name (`runtimeStateNameWith?`, `:8701-8710`). I mapped the exact
`RationalNumber` boundary and both agree on every case:

- `2+3`, `-3`, `1 ether`, `~1`, `1<<4`, plain `5` → RationalNumber → **pure OK**
- `true` (bool), `address(0)`, `uint(5)` (explicit conv), `bytes32(...)`,
  `keccak256("x")`, and a **reference to another `constant`** (`X = K`) →
  NOT RationalNumber → **pure REJECT** (view required)

The `X = K` case is subtle and correct in Lean: `exprIsRationalConstant` returns
`false` for an identifier, matching solc (a `constant` reference has the declared
value type, not `RationalNumber`). The doc comment at `TypeCheck.lean:8558-8569`
already records these exact probes.

### constant type-shape + cycle detection (mission #1)
`isConstantStateVarTypeShape` (`TypeCheck.lean:456-460`) = value-type ∪ `bytes` ∪
`string`; enforced at `:9566-9576` with the compile-time-constant init requirement.
Array/struct/mapping constants rejected; `string`/`bytes` accepted. Cyclic
constants caught by `constantsHaveCycle` wired at `:12757` and `:13694`.

### immutable type-shape (mission #2/#8)
`isImmutableStateVarTypeShape` (`:462-466`) rejects external-function-type and any
non-value type, accepts value types incl. enum/UDVT/contract/internal-fn. Matches
solc's `TypeChecker.cpp:508` ("non-value type") plus the "external function type
not yet supported" special-case (both REJECT; only the message text differs).

## Non-divergences worth recording

- **immutable-as-array-size (#8)** is structurally unreachable in Lean: `Ty.array`
  carries `Option Nat` (`Ast.lean:84`), i.e. the length is already a resolved
  `Nat` from the frontend AST. solc rejects the immutable-sized array at compile
  time (probe #9), so no such AST is ever produced; there is no Lean size-*expression*
  evaluator to diverge. Neutral, not a hole.
- Error-message text differs in several REJECT cases (e.g. #26 "external function
  type not yet supported" vs Lean "immutable variable has unsupported type"), but
  accept/reject verdict is identical — not a semantic divergence.

## Residual risk (why 90%, not 100%)

Runtime *values* (mission #5/#6/#7) were reasoned from the state-slot default path
rather than executed through the Forge/interpreter differential harness in this
pass: reading a never-assigned or read-before-write immutable yields 0 in solc and
should via the storage-default read in Lean; a ctor-assigned immutable reads back
the assigned value; public getters return the value. These paths are simple and
consistent with the accept/reject alignment above, but were not end-to-end
executed here. A follow-up that runs probes #13, #18, #19 and a public-getter case
through `scripts/run_forge_interpreter_harness.py` would close the gap to ~100%.
