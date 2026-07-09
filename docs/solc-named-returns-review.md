# solc 0.8.35 named-return-values review (solidity-lean)

Search-only divergence hunt on function-level named return values
(`returns (uint x, bool y)`) vs pinned solc 0.8.35 (legacy codegen) + Forge.
No Lean semantics were modified. Scratch fixtures/witnesses used during the
hunt were removed after use.

## Verdict: CLEAN NEGATIVE (no divergences found)

Every named-return behavior tested — value flow (fall-through, bare `return;`,
explicit `return expr` override, branch-dependent mixing), reference-type
defaults, named-return-as-lvalue, shadowing, and the return accept/reject rules
(arity, duplicate-name) — matches solc 0.8.35. Confidence 90%.

Two premises in the mission brief are outdated for 0.8.35 and were themselves
verified against solc (see items 2 and 9); solidity-lean happens to match solc
on the *actual* 0.8.35 behavior, not the stated premise.

## How solidity-lean implements named returns (root code)

- Named returns are declared as ordinary callee-frame locals, each defaulted:
  `FunctionDef.initialFrame?` / `InternalFunction.initialFrame?` append
  `returnDefaultBindings` (`= returns.map BindingDecl.defaultBinding`) after the
  bound params — `Interpreter.lean:9093`, `7754`, `7724`, `7499`.
  `BindingDecl.defaultBinding` uses `decl.ty.defaultValue` (storage-ref returns
  get the uninitialized-storage sentinel) — `Interpreter.lean:7499`.
- Fall-through end (`Result.normal`) collects the named-return locals via
  `collectReturnBindings` (lookup each local, deref, coerce to declared type) —
  `Interpreter.lean:9131`, `7764`.
- Bare `return;` reaching runtime (`Result.returned … []`, empty values) also
  collects the named locals — `Interpreter.lean:9135-9140`.
- `return expr` / `return (a,b)` (non-empty values) uses the *explicit* values
  via `coerceReturnValues` / `coerceReturnBindings`, ignoring the named locals —
  `Interpreter.lean:9141-9144`, `7784`.
- Return accept/reject typing lives in `checkReturnExprs`
  (`TypeCheck.lean:8756`) — arity via `returnArityMismatch`, tuple-length via
  `checkTupleItemValuesContextuallyAssignableToWithStorageRefs`.

## Evidence (solc ground truth + solidity-lean interpreter/typechecker)

Interpreter results obtained by importing scratch `.sol` through
`scripts/solc_ast_to_lean_source.py` (pinned solc AST → Lean source) and running
`CheckedInput.ownCall` witnesses; typecheck rejects via
`TypecheckedInput.checkedSourceUnit … |> Result.isOk`.

| Case | Program (body) | solc 0.8.35 | solidity-lean |
|---|---|---|---|
| #3 explicit overrides named | `returns (uint){ uint x; x=7; return 9; }` | 9 | `word 9` |
| #4 branch mix (true) | `returns (uint x){ if(c){x=1;return x;} else return 2; }` c=true | 1 | `word 1` |
| #4 branch mix (false) | …c=false | 2 | `word 2` |
| #1 fall-through named + unset | `returns (uint a,bool b){ a=3; }` | (3,false) | `[word 3, word 0]` |
| #5 compound-assign lvalue | `returns (uint x){ x=5; x+=2; return x; }` | 7 | `word 7` |
| #5 reference named lvalue | `returns (uint[] memory a){ …a=t; return a; }` | [5,6] | `dynamicArray [5,6]` |
| #7 `uint[] memory` default | `returns (uint[] memory a){ return a; }` | [] (empty) | `dynamicArray []` |
| #7 `bytes memory` default | `returns (bytes memory bb){ return bb; }` | 0x (empty) | `bytes []` |
| #7 `string memory` default | `returns (string memory ss){ return ss; }` | "" (empty) | `bytes []` |
| #7 `S memory` default | `returns (S memory s){ return s; }` (S{uint,bool}) | zero struct | `tuple [word 0, word 0]` |
| #8 named shadows state var | `uint sv; returns (uint sv){ sv=42; return sv; }` | accept → 42 | accept → `word 42` |

Accept/reject rules (both reject / both accept):

| Case | Program | solc | solidity-lean |
|---|---|---|---|
| #2 bare `return;` w/ named return | `returns (uint x){ x=7; return; }` | **reject** (TypeError 6777 "Return arguments required.") | reject (`checkReturnExprs` G5, `TypeCheck.lean:8760-8764`) |
| #9 fall-through w/ unnamed unset | `returns (uint,bool x){ x=true; }` | accept (warning only) | accept |
| #10 tuple in single-return | `returns (uint x){ return (1,2); }` | reject ("Different number of arguments…") | reject (`false`) |
| #10 scalar in two-return | `returns (uint a,uint b){ return 1; }` | reject | reject (`false`) |
| dup named returns | `returns (uint x,uint x){…}` | reject ("Identifier already declared.") | reject (`false`) |
| #8 named == param name | `f(uint x) returns (uint x){…}` | reject ("Identifier already declared.") | reject (`false`) |

## Notes on outdated mission premises (verified against solc, not divergences)

- **Item #2 premise is wrong for 0.8.35.** A bare `return;` in a function with a
  non-empty return-parameter list — *even when every return is named* — is a
  solc **error** ("Return arguments required.", TypeError 6777), not a
  legal "return current named values". solidity-lean rejects it identically via
  the deliberate G5 rule at `TypeCheck.lean:8760-8764`. (The "return current
  values" behavior only applies to *fall-through* off the end, not to an
  explicit bare `return;`.) Confirmed: `solc BareReturn.sol` → error.
- **Item #9 premise is wrong for 0.8.35.** An unnamed return that is never
  assigned does **not** require an explicit `return`; solc only emits a
  *warning* ("Unnamed return variable can remain unassigned…") and the function
  compiles, returning the unnamed slot's default. solidity-lean also accepts.
- Item #4's exact sample `if(c){x=1;return;} else {return 2;}` cannot compile at
  all under 0.8.35 because of the bare `return;` rejection above; the
  branch-mixing was therefore verified with `return x;` in the taken branch.

## Files of interest

- `SolidCore/Solidity/Interpreter.lean:7499` (`defaultBinding`), `:7724`
  (`returnDefaultBindings`), `:7754`/`:9093` (`initialFrame?`), `:7764`
  (`collectReturnBindings`), `:7784` (`coerceReturnBindings`), `:9129-9155`
  (`callBodyResult` — fall-through / bare / explicit dispatch).
- `SolidCore/Solidity/TypeCheck.lean:8756-8828` (`checkReturnExprs` — arity,
  tuple-length, G5 bare-return reject).
