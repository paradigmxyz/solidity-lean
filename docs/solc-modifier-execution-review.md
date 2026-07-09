# solc 0.8.35 vs solidity-lean — Function-Modifier EXECUTION semantics review

Search-only divergence hunt targeting the RUNTIME semantics of function modifiers:
placeholder `_` expansion, chaining/order, arguments, `return` unwinding, and the
type-checker guards around them. Ground truth: pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) + Forge (legacy
codegen: `optimizer=false`, no via-IR). solc C++ at
`/Users/dan/Projects/solidity-src`.

Method: for each construct, a minimal contract was compiled/executed with real
solc+Forge (storage/return observed via events), then the same source was
imported through `scripts/solc_ast_to_lean_source.py` and executed through the
Lean interpreter (`TypeCheck.CheckedInput.ownCall` / `CheckedContract.construct`),
reading storage slots and return values. Type-checker-only cases that solc
rejects at parse/analysis (so the AST importer can't reach them) were reproduced
by hand-built Lean ASTs.

---

## How solidity-lean models modifiers (for reference)

INLINING via placeholder substitution — not a continuation/stack model. The live
path is `functionExpandModifiersToCoreWithInternalCallsFull?`
(`Interface.lean:16528`, wired at `18078` for functions and `19976` for
constructors). It right-folds the invocation list so the leftmost modifier is
outermost; each modifier body is lowered with every `Stmt.modifierPlaceholder`
rewritten (recursively, replace-ALL) to `Stmt.captureReturn returnNames inner`
(`Interface.lean:16225`; pure analogue `toCoreReplacingModifierPlaceholder?` at
`7615`). Modifier arguments become `varDecl` prefixes evaluated once at the
invocation site in the caller's frame (`modifierParamBindingsFrom?`,
`Interface.lean:9809`), params α-renamed to `modifierParamRuntimeName i`.
`Stmt.captureReturn` (`Interpreter.lean:8525`) catches a body `Result.returned`,
writes the values into the named-return variables, and downgrades to
`Result.normal` so post-`_` code runs — this is Solidity's "return jumps to the
modifier continuation."

This model is **correct** across every execution behavior probed below.

---

## FINDING 1 — Over-accept: `return <expr>` inside a modifier body

**Confidence: 99%. Severity: over-accept (type-checker). Real-world impact: low
(unusual syntax), but a genuine, precisely-rooted divergence.**

solc forbids a `return` statement with ANY argument expression inside a modifier
body. solidity-lean accepts it whenever the expression is void-typed (including
the special `delete`/`require` forms), because it type-checks a modifier body
exactly like a zero-return function.

### Programs (all rejected by solc, accepted by Lean)

```solidity
// (a)
contract RD { uint256 public x;
  modifier m() { _; return delete x; }
  function f() public m {} }

// (b)
contract RR2 {
  modifier m() { _; return require(true); }
  function f() public m {} }
```

### solc 0.8.35
Both REJECT:
```
Error: Return arguments not allowed.   (TypeError 7552)
```

### solidity-lean
Both ACCEPT (`TypecheckedInput.checkedSourceUnit` → `Result.ok`):
- `return delete x;` in modifier accepted = **true**
- `return require(true);` in modifier accepted = **true**

(Control cases, correctly matching solc: `return 9;` in a modifier → Lean
**rejects**; a `view` function applying a storage-writing modifier → Lean
**rejects**.)

### Why (root cause)

- **solc** — `TypeChecker::endVisit(Return const&)`,
  `libsolidity/analysis/TypeChecker.cpp:1133`. It reads
  `params = _return.annotation().functionReturnParameters`. A **modifier** has
  **no** return-parameter list, so `params == nullptr`, and any `return` *with*
  an expression hits `if (!params) ... typeError(7552, "Return arguments not
  allowed.")` (lines 1142–1146). A bare `return;` in a modifier is fine
  (`!_return.expression()` with null params returns early, 1136–1141). Crucially
  this is distinct from a **zero-return function**, whose `params` is a *non-null
  but empty* `ParameterList` — there `return delete x;` / `return require(...)`
  are accepted (void tuple, size 0 == 0). Verified: solc ACCEPTS
  `function f() public { return delete x; }` and `return require(true);`.

- **solidity-lean** — the modifier body is checked with `returnTys := []`
  (`ModifierDecl.check`, `TypeCheck.lean:~11999`; `checkBodyForCaller`,
  `~10769`). `checkReturnExprs` (`TypeCheck.lean:8720`) keys solely off
  `env.returnTys`: the `some expr, []` branch (8729–8752) special-cases
  `return require(cond, E(...))` (8731) and `return delete _` (8747) as OK, and
  otherwise accepts any expression whose type is `Ty.tuple []` (void). It never
  consults `env.inModifier` (the flag exists — it is set by `enterModifier` and
  used for the placeholder-presence and `_`-scope checks — but is ignored here).
  So a modifier is treated identically to a zero-return function, collapsing
  solc's null-vs-empty `functionReturnParameters` distinction.

### Suggested fix direction (not applied — search-only)
In `checkReturnExprs`, when `env.inModifier` is true, reject any `some expr`
(mirror solc's null-params branch) regardless of the expression's type.

---

## CLEAN NEGATIVES — every execution behavior matches solc/Forge

All values below are solc+Forge ground truth (left) vs Lean interpreter (right);
storage slots: contract-specific, noted inline. Every pair is identical.

| Construct | solc/Forge | Lean |
|---|---|---|
| **Multiple `_`**: `modifier twice(){ _; _; }` body `log+=1` | log = **2** | 2 |
| Multiple `_` with early `return` in body: `twice` + `f(){ log+=1; return log; }` | ret=**2**, log=**2** | ret=2, log=2 |
| **`_` in `for`**: `modifier thrice(){ for(i<3){ _; } }` body `log+=1` | log = **3** | 3 |
| **`_` in `if`**: `modifier gate(bool c){ if(c){ _; } }` | c=true→log=**1**, c=false→log=**0** | 1 / 0 |
| **Zero `_`** (`modifier none_(){ log=1; }`) | **REJECT** "Modifier body does not contain '_'" | REJECT "modifier body does not contain a placeholder" |
| **Chain order** `f() m1 m2 { push5 }`, m1=1/6, m2=2/3 (base-10 digits) | seq = **12536** | 12536 |
| **Return + named returns + post-code**: `modifier post(){ _; trace=99; }`, `f() post returns(uint r){ r=7; return r; }` | ret=**7**, trace=**99** | ret=7, trace=99 |
| **`return;` in modifier post-code**: `modifier m(){ _; t=1; return; }`, `f() m returns(uint r){ r=7; }` | ret=**7**, t=**1** | ret=7, t=1 |
| **Same modifier twice** `f() m m { log+=1; }`, `modifier m(){ _; }` | log = **1** | 1 |
| **Constructor modifier**: `modifier m(uint x){ t=x; _; t+=100; }`, `constructor() m(5){ t+=1000; }` | t = **1105** | 1105 |
| **Arg evaluated once, in fn scope**: `f() useArg(inc())` (inc side-effects counter) | counter = **1** | 1 |
| **Arg references fn param**: `modifier m(uint x){ t=x; _; }`, `f(uint p) m(p*2){ t+=1; }`, call f(10) | t = **21** | 21 |
| **Arg-eval order across a chain** (interleaved): `f() a(e(1)) b(e(2))` with a/b pre-codes 7/8, body 9 (digits) | ord = **17289** (a.arg,a.pre,b.arg,b.pre,body) | 17289 |
| **`return <uint value>` in modifier** | **REJECT** "Return arguments not allowed" | REJECT (type mismatch vs `tuple []`) |
| **`view` fn + storage-writing modifier** | **REJECT** (state-mutability) | REJECT (mutability violation) |

Type-checker guards additionally confirmed present and solc-faithful:
placeholder-presence (`TypeCheck.lean:11982`), `_` only inside a modifier
(`9438`), applied name must resolve to a modifier (`10742`/`3606`), and effective
state-mutability re-check of the modifier body under the caller function's
mutability (`11945`/`11960`, `enterModifier` preserves `currentMutability`).

---

## Summary

- **1 real divergence (over-accept)**: `return <void-typed expr>` (incl.
  `return delete x;`, `return require(...)`, `return voidCall();`) inside a
  modifier body — solc rejects (TypeError 7552, `functionReturnParameters ==
  nullptr`), solidity-lean accepts (checks the modifier as a zero-return
  function; `checkReturnExprs` at `TypeCheck.lean:8720` ignores `env.inModifier`).
  Confidence 99%, low practical severity.
- **Everything else is a clean negative**: placeholder expansion (multiple/zero/
  loop/conditional), chaining order, argument evaluation (count/scope/order,
  including interleaving across a chain), `return` unwinding with named returns,
  `return;`/post-code in modifiers, constructor modifiers, same-modifier-twice,
  and the state-mutability / placeholder-presence type guards all match solc
  0.8.35 exactly under the executed probes.
