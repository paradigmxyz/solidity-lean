# Free (file-level) declarations review vs solc 0.8.35

Search-only divergence hunt over free functions and other file-level declarations
in solidity-lean vs pinned solc 0.8.35 (legacy codegen). Single-file only.

Method: each program compiled with pinned solc `--standard-json` (accept/reject),
then imported via `scripts/solc_ast_to_lean_source.py` and executed through the
`CheckedInput.program` → `CheckedContract.callFunctionWithContext` path (the
contest observable helper), comparing return values / revert / accept-reject.

## Headline

**ONE real over-reject found** (high confidence, precisely localized), plus a
broad set of clean positives. The over-reject is a general lowering gap, not
specific to structs: **any free-function call in argument position of another
call over-rejects the whole contract.**

---

## DIVERGENCE 1 — free-function call in argument position → whole-contract over-reject

**Severity: over-reject. Confidence: 97%.**

solc accepts and runs; solidity-lean rejects the entire contract translation with
`TypeError.unsupported "checked executable checked contract C"`.

### Minimal program (no structs needed)

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
function inner(uint a) pure returns (uint) { return a * 2; }
function outer(uint a) pure returns (uint) { return a + 1; }
contract C {
  function run(uint x) public pure returns (uint) { return outer(inner(x)); }
}
```

- **solc**: accepts; `run(5)` returns `11`.
- **solidity-lean**: `solidity-lean-reject … TypeError.unsupported "checked executable checked contract C"` (contract fails to translate at all).

### Exact trigger

The free call must appear **nested inside the argument list of another call**.
The enclosing call may be a free function OR a contract member; the *nested*
callee being free is what triggers it.

| Program (inside `run`)                                    | solc | solidity-lean |
|-----------------------------------------------------------|------|--------|
| `return inner(x);` (free, top-level)                      | ok 10 | ok 10 |
| `return inner(x) + 1;` (free in arithmetic)               | ok 11 | ok 11 |
| `uint y = inner(x); return y+1;` (free at top of initializer) | ok 11 | ok 11 |
| `if (inner(x) > 3) …` / `require(inner(x) > 0);`          | ok    | ok    |
| `return outer(inner(x));` **outer FREE, inner MEMBER**     | ok 11 | ok 11 |
| `return outer(inner(x));` **outer FREE, inner FREE**       | ok 11 | **REJECT** |
| `return outer(inner(x));` **outer MEMBER, inner FREE**     | ok 11 | **REJECT** |
| `return outer(inner(x) + 0);` (free nested, wrapped)      | ok    | **REJECT** |
| `uint y = outer(inner(x)); return y;` (varDecl initializer)| ok    | **REJECT** |
| `sink(inner(x));` (expression statement, `inner` free)    | ok    | **REJECT** |

The original struct end-to-end case (mission #7) —
`function mk(...) returns (P memory)` + `function sum(P memory)` +
`return sum(mk(x, x+10));` — is just an instance of this: `mk` (free) is nested
as the argument to `sum`. Split into a local (`P memory p = mk(...); return sum(p);`)
it works; the struct itself is fine.

### Root cause

**`SolidCore/Solidity/Interface.lean:10186-10197`** —
`FunctionDecl.directOrPtrCallArgReturnTy?` takes only `(functions : List FunctionDecl)`
(contract members) and never a `freeFunctions` list. It resolves a nested call's
return type solely against `functions`:

```
10189   match FunctionDecl.findInternalCalleeWithArgs? functions env name args with
10190   | some (callee, _) => FunctionDecl.singleReturnTy? callee
10191   | none => …            -- only the fn-POINTER branch, never freeFunctions
```

Load-bearing call sites, all passing only `functions` (dropping `freeFunctions`):

- **Interface.lean:14731** — `Stmt.returnValues` nested-arg hoist (`return outer(inner(x))`).
- **Interface.lean:14310** — `Stmt.varDecl` initializer nested-arg hoist.
- **Interface.lean:13526** — `Stmt.expr` expression-statement nested-arg hoist.

`Args.replaceDirectInternalCallArg?` (Interface.lean:10544) detects `inner(x)` in
argument position *syntactically*, regardless of member-vs-free. The very next
gate, `directOrPtrCallArgReturnTy? functions …`, then fails to find a free callee
(returns `none`), so control falls to the `fallback?` branch (≈14774) which tries
to lower `outer([inner(x)])` with the nested free call left unhoisted — a shape no
plain-expression lowering handles → `none` → `toCoreContractFor?` `none` →
`CheckedProgram.contract` raises the `unsupported` error (`Checked.lean:230`).

Sibling helpers in the same family DO thread `freeFunctions` and would fix this if
mirrored: `FunctionDecl.internalCalleeReturnTys?` (Interface.lean:10170-10178,
free fallback at 10176) and `Expr.abiTyWithInternalFunctionsEnv?`
(Interface.lean:10199-10215, free fallback at 10213). Also note the hoist itself
(`internalSingleReturnCallCore? … functions freeFunctions …`, ≈14737) already
threads both lists — only the *return-type gate* that guards it drops the free
list. So `directOrPtrCallArgReturnTy?` is the single member of this family missing
the parameter.

---

## Clean positives (no divergence) — verified value / accept-reject matches

All below: solc and solidity-lean agree (values or shared-frontend reject).

1. **Free function call** — `add(5,3)` → `8`. ok.
2. **Free-function overloading by arity** — `f(uint)`=`x+100`, `f(uint,uint)`=`a+b+200`;
   `f(5)`→105, `f(5,5)`→210. ok.
3. **File-level constants** — `uint constant X=5; uint constant Y=X*3;` → `X`=5, `Y`=15. ok.
   Non-constant initializer `uint constant K = ext();` → solc rejects, importer fails closed. ok.
   **File-level `string constant NAME="hi"`** → `bytes(NAME).length`=2. ok.
4. **File-level struct / enum / UDVT / error used in a contract** —
   `S(a,a+1).x+.y`, `uint(E.C)`=2, `T.unwrap(T.wrap(a))+1`, `revert Err(9)`
   (→ `custom:Err:w:9`). all ok.
5. **`using {freeFn} for T`** (file-level) — `using {dbl} for uint; x.dbl()`→10. ok.
   **`using {freeFn} for <UDT> global`** — `struct Point; function mag(Point); using {mag} for Point global;`
   `p.mag()`→11. ok. (`using {dbl} for uint global` correctly rejected by solc:
   global requires a user-defined type; importer fails closed.)
6. **Forward / out-of-order file-level references** —
   `function early(a){return late(a)+K;} function late(a){return a*2;} uint constant K=7;`
   `early(5)`→17. Forward reference to a later free function AND a later constant both resolve. ok.
7. **Free function taking/returning a file-level struct (non-nested)** —
   `mk` returns `P memory`, read fields → 20; `sum(P memory)` on a local → 20. ok.
   (The *nested* `sum(mk(...))` form is Divergence 1.)
8. **Shadowing** — a contract member `g(uint)` shadows a file-level `g(uint)`:
   `g(x)`→`x+1` (member wins, file-level `+1000` ignored). ok.
   Complementary solc semantics also matched via fail-closed import: when a
   contract member `f(uint)` shadows a file-level `f(uint,uint)` of *different*
   arity, solc resolves the name to the member ONLY and rejects `f(x,x)`
   ("wrong argument count") — the file-level overload is fully hidden, not merged.
   Importer fails closed; consistent.
9. **Free function as a function pointer** — `function(uint) pure returns(uint) fp = inc; fp(5)`→6. ok.
10. **Accept/reject (all shared-frontend consistent; solc rejects, importer fails closed):**
    - `public` on a free function → `SyntaxError: Free functions cannot have visibility.`
    - `virtual` on a free function → `SyntaxError: Free functions cannot be virtual.`
    - `payable` on a free function → `TypeError: Free functions cannot be payable.`
    - free function named `constructor` → `ParserError`.
    - duplicate free function (same name+params) → `DeclarationError: … defined twice.`
    - free function reading a contract state var / `this` → `DeclarationError: Undeclared identifier.`
    - **`msg.sender` in a free function is ACCEPTED by solc** (context, not state);
      solidity-lean runs it and returns the sender correctly. ok. (The mission's
      "free function with msg/state access → reject" holds only for contract
      *state*/`this`, not for `msg`/`block` globals.)

---

## Notes / caveats

- Over-**accept** of the free-function-specific SYNTAX rejects (visibility /
  virtual / payable / duplicate) is not reachable through this harness: those are
  rejected by solc's frontend, so the importer never produces such an AST, and
  solidity-lean's own checker is never exercised on them. They are reported here
  as shared-frontend consistent, not independently verified in the Lean checker.
- Divergence 1 was reproduced across all three arg-hoist statement contexts
  (return, varDecl, expression statement), each matching the missing-parameter
  prediction, which raises confidence it is exactly the `freeFunctions`-dropped
  gate and not an incidental interaction.
