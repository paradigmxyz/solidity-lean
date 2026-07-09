# solc 0.8.35 custom-errors divergence review (solidity-lean)

Scope: user-defined custom errors — declaration, revert-payload encoding, selector
canonicalization, `Foo.selector`, `require(cond, CustomError())`, catch routing,
accept/reject rules. Ground truth: pinned solc 0.8.35 (legacy codegen). SEARCH-ONLY;
no Lean semantics changed.

## Verdict: CLEAN NEGATIVE (no divergences found; confidence 90%)

Every checked construct matches solc 0.8.35. The custom-error selector and argument
encoding reuse the exact same shared code paths as function selectors / `abi.encode`,
which are independently validated by the green Forge replay suite (105/105), and the
OpenZeppelin fixtures under `tests/forge-harness/` exercise custom-error reverts and
`catch` routing byte-for-byte against solc.

## Evidence by point

### 1. Selector canonicalization — CLEAN (confidence 95%)
`ErrorDecl.abiSelector?` (Interface.lean:8246) and `ErrorDecl.toCore`
(Interface.lean:19490-19499) build the signature from `Parameters.abiCanonicalTypes?`
→ `Ty.abiCanonical?` (Interface.lean:8140-8142) — the **same** canonicalizer used for
function selectors — then take `keccak256(sig)[0:4]` via `ABI.selectorFromSignature`.

Confirmed against solc `--asm` (PUSH32 left-aligned constants):
- `EnumErr(E)` → `EnumErr(uint8)` → `0x0f028445` (enum → uint8)
- `UdvtErr(MyId)` (MyId is uint64) → `UdvtErr(uint64)` → `0xb80e918b` (UDVT → underlying)
- `StructErr(S)` → `StructErr((uint256,address))` → `0x1dc70c3a` (struct → tuple)
- `ContractErr(C)` → `ContractErr(address)` → `0xea4d9bfe` (contract → address)
- `Foo(uint)` → `Foo(uint256)` → `0x1176bd96` (uint → uint256) — matches emitted selector
  in `require(x>0, Foo(x))` runtime bytecode.

### 2 / 8. Argument ABI encoding — CLEAN (confidence 90%)
`Contract.encodeRevertData?` (ABI.lean:574-577) for `RevertData.custom name values`
does `findErrorDecl?` then `encodeSelector decl.selector ++ encodeValues? decl.fields
values`. `encodeValues?` is the same head/tail encoder as `abi.encode`; `decl.fields`
are the actual declared (non-canonical) types, which is correct for encoding.
Dynamic/struct/nested-array/UDVT/enum args therefore encode identically to `abi.encode`.
solc `--asm` confirms `Dyn(bytes,uint256[],string)` → `0x5c9219c2`. OZ fixtures exercise
dynamic-arg custom errors in the green replay suite.

### 3. `revert Foo(...)` vs `revert("str")` vs `revert()` — CLEAN
Interpreter routes: `Stmt.revert name exprs` → `RevertData.custom` (Interpreter.lean:8913-8917);
`Stmt.revertError (some msg)` → `RevertData.error` → selector `0x08c379a0` + `abi.encode(string)`
(ABI.lean:570-573); `Stmt.revertError none` → `RevertData.empty` → empty bytes
(ABI.lean:565). All three payloads match.

### 4. `Foo.selector` — CLEAN
Frontend resolves `Expr.member (Expr.ident name) "selector"` against a `SelectorEnv`
containing error selector entries (`ErrorDecls.selectorEntries`, Interface.lean:8327-8329,
wired at 20288/20295) → `selectorLiteralExpr` of the canonical 4-byte selector
(Interface.lean:8546-8549). Typechecker types it `bytesN 4` (TypeCheck.lean:5301-5309).
Equals the revert payload's leading 4 bytes.

### 5. `require(cond, CustomError())` in 0.8.35 — ACCEPTED by both (KEY FINDING)
**solc 0.8.35 ACCEPTS `require(cond, Foo(args))`** (verified: `require(x>0, Foo(x))`
compiles, emits selector `0x1176bd96` = `Foo(uint256)`, revert = `selector ++ abi.encode(x)`).
solidity-lean also accepts and matches:
- Frontend lowers `require(cond, Name(args))` to `Stmt.requireCustom` (Interface.lean:6275-6281,
  13459-13483), disambiguating via function-env lookup: if `Name` resolves as an
  internal/free function returning a value it becomes `requireErrorExpr` (Error string
  overload), otherwise `requireCustom` (custom error). Because a function and an error
  cannot share a name in solc, this routing is unambiguous.
- Interpreter `Stmt.requireCustom` (Interpreter.lean:8507-8524): on falsy cond →
  `RevertData.custom name args` — same payload as `if(!cond) revert Foo();`.
- Typecheck `checkStmt` (TypeCheck.lean:9372-9395): tries `checkCustomErrorArgs`; if the
  name is not a declared error it falls back to the string-overload check, so
  `require(cond, fnReturningString())` (also solc-accepted, verified) is NOT over-rejected.

Note: no dedicated `require(cond, CustomError())` fixture exists in `tests/`; the accept
path and payload are established by code inspection here, not by an existing replay case.
(This is the main residual-uncertainty item and the reason confidence is 90%, not higher.)

### 6. Catching a custom error — CLEAN
`revertClassify` (Interpreter.lean:7592-7607) classifies as `errorString` only if the
selector equals `0x08c379a0` (and ≥68 bytes, decodable) and `panic` only for `0x4e487b71`
(≥36 bytes); any other selector — including a custom-error selector — is `lowLevel`,
routing to `catch (bytes memory)` / `catch {}` with `data = selector ++ args`. Matches solc.

### 7. No-arg custom error — CLEAN
`encodeValues? decl.fields values` with empty fields = `[]`, so payload = 4-byte selector
only. Confirmed `NoArg()` → `0x141eb202` (exactly 4 bytes). OZ fixtures include many no-arg
errors in the green suite.

### 9. Accept/reject rules — CLEAN
`checkCustomErrorArgs` (TypeCheck.lean:8257-8291) rejects `revert E(...)` when `E` is a
local variable or a contract-level non-error member shadowing a free error (solc TypeError
1885), and rejects unknown names / wrong arity / wrong arg types via `ErrorSigs.resolveChecked`.
Parse-level rejects (error declared inside a function body) never reach solidity-lean:
the Python AST frontend (`scripts/solc_ast_to_lean_source.py`) consumes solc's already
type-checked AST, so any solc-rejected program is excluded upstream.

## Notes / limitations
- The Python frontend drops `referencedDeclaration`/`errorSelector` metadata
  (`METADATA_SCALAR_FIELD_SUFFIXES`), so the Lean frontend disambiguates custom-error vs
  function calls structurally + by function-env lookup rather than by solc's resolved
  reference. Verified sound for the common cases (see point 5); an exotic reason source
  (e.g. a public-getter or function-typed state variable returning `string` used as the
  require reason) was not exhaustively exercised — low risk.
- Findings for points 1–4, 6–9 are backed by shared, replay-validated code paths plus
  direct solc `--asm`/bytecode selector confirmation. Point 5 (require-with-custom-error)
  is code-inspection only for solidity-lean (no fixture); solc-side acceptance is verified.
