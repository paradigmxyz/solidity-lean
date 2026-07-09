# solc memory-allocation / complex-memory-type review

Adversarial review (Fable), 2026-07-09. Scope: allocation / initialization /
layout / copy of complex memory objects and their observable values, vs pinned
solc 0.8.35 (LEGACY codegen, ABI coder v2). Method: read solc source
(`YulUtilFunctions.cpp`, `CompilerUtils.cpp`) + language spec "Layout in
Memory"; get solc ground truth via Forge (pinned 0.8.35, `evm_version=prague`,
`optimizer=false`); drive solidity-lean via the solc-AST importer
(`scripts/solc_ast_to_lean_source.py`) + `CheckedInput.ownCall` and inspect the
returned `Value` list. All probe sources/tests are under the scratchpad, not the
repo corpus (no fixtures/tests/semantics were modified).

Bottom line: the **allocation / init / copy / aliasing** surface is clean — 23
value/length/aliasing probes across `new T[](n)`, multi-dim arrays, memory
structs, storage→memory deep copy, packed-array copy, array literals, and
`abi.decode`-into-memory all matched solc exactly. One **real executable-layer
over-reject** was found and precisely localized: solidity-lean refuses to
*execute* (raises `TypeError.unsupported`) a class of solc-valid programs that
read a `string`/`bytes` element of a memory (or calldata) dynamic array and feed
it to a `bytes(...)`/`string(...)` conversion or `abi.encode*`. It is
**fail-closed** (never a wrong value), so it is a coverage gap, not a soundness
bug.

---

## D-MEM-1 (confirmed) — `bytes(...)`/`string(...)`/`abi.encode*` of a memory `string[]`/`bytes[]` element is rejected at core lowering

**Severity: medium-low** (fail-closed over-reject; typechecker accepts, executor
refuses; no silent wrong value). **Confidence: high** (exact source + Forge +
Lean evidence; mechanism traced end-to-end).

### Minimal repro

```solidity
function f() external pure returns (uint256) {
    string[] memory s = new string[](1);
    s[0] = "hi";
    return bytes(s[0]).length;   // solc: 2
}
```

Other members of the same family (all solc-valid, all rejected by
solidity-lean):

| pattern (element of a memory `string[]`/`bytes[]`)                | solc | solidity-lean |
|------------------------------------------------------------------|------|---------------|
| `bytes(s[0]).length` (s: `string[]` or `bytes[]`)                | runs | `unsupported` |
| `bytes(s[0]).length == 0`                                        | runs | `unsupported` |
| `keccak256(bytes(s[0]))` (s: `string[]`)                         | runs | `unsupported` |
| `abi.encode(s[0])` / `abi.encodePacked(s[0])` (s: `string[]`)   | runs | `unsupported` |
| `bytes1(s[0])`, `return s[0]` directly                          | runs | **runs** (OK) |

Boundary (what still works, sharpening the trigger):
- **Value-type** element conversions are fine: `uint256(u8arr[i])`,
  `uint8(u256arr[i])`, `bytes1(bytesArr[i])` all lower and run.
- The identity read `return s[0];` and `bytes[]`-element `keccak256(s[0])` /
  `abi.encodePacked(bytesArr[i])` (no conversion, bytes source) are fine.
- **Workaround the model accepts**: bind the element to a local first —
  `string memory x = s[0]; return bytes(x).length;` — lowers and runs.
  So the gap is specifically the *inline* use of an indexed `string`/`bytes`
  element as a `bytes`/`string` value.

### solc behavior + evidence

solc compiles and executes every row. Forge (pinned 0.8.35) on the exact
patterns, e.g. `new string[](2); s[0]="hi";` then `bytes(s[0]).length` and
`bytes(s[1]).length` returns `(2, 0)`; `abi.encodePacked`/`abi.encode` of a
string element return the tightly-packed / ABI-encoded bytes. Reference: solc
treats `bytes(str)`/`string(bytes)` as a pure pointer reinterpretation
(`arrayConversionFunction`, identity `converted := value`) and an array element
read as pointer arithmetic; nothing about the element being indexed vs. named
changes codegen.

### solidity-lean behavior + exact location

`CheckedInput.ownCall … "f"` returns
`Except.error (TypeError.unsupported "checked executable checked contract One")`
— i.e. the source→core translation
`SourceUnit.toCoreContract?` / `ContractDecl.toCoreFromOrders?` returns `none`.
The program **typechecks** (`TypecheckedInput.checkedSourceUnit` = ok); only the
executable lowering fails.

Traced mechanism (all verified by `#eval`):

1. `FunctionDecl.toCore?` runs `Stmt.annotateAbi env body`
   (`SolidCore/Solidity/Interface.lean:17906`). For a `bytes`/`string` element
   read, `annotateAbi` inserts an ABI-cleanup conversion wrapper, rewriting
   `bytes(s[0])` into `bytes(bytes(s[0]))` (confirmed:
   `Expr.annotateAbiFuel`, `Interface.lean:7316`).

2. The subsequent `Expr.toCore?` (`Interface.lean:4011`) then sees the wrapped
   operand. Its dynamic-target (`Ty.bytes`/`Ty.string`) conversion handling only
   accepts a **bare-identifier-indexed** operand
   (`Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.index (Expr.ident name) index)]`,
   arm at `Interface.lean:4102-4113`) or, in the general fallthrough
   (`Interface.lean:4161-4193`), a bare `Expr.ident` / literal / `T(bareIdent)`.
   A `bytes(bytes(arr[i]))` (operand = a conversion *call*, not a bare
   ident/index) matches none of these and falls into the sink
   `| _ => do let sourceTy ← Expr.abiTy? …; match sourceTy with | _ => none`
   (`Interface.lean:4190-4193`), returning `none`.

Because isolated `Expr.toCore?`/`Stmt.listToCore?` on the *un-annotated*
`bytes(s[0])` succeed (arm 4102 matches), the failure only appears after the
`annotateAbi` wrapping in the full function pipeline — which is why it evaded
the un-annotated statement translators.

### Classification
Executable-layer **over-reject / incompleteness** (under-accept vs solc). Not a
value divergence: it is fail-closed. Realistic triggers (hashing/encoding/empty
-checking an element of a `string[]`/`bytes[]`, e.g. `keccak256(bytes(names[i]))`,
`bytes(items[i]).length == 0`) make it a plausible coverage gap.

### Suggested fix shape (not applied — review only)
Either (a) have `Expr.toCore?`'s `Ty.bytes|Ty.string` conversion arms accept a
general index/member operand (recurse via `Expr.toCore?` when
`sourceTy ∈ {bytes,string}`), replacing the `| _ => none` sink at 4190-4193; or
(b) have `annotateAbi` not wrap (or wrap in a toCore-recognized form) reads of
`bytes`/`string` dynamic-array elements. Option (a) also covers nested
`s[i][j]` and member reads.

---

## Clean negatives (verified matching solc exactly)

Each probe: solc value via Forge, solidity-lean value via
`CheckedInput.ownCall` returned `Value` list. All identical.

### Allocation / zero-init
- `new uint256[](4)` → length 4, all elements 0, indexed write/read correct.
- `new bytes(5)` → length 5, bytes zero-initialized (`b[3] == 0x00`).
- `new bytes[](3)` → outer length 3, each inner `.length == 0`.
- `new string[](2)`; set `s[0]="hi"` → lengths `(2, 2, 0)` (the *read* is fine;
  only the `bytes(...)`-conversion of the element trips D-MEM-1).
- `new uint256[][](3)`; `o[0]=new uint256[](2); o[0][1]=7` → `(2, 7, 0)` — inner
  siblings independent (matches solc's fresh-per-slot zero init).
- `new uint256[2][](3)` (dynamic outer, static inner) → `(3, 8, 0)`.
- `new P[](2)` for `struct P{uint128 a,b;}` → each struct zero-init, per-slot
  independent `(2, 5, 0, 0)`.

### Layout / literals
- Array literal `[uint8(1),2,255]` → `uint8[3]`, values `(1,255)`.
- Widening literal `[uint256(1),2,3]` → `(1,3)`.
- Nested static literal `[[uint256(1),2],[uint256(3),4]]` → `uint256[2][2]`,
  `(m[0][0],m[1][1],m[0][1]) = (1,4,2)`.

### Copy semantics (storage→memory deep copy independence)
- Packed `uint8[]` storage → `uint8[] memory`, mutate memory → source unchanged:
  `(255,99,42 | s[1]=1)`. Each element lands in its own word.
- Signed packed `int8[]` storage → `int8[] memory`: sign-extended `(-1,-128)`.
- Fixed packed `uint8[3]` storage → memory: `(10,99 | s[1]=20)`.
- Struct `S{uint,uint}` storage → memory, mutate → source unchanged `(99,10)`.
- Nested struct `Outer{uint x; Inner inner; uint8[3] fixedArr}` storage → memory,
  deep copy: `(x=5, m.inner.a=88, s.inner.a=1, m.fixedArr[2]=9)`.
- Array-of-struct `Inner[]` storage → memory: `(m[0].a=55, s[0].a=1, m[1].b=4)`.
- `WithDyn{uint; uint[]}` element storage → memory (dynamic member deep-copied):
  `(m.d[0]=77, s.d[0]=9, m.d.length=1... )` all independent.

### Aliasing (memory→memory by reference — cross-check, already mined M1–M5)
- Outer `uint256[] memory b = a` alias, `b[0]=42` → `(a[0],b[0])=(42,42)`.
- `S memory b = a` alias, `b.a=9` → `(a.a,b.a)=(9,9)`.
- `o[0]=inner; o[1]=inner; o[0][0]=5` → `(5,5)` (shared inner).

### delete / uninitialized
- `delete m;` on `uint256[] memory` → length 0.
- `delete w.x;` on a memory struct field → `(0, w.d.length=0)`.
- Uninitialized `WithDyn memory w;` → `(w.x=0, w.d.length=0)` (dynamic member
  reads as empty).

### abi.decode into memory (nested dynamic)
- `abi.decode(data, (uint256[][]))` for `[[7],[8,9]]` → materialized memory
  yields `(a.length=2, a[0].length=1, a[1][0]=8)`, matching solc. (The
  memory-materialization *shape* is correct here; distinct from the already-mined
  D1 calldata-decode-laziness finding.)

---

## Notes / non-findings

- The `arrayAllocationSizeFunction` bound (`Panic(0x41)` on
  `length > 2^64-1`) is modeled at `Context.checkMemoryAllocation`
  (`Interpreter.lean:1697`) exactly as solc
  (`YulUtilFunctions.cpp:2370`). Not re-probed here.
- Memory arrays are stored inline as `Value.dynamicArray`/`Value.fixedArray`/
  `Value.tuple` trees and materialized into the `memoryRef` heap on
  declaration/assignment, giving solc's array-of-pointers aliasing (design doc
  `docs/memory-layer-design.md`). Confirmed observationally by the aliasing
  probes.
- A harness-frontend (non-semantic) artifact: the AST importer renders a
  contract-local struct used only as `new S[]` with an unqualified
  `Ty.user ["S"]` in the `new` expression while the struct registers as
  `["Contract","S"]`, so such a contract fails to import (typechecker reports a
  name mismatch). This is a `scripts/solc_ast_to_lean_source.py` limitation, not
  a semantics divergence; noted so it isn't mistaken for one.
