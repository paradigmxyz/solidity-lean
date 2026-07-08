# Deep review of MEMORY semantics (solc 0.8.35 vs Solidus)

Dedicated round-8 review. Scope: the memory model exhaustively — allocation &
free-memory discipline, the **data-location copy/alias matrix**, in-memory
layout, memory array ops, copy primitives, and memory-value passing across the
call boundary. Read-only; the corpus was **not** built or run. solc probes use
the pinned `solc-0.8.35+commit.47b9dedd` and `forge` (concrete, PASS-verified).

Terminology: **Solidus** = our Lean semantics (`SolidCore/Solidity/*`). solc
source is READ-ONLY at `/Users/dan/Projects/solidity-src` (v0.8.35).

---

## Executive summary

Solidus does **not** model memory as a flat byte array with a free-memory
pointer at `0x40`. It uses an **abstract, id-keyed graph**: memory is
`MemoryMap := Std.HashMap Nat Value` (`Interpreter.lean:790`), a `memoryRef` is
a monotonic allocation id (`Value.memoryRef : Nat`, `Interpreter.lean:136`), and
a nested reference-type sub-object inside an aggregate is stored as its own
`memoryRef` cell (`Runtime.memoryStoredValues`, `Interpreter.lean:1151`). This
is a faithful *aliasing* abstraction of solc's "array-of-pointers / struct-of-
pointers" layout, and it sidesteps every byte-level concern (FMP arithmetic,
`Panic(0x41)` overflow, memory expansion, `mcopy` vs identity-precompile,
`copyToMemory` widths) by construction — those are unobservable in an id-keyed
model, so they are **N/A**, not divergences.

The copy/alias matrix is **mostly faithful but has one confirmed soundness hole
(a family of wrong-alias cases)**. The interpreter preserves memory→memory
*pointer aliasing* only for a **restricted set of RHS shapes**; the remaining
shapes silently **deep-copy** where solc aliases.

**NEW findings by reachability + severity:**

| Reachability | SOUNDNESS (wrong-alias) | COMPLETENESS | UNTESTED |
|---|---|---|---|
| DIFFERENTIALLY-LIVE | **1 family (M1)** | 0 | 0 |
| IMPORTER-MASKED | 0 | 0 | 0 |

- **M1 (DIFFERENTIALLY-LIVE, SOUNDNESS, solc CONFIRMED / Solidus INFERRED):**
  memory→memory binding/assignment of a reference type **deep-copies instead of
  aliasing** whenever the RHS is not a plain variable name (for assignment) or a
  plain variable / index (for declaration). solc treats every such
  reference-type assignment as a **pointer copy**; Solidus allocates a fresh,
  independent object, so a later mutation through the new name is **not**
  observed through the source (and vice-versa). Verified on the solc side by six
  passing Forge probes; the Solidus side is traced through the interpreter (not
  executed), hence INFERRED.

Everything else reviewed — fresh-allocation zero-init, storage↔memory deep copy,
calldata→memory copy, `.length`, element/field read-write, delete-clearing of
memory, and `abi.encode` of memory values — reproduces solc faithfully.

---

## The data-location COPY/ALIAS matrix (the headline target)

### solc ground truth (Forge, all PASS on solc 0.8.35)

`src/MemProbe.sol` + `src/MemProbe2.sol` — each returns the observable after a
mutation through the *new* name:

| # | Pattern (b is `uint256[] memory`) | solc observable | solc verdict |
|---|---|---|---|
| a | `b = a;` (`b`,`a` memory locals), then `b[0]=99` | `a[0]==99` | **alias** |
| b | `uint256[] memory b = a;` decl, then `b[0]=77` | `a[0]==77` | **alias** |
| c | `uint256[] memory b = arr[0];` decl, `b[0]=55` | `arr[0][0]==55` | **alias** |
| d | `b = arr[0];` assign, `b[0]=42` | `arr[0][0]==42` | **alias** |
| e | `b = s.inner;` assign, `b[0]=88` | `s.inner[0]==88` | **alias** |
| f | `uint256[] memory b = c ? x : y;` decl, `b[0]=42` | `x[0]==42` | **alias** |
| g | `b = c ? x : y;` assign, `b[0]=42` | `x[0]==42` | **alias** |
| h | `uint256[] memory b = idret(x);` decl, `b[0]=42` | `x[0]==42` | **alias** |
| — | `uint256[] memory m = storageVar;`, `m[0]=100` | `sv[0]==7`, `m[0]==100` | **deep copy** |
| — | `new uint256[](3)` reads back | all `0` | zero-init |

solc codegen: for a memory reference-type LValue the assignment simply
`storeValue`s the RHS *pointer* into the local's stack slot
(`libsolidity/codegen/ExpressionCompiler.cpp:303-333`, `visit(Assignment)` →
`m_currentLValue->storeValue`, where a `MemoryItem` holds the memory offset);
the memory→memory `convertType` is a no-op. Every reference-type memory
assignment is therefore a pointer copy — cases a–h all alias.

### Solidus behaviour (traced)

Memory objects are id-keyed; a binding holds `Value.memoryRef id`. Aliasing is
preserved only where the interpreter explicitly threads the *ref* rather than
the *deref'd value*. Two narrow entry points do this; everything else falls to a
deep-copying default.

**Declaration** `T memory b = RHS` → `Stmt.memoryVarDecl`
(`Interpreter.lean:7605`) first calls `Expr.memoryRefOrValueWithRuntimeOrder`,
which returns a ref id only for **`Expr.var`** (a memory local) and
**`Expr.index`** (an aggregate element / struct field — struct members are
lowered to `Expr.index`, `Interface.lean:1618-1625`)
(`Interpreter.lean:6689-6721`). On a ref id it binds `Value.memoryRef id`
directly (alias). Any other RHS falls to `Runtime.declareMemoryLocal`
(`Interpreter.lean:1298-1303`), which `memoryStoredValue`s + `allocMemory`s a
**fresh** cell → deep copy.

**Assignment** `b = RHS` → `Stmt.assign` (`Interpreter.lean:7717`) special-cases
**only** `LValue.var name, Expr.var source` (both memory refs) →
`assignLocalRaw? (Value.memoryRef sourceId)` (alias, `Interpreter.lean:7743-`).
Every other RHS goes through the general path: plain eval derefs the value
(`Expr.var` derefs one level, `Interpreter.lean:6010`; `Expr.index` derefs the
element, `Interpreter.lean:6588`), then `assignLocal?` sees a memory *object*
and `memoryStoredValue`+`allocMemory`s a **fresh** cell
(`Interpreter.lean:1249-1253`) → deep copy.

### Resulting matrix (Solidus vs solc)

| Pattern | RHS shape | Solidus path | Solidus result | solc | Divergent? |
|---|---|---|---|---|---|
| decl `T memory b = a` | `var` | memoryVarDecl→ref | alias | alias | ok |
| decl `= arr[i]` / `= s.field` | `index` | memoryVarDecl→ref | alias | alias | ok |
| decl `= c ? x : y` | `conditional` | declareMemoryLocal | **deep copy** | alias | **M1** |
| decl `= f(x)` | `call` | declareMemoryLocal | **deep copy** | alias | **M1** |
| assign `b = a` | `var` | var=var special | alias | alias | ok |
| assign `b = arr[i]` / `= s.field` | `index` | general/assignLocal? | **deep copy** | alias | **M1** |
| assign `b = c ? x : y` | `conditional` | general/assignLocal? | **deep copy** | alias | **M1** |
| assign `b = f(x)` | `call` | general/assignLocal? | **deep copy** | alias | **M1** |
| `T memory m = storageVar` | storage read | declareMemoryLocal | deep copy | deep copy | ok |
| `storageVar = m` | — | store-with-clear | deep copy | deep copy | ok |
| `T memory m = calldataArg` | calldata | declareMemoryLocal | deep copy | deep copy | ok |

The `var`/`index` alias cases and both storage↔memory deep-copy directions match
solc. The divergent cells are exactly the **non-trivial memory-ref RHS** shapes.

Note the subtle asymmetry Solidus exhibits: `T memory b = s.field` (declaration)
aliases correctly (member → `Expr.index` → handled), but `b = s.field`
(assignment to an already-declared pointer) deep-copies — the assignment path
only whitelists `var = var`, not `var = index`.

### Why M1 is a genuine wrong-VALUE bug, not a benign copy

In solc, after case (d) `b = arr[0]; b[0]=42;`, `arr[0][0]` **is** 42 (aliased).
Solidus binds `b` to a fresh cell, so `arr[0][0]` stays 1 and `b[0]` is 42 — the
two names disagree with solc on both. This is observable through any subsequent
read of the source aggregate (return it, hash it, branch on it). It is a
**soundness / wrong-alias** divergence.

### Reachability / classification

- **DIFFERENTIALLY-LIVE:** the importer emits the offending statements verbatim
  — `Assignment` lowers to a plain `Expr.assign lhs op rhs` with **no**
  memory-aliasing rewrite (`scripts/solc_ast_to_lean_source.py:1241-1251`;
  `Interface.lean:4401-4404` → `Stmt.assign target rhsCore`,
  `Interface.lean:5739`), so nothing masks it. solc compiles and runs all of
  a–h; Solidus mis-values d–h and the two `conditional`/`call` declarations.
- **Confidence:** solc side **CONFIRMED** (6/6 Forge probes PASS: cases d, e, f,
  g, h plus the control aliases a, b, c). Solidus side **INFERRED** — traced
  through `Stmt.assign`/`memoryVarDecl`/`assignLocal?`/`declareMemoryLocal` but
  not executed (per instructions, the corpus was not built/run).
- **Severity:** SOUNDNESS (wrong-alias → wrong-value).
- **Currently latent:** the pattern requires reassigning/redeclaring a memory
  reference pointer *from a non-variable memory-ref expression* and then
  observing the source. It is legal, common-enough Solidity (e.g. picking a row
  out of a 2-D memory array, or `b = cond ? bufA : bufB;`), but may not be in
  the present corpus — so this is a **latent** soundness bug, not necessarily a
  currently-failing replay.

**Suggested fix direction (not applied):** extend the ref-preserving pre-check
to `Expr.conditional` and memory-returning `Expr.call` in
`memoryRefOrValueWithRuntimeOrder`, and widen the `Stmt.assign` alias case from
`var = var` to `var = <any memory-ref-valued expr>` (i.e. reuse
`memoryRefOrValue` on the assignment RHS, symmetric with the declaration path).
Passing arguments to internal functions is the same question (below) and should
share the fix.

---

## Other memory surfaces (reviewed — faithful)

- **Allocation & zero-init.** `Ty.defaultValue` (`Interpreter.lean:140-154`)
  builds structural zeros (`word 0`, empty `dynamicArray`, replicated defaults);
  `new uint[](n)` reads back all zeros, matching solc's
  `allocateAndInitializeMemory`. The byte-level FMP/`0x40` discipline, memory
  expansion, and the `Panic(0x41)` allocation-overflow bound are **unobservable**
  in the id-keyed model (there is no address arithmetic to overflow), so they
  are N/A. `RevertData.memoryAllocationTooLarge` exists
  (`Interpreter.lean:299`) for the size-driven revert where solc *would* panic.
- **storage↔memory independence.** Storage reads go through
  `storageMaterializedValue`/`derefMemoryValueDeep` (`Interpreter.lean:1131`,
  fully materialize, no shared ids), then a fresh `declareMemoryLocal`. Forge
  confirms independence (`sv[0]==7` after `m[0]=100`). Faithful in both
  directions.
- **In-memory layout / `abi.encode`.** ABI encoding is value-structural
  (`ABI.lean`) over the materialized aggregate, so `abi.encode`,
  `abi.encodePacked`, and `keccak256(abi.encode(...))` of a memory value depend
  on the *value*, not on a byte offset. Aggregate shape (length + elements,
  array-of-pointers) is represented by the value tree, so these match solc
  byte-for-byte for the values Solidus produces. (Not re-derived byte-by-byte
  this round — covered in prior codec rounds.)
- **`.length`, element/field access.** `Value.length?`
  (`Interpreter.lean:202-214`) returns the element count for `bytes`/arrays/
  tuples; index/member reads deref through the ref graph
  (`Interpreter.lean:6567-6601`). Memory dynamic arrays are fixed-length after
  allocation and there is no `memArr.push()` — solc **rejects** that at compile
  time (TypeError), so the importer never sees it → IMPORTER-MASKED / N/A.
- **Delete-clearing.** `ResolvedLValue.delete` on a memory local resets to
  `defaultLike` through the ref (`Interpreter.lean:5745-5768`), matching solc's
  memory zeroing.
- **Copy primitives / `mcopy`.** `mcopy` (Cancun, 0.8.25+) *is* emitted by solc
  0.8.35 at the bytecode level, but it is a pure byte-move with no
  value-observable effect distinct from the identity-precompile copy; the
  id-keyed model has no byte buffer to move, so this is N/A.

---

## Memory-value passing across the call boundary

Internal-call argument/return of memory refs was substantially built by the
refs-completion arc (`docs/refs-completion-solc-research.md`). Aliasing of a
memory pointer *passed as an argument* shares M1's root cause: whether the
callee's parameter aliases the caller's object depends on the same
ref-vs-deref decision. Passing a plain memory local aliases; passing
`arr[i]` / `s.field` / a ternary as the argument is the same family and is the
place to re-verify once M1 is addressed. Not separately probed this round;
flagged as **same-root-cause, UNTESTED** rather than a distinct finding.

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round:**

- [x] Memory model shape (id-keyed graph, `memoryRef`, `MemoryMap`)
- [x] Allocation + zero-init of `new T[](n)` / default values
- [x] **Copy/alias matrix: memory→memory (var/index/member/ternary/call)** ← M1
- [x] storage→memory deep copy (independence, Forge-confirmed)
- [x] memory→storage deep copy (store-with-clear path)
- [x] calldata→memory copy
- [x] `.length` / element / struct-member read + write
- [x] delete-clearing of memory locals
- [x] `.push()` on memory (solc-rejected → masked)
- [x] Layout dependence of `abi.encode`/`keccak256` (value-structural → faithful)
- [x] Importer: `Assignment` lowering carries no aliasing rewrite

**Still not reached / deferred (honest gaps):**

- [ ] Byte-exact `abi.encode` of *nested* memory aggregates re-derived against
  solc this round (relied on prior codec-round conclusions).
- [ ] Tuple-destructuring assignment/declaration of multiple memory refs
  (`(uint[] memory a, uint[] memory b) = f();`) — likely the same M1 family via
  `assignTuple`/`writeTupleWithRuntime`, not individually probed.
- [ ] Concrete execution of M1 on the Solidus side (INFERRED, not run — corpus
  build/run out of scope).
- [ ] Memory-argument aliasing across the internal boundary re-probed post-fix.

---

## Cross-reference to prior rounds

- Rounds 1–7 (`docs/solc-implementation-divergences{,-2..7}.md`,
  `docs/solidus-solc-deep-comparison.md`) covered arithmetic/ABI-codec,
  analysis-pass acceptance, value-producing codegen, storage packing/slots/
  mutators, and (round 7) runtime behavior. **None** touched the memory
  copy/alias matrix — M1 is **NEW**.
- IN-FLIGHT items (V1 slice OOB, A1 abstract interfaceId, enum using-for
  dispatch) and known-stays (G16, CF2 residuals) are unrelated to memory and not
  re-litigated here.
