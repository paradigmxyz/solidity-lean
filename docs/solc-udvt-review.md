# solc 0.8.35 vs solidity-lean — User-Defined Value Types (UDVT) review

Scope: the UDVT *type* itself — `type MyInt is uint256;`, `wrap`/`unwrap`, and the
type / ABI / storage rules. User-defined *operators* (`using {f as +} for T`) were
covered by a prior "G1" review and are out of scope except where a finding is
clearly distinct.

Ground truth: pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`), legacy codegen.

## Verdict: CLEAN NEGATIVE (no divergences found), confidence 90%

Every one of the ten audited axes matches solc 0.8.35. Two of the mission's
stated premises (#2 "enum allowed as underlying", #6 "`type(UDVT).min/max`
supported") are in fact *wrong for 0.8.35* — solc rejects both — and solidity-lean
matches solc's actual (rejecting) behaviour.

## How solidity-lean models a UDVT

Two-stage pipeline, verified by reading:

1. **Typecheck stage** runs on the *unresolved* source AST — UDVTs are kept as
   `Ty.user path`, with the underlying recorded in `TypeContext.userValueTypes`
   (`TypeCheck.lean:249-253`, a `path → underlying` map). The checker distinguishes
   a UDVT from its underlying everywhere. `CheckedProgram.fromSource?`
   (`Checked.lean:86-88`) calls the checker (`checkedSourceUnit?`) *first*, then
   applies type resolution — so the checker sees UDVTs intact. UDVT decls survive
   into the checked program (`rawFreeUserValueTypes`, `Checked.lean:133`).
2. **Lowering stage** substitutes each UDVT by its underlying for execution / ABI /
   storage: `Ty.resolveUserTypesFuel` (`Interface.lean:841-863`, recurses through
   array/mapping/tuple/struct/function types), applied program-wide in
   `ContractDecl.toCoreFromOrders?` (`Interface.lean:~20238`) before selectors are
   computed. `wrap`/`unwrap` member-calls are specially preserved through the
   resolver (`Interface.lean:894-921`).

This mirrors solc: a UDVT is a nominally-distinct type at the checker, encoded /
stored / selector-named as its underlying.

## Axis-by-axis evidence

### 1. wrap / unwrap + no-implicit-conversion  — MATCH
`wrap` checks the arg is assignable to the *underlying*
(`TypeCheck.lean:6116` `arg.expectAssignableToIn env.types underlying`), result
type = the UDVT. `unwrap` checks the arg is assignable to the *UDVT*
(`TypeCheck.lean:6128`), result type = underlying. Both callable in the
`T.wrap`/`T.unwrap` and `Lib.T.wrap` member forms (`TypeCheck.lean:6113-6136`,
`6256-6279`).

- `MyInt(x)` direct cast — solc: `Error: Explicit type conversion not allowed from
  "uint256" to "MyInt".` solidity-lean: no cast path exists; UDVT ↔ underlying is
  not in `Ty.canImplicitlyConvert` nor an explicit-conversion target → rejected.
- Bare arithmetic `a + a` on `MyInt` — solc: `Built-in binary operator + cannot be
  applied to types MyInt and MyInt.` solidity-lean: numeric operand predicates
  accept only elementary numerics, not `Ty.user` → rejected.

### 2. Underlying must be an elementary value type — MATCH
`UserValueTypeDecl.check` requires `Ty.isBuiltInValueTypeShape decl.underlying`
(`TypeCheck.lean:12204-12206`); that predicate (`TypeCheck.lean:430-439`) admits
only bool / address / uintN / intN / fixed / ufixed / bytesN — **not** enum, not
contract, not string/array/struct.

solc 0.8.35 confirmations:
- `type T is E;` (enum) → `Error: The underlying type for a user defined value type
  has to be an elementary value type.` (solc **rejects** enum — contradicts the
  mission brief; solidity-lean also rejects → match.)
- `type T is Other;` (contract) → rejected (both).
- `type T is string;` → `Error: The underlying type ... is not a value type.` (both reject).
- `type T is uint256;` / `type A is address payable;` / `type T is fixed128x18;` →
  accepted by solc; `isBuiltInValueTypeShape` accepts each → match.

### 3. ABI / selector uses the underlying's canonical name — MATCH
solc: `function f(MyInt x)` → hash table shows `b3de648b: f(uint256)` (the UDVT name
is invisible; selector == `f(uint256)`). solidity-lean resolves the param type to
`uint256` before selector computation, so the signature string is `f(uint256)`.
`Ty.abiCanonical?` maps a leftover `Ty.user` to `"address"` (`Interface.lean:2495`),
but UDVTs never reach it unresolved — that branch is only hit for *contract* value
types (which are address-encoded). UDVTs nested in tuple/array/struct/mapping are
resolved recursively (`Interface.lean:846-849`).

### 4. Storage packing — MATCH
UDVT storage type is the underlying (state-var type resolved by
`StateVarDecl.resolveUserTypes`, `Interface.lean:991`), so a `type T is uint8` packs
exactly like `uint8`. Narrow-width behaviour is exercised by the passing fixture
`tests/forge-harness/narrow-udvt-arithmetic` (uint8/int8 UDVTs).

### 5. Bare `==` on two UDVTs (no bound operator) — MATCH (distinct from G1)
solc: `Error: Built-in binary operator == cannot be applied to types MyInt and
MyInt. No matching user-defined operator found.` solidity-lean:
`Ty.isEqualityComparable` returns `false` for a `Ty.user` path that is a UDVT
(only contract/enum user-paths are equality-comparable) — `TypeCheck.lean:3471-3486`.
This is the *equality* operator specifically (G1 covered arithmetic operators).

### 6. `type(MyInt).min` / `type(MyInt).max` — MATCH (both reject)
solc 0.8.35: `Error: Invalid type for argument in the function call. An enum type,
contract type or an integer type is required, but type(MyInt) provided.` — solc does
**not** support `type()` on a UDVT (contradicts the mission brief). solidity-lean:
the `type(...).min/max` path handles only raw `Ty.uint`/`Ty.int`
(`TypeCheck.lean:5546-5556`) and enums; for a UDVT `Ty.user` path that is neither
enum nor contract it falls through to
`Except.error (TypeError.unsupported "member min/max")` (`TypeCheck.lean:5614`) →
rejected. Match.

### 7. Default value — MATCH
A UDVT lowers to its underlying, whose default (0 / false / zero-address wrapped) is
used. No separate default-value logic; inherited from the underlying via lowering.

### 8. UDVT as mapping key / array element / event indexed — MATCH
`Ty.resolveUserTypesFuel` recurses into `Ty.array` and `Ty.mapping`
(`Interface.lean:846-847`) and event/param types, so key preprocessing, element
encoding, and indexed-topic encoding all use the underlying. `f(MyInt)`-style
signatures use `uint256` (verified in axis 3).

### 9. wrap/unwrap arg type checking — MATCH
- `Big.wrap(uint8Val)` (Big over uint256): solc accepts (uint8→uint256 implicit);
  solidity-lean `expectAssignableToIn uint256` accepts the widening → match.
- `A.wrap(aVal)` where `aVal:A` (A over uint256): solc rejects `Invalid implicit
  conversion from A to uint256`; solidity-lean checks arg assignable to `uint256`,
  `A` (a `Ty.user`) is not → rejected → match.
- `B.unwrap(aVal)` where `aVal:A`, distinct UDVTs: solc rejects `Invalid implicit
  conversion from A to B`; solidity-lean `unwrap` checks arg assignable to `B`, `A`
  is not → rejected → match. Two UDVTs sharing an underlying are kept distinct;
  `TypeContext.canImplicitlyConvert` only unifies *local aliases of the same* UDVT
  (`TypeCheck.lean:1287-1294`), never distinct UDVTs and never UDVT↔underlying.

### 10. UDVT over bytesN / bool / address — MATCH
`isBuiltInValueTypeShape` accepts bool / address / bytesN / fixedBytes; wrap/unwrap
and lowering are type-agnostic over the underlying. `type A is address payable;`
accepted by both.

## Residual uncertainty (why 90%, not higher)
- Value-level round-trips and storage packing were validated by *reading the
  lowering* plus the existing passing `narrow-udvt-arithmetic` fixture, not by a
  fresh end-to-end `lake` eval of every underlying kind (bytesN / bool / address
  packing, mapping-key preprocessing) built in this session.
- Reject cases could only be confirmed on the solc side (an invalid program has no
  importable AST); the solidity-lean rejects were established by reading the
  checker, which is unambiguous for each case above.

## Key file:line references
- Underlying-type restriction: `TypeCheck.lean:430-439`, `12204-12206`
- wrap/unwrap checking: `TypeCheck.lean:6108-6138`, `6251-6279`
- Bare `==` reject: `TypeCheck.lean:3471-3486`
- `type(UDVT).min/max` reject: `TypeCheck.lean:5546-5616`
- UDVT↔underlying non-convertibility / alias-only unification: `TypeCheck.lean:1281-1299`
- UDVT in TypeContext: `TypeCheck.lean:249-253`
- Checker-before-resolve ordering: `Checked.lean:86-88`
- UDVT → underlying lowering: `Interface.lean:841-863`, `894-921`, `~20238`
- ABI canonical name: `Interface.lean:2443-2497`
