# solc 0.8.35 vs solidity-lean — Struct construction / literals / default-init / copy review

Scope: struct positional & named construction, nested literals, mapping-member
memory-construction reject, dynamic-member literals, default/zero-init, copy
semantics, comparison, recursive-struct accept/reject. Ground truth: pinned
solc 0.8.35 (legacy codegen) + solc C++ source at ../solidity-src.

## VERDICT: CLEAN NEGATIVE (no divergence found). Confidence 90%.

Every candidate I constructed matched solc's accept/reject decision, including
the three the mission flagged as highest-risk (#2 named-arg reorder/completeness,
#4 mapping-member memory-construction reject, #10 recursive-struct boundary).

## Method

- solidity-lean side: built minimal `SourceUnit` ASTs and evaluated
  `TypeCheck.sourceUnitAccepted?` (accept/reject), plus traced the runtime
  construction path in `Interface.lean`.
- solc side: compiled matching `.sol` with the pinned solc-0.8.35 artifact,
  observed the error code / clean compile.

## Results (solidity-lean vs solc — all agree)

| # | Case | solidity-lean | solc 0.8.35 |
|---|------|---------------|-------------|
| 2 | `S({a:1,b:2})` | accept | accept |
| 2 | `S({b:2,a:1})` reorder | accept | accept |
| 2 | `S({a:1})` missing field | reject | reject |
| 2 | `S({a:1,b:2,a:3})` duplicate | reject | reject |
| 2 | `S({a:1,c:2})` unknown name | reject | reject |
| 2 | `S(1,{b:2})` mixed pos+named | reject | reject |
| 1 | `S(1,2)` positional | accept | accept |
| 1 | `S(1)` wrong arity | reject | reject |
| 1 | `S8(300)` field out of range | reject | reject (implicit-conv error) |
| 1 | `S(-1,2)` signed→uint field | reject | reject |
| 5 | `SB(1, hex"aa")` bytes member | accept | accept |
| 6 | `S memory s;` default-init | accept | accept |
| 8 | `s1 == s2` | reject | reject (operator not applicable) |
| 10| `struct X { X x; }` | reject | reject (Recursive struct) |
| 10| `struct A{B b;} struct B{A a;}` mutual | reject | reject (Recursive struct) |
| 10| `struct Node{uint v; Node[] c;}` | accept | accept |
| 4 | `M memory s;` (M has mapping) | reject | reject |
| 4 | `M(1)` / `M(1,2)` ctor of mapping struct | reject | reject (9515) |
| 4 | `Out(1, si)` — nested mapping via storage Inn | reject | reject (9515) |

## Key implementation notes (root-cause references)

- **Named-arg reorder & completeness (#2)** — `CheckedArgInfos.ordered?`
  (`SolidCore/Solidity/TypeCheck.lean:3318`): rejects positional+named mix,
  rejects non-unique names, requires `infos.length == paramNames.length`, and
  `collectNamed?` (line 3309) pulls each param name out of the supplied set so a
  missing field (count matches but a name absent) or an unknown name both fail.
  Struct-specific entry: `checkStructConstructorArgs`
  (`TypeCheck.lean:4714`) feeds `StructDecl.fieldNames`/`fieldTys`.
- **Runtime reorder + per-field conversion** —
  `StructDecl.constructorArgs?` (`SolidCore/Solidity/Interface.lean:1553`):
  named branch is `mapOption (fun field => Args.findNamed? field.name args)
  decl.fields`, i.e. it walks *declaration-order* fields and fetches each by
  name, so the value lands in the right field. Each field expr is then wrapped
  in `Expr.call (Expr.typeName field.ty) [...]` (line 1636-1642), applying the
  per-field implicit conversion. Matches solc `StructType::constructorType`
  (Types.cpp:2551) which builds param types in member order.
- **Mapping-member reject (#4)** — solc rejects the constructor form itself,
  unconditionally, in `TypeChecker.cpp:2762` (error 9515 "Struct containing a
  (nested) mapping cannot be constructed"), guarded by
  `containsNestedMapping()`. solidity-lean has no dedicated 9515 analogue at the
  struct-ctor path (`TypeCheck.lean:5820`), but reaches the same *reject* by
  two independent routes: (a) a mapping-containing struct cannot be declared as
  a memory local (`Ty.containsMapping` gating, `TypeCheck.lean:1543`), and
  (b) no expression can be assigned to a mapping-typed field, so the arg
  assignability check fails — including the nested `Out(1, si)` case where the
  storage `Inn` value is not assignable into the memory `Inn` field.
  Because the reject is decision-equivalent for every program I could express,
  this is not a divergence; it is only a difference in *which* error fires.
- **Recursive struct (#10)** — direct and mutual struct recursion both reject;
  recursion broken by a dynamic array member (`Node[]`) accepts. Matches solc
  "Recursive struct definition."
- **Comparison (#8)** — struct `==` rejected; see the no-builtin-equality note
  at `TypeCheck.lean:3469`.
- **containsMapping fuel** — `Ty.containsMapping` (`TypeCheck.lean:656`) recurses
  through array/tuple/struct/function with fuel 64, so nested-mapping detection
  is robust for realistic depths.

## Residual-risk notes (not divergences; would need runtime-value differential)

1. The mapping-struct reject reason differs from solc's (arg-count /
   assignability vs a dedicated 9515). If a future change made mapping-typed
   fields assignable (e.g. a storage mapping arg), the struct-ctor path lacks
   solc's up-front `containsNestedMapping` guard and could over-accept. Today no
   such expression exists, so it is latent, not live. Confidence this is
   currently non-divergent: 85%.
2. I did not run a full Forge-vs-interpreter runtime differential for the
   named-reorder *values* or for the copy-vs-alias directions (#7) — those
   overlap the M-family/array-copy work per the mission and the static reorder
   logic is provably order-preserving. Confidence the reorder value is correct:
   88% (from the `constructorArgs?` code path, not executed end-to-end here).

No report-worthy divergence to fix.
