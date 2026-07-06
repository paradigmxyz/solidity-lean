# A1 — Rational constant folding: audit (evidence-based)

**Scope:** audit only. No engine build, no interpreter/checker/importer semantic
changes. This characterizes solc 0.8.35's constant-folding semantics from
compiled probes, then pinpoints where *our* current implementation diverges.

**Tooling:** pinned `solc-0.8.35`; probes in `tests/rational-probes/`
(`accepts.sol`, `rejects/*.sol`), driven by `tests/rational-probes/extract_solc.py`
(solc side) and `tests/rational-probes/our_side_eval.lean` (our side, run with
`lake env lean`).

**Headline finding (correcting the registry's suspicion):** the registry marks
A1 as *suspected unsoundness* ("may currently mis-evaluate"). The suspected
failure mode — silently truncating a fractional constant and accepting a wrong
integer — **does not occur.** A rational folder (`NumberRat`) already exists
(introduced in Phase 3b, `Interface.lean`), folds exactly, and rejects
non-integers. Across the whole probe set there are **0 WRONG-VALUE divergences.**
The real, live gap is **OVER-REJECTION**: `NumberRat` is represented over `Nat`,
so any constant whose folded value is **negative** (formed by subtraction, or a
unary minus nested inside a larger expression) is rejected even though solc
accepts it. See §(b).

---

## (a) solc 0.8.35 semantics, characterized by evidence

### The folding model

solc folds every constant (sub)expression in **unbounded-precision signed
rationals ℚ**, exposed directly in the AST: each expression node carries
`typeDescriptions.typeIdentifier = t_rational_[minus_]<num>_by_<den>` and
`typeString = "int_const N"` (when `den==1`) or `"rational_const N / D"` (when
`den>1`). This is solc's own folded value — no getter needed to read it. Example
(`1 ether / 3 * 3`, from the AST of `accepts.sol`):

```
1 ether            -> int_const 1000000000000000000        (t_rational_1000000000000000000_by_1)
(1 ether) / 3      -> rational_const 1000000000000000000/3 (t_rational_1000000000000000000_by_3)
(1 ether) / 3 * 3  -> int_const 1000000000000000000        (den cancels back to 1)
```

The model is: **fold in exact ℚ (no rounding, no truncation, unbounded
num/den), sub-denominations scale the value by an integer factor, and only a
single final check** decides acceptance when the constant is assigned to a typed
location.

### The accept/reject boundary (exact)

A folded rational `N/D` assigned to target type `T` is **accepted iff all three**:

1. **Integer:** `D == 1` (after full reduction). Otherwise:
   `Error: Type rational_const N / D is not implicitly convertible … Try
   converting to type ufixedMxN …`.
2. **In range:** `uintB`: `0 ≤ N ≤ 2^B − 1`; `intB`: `−2^(B−1) ≤ N ≤ 2^(B−1) − 1`.
   Otherwise: `Error: … Literal is too large to fit in T`.
3. **Sign-compatible:** a **negative** `int_const` into an **unsigned** target is
   rejected even when |N| is in range: `Error: … Cannot implicitly convert signed
   literal to unsigned type`.

### Probe results — ACCEPTS (`accepts.sol`, folded value from AST)

| probe | expression | solc folded value |
|---|---|---|
| SCI_1E18 | `1e18` | 1000000000000000000 |
| SCI_1_5E3 | `1.5e3` | 1500 |
| SCI_2EM2X | `2e-2 * 100` | 2  (fractional intermediate `1/50`) |
| SCI_10E0 | `10e0` | 10 |
| D_ETHER | `1 ether` | 1000000000000000000 |
| D_GWEI | `3 gwei` | 3000000000 |
| D_MINUTES | `2 minutes` | 120 |
| D_MIXTIME | `2 minutes + 30 seconds` | 150 |
| D_WEI | `5 wei` | 5 |
| F_ETHER3 | `(1 ether) / 3 * 3` | 1000000000000000000  (int-trunc would give 999…) |
| F_7_2_2 | `7 / 2 * 2` | 7  (int-trunc would give 6) |
| F_10_4_4 | `10 / 4 * 4` | 10  (int-trunc would give 8) |
| P_256_255 | `2**256 / 2**255` | 2 |
| P_200_3 | `(2**200 * 3) / 2**200` | 3 |
| M_ETHER5 | `1 ether + 5` | 1000000000000000005 |
| M_HALFSUM | `1 / 2 + 1 / 2` | 1  (int-trunc would give 0) |
| N_NEG5 | `0 - 5` | −5 |
| N_SUB | `3 - 10` | −7 |
| N_FRACNEG | `7 / 2 * 2 - 100` | −93 |
| N_UNARY | `-3` | −3 |
| B_U8_255 | `255` (into `uint8`) | 255 |
| B_I8_MIN | `-128` (into `int8`) | −128 |

### Probe results — REJECTS (`rejects/*.sol`, each its own compile)

| probe | expression / target | solc error class |
|---|---|---|
| r01_frac_7_2 | `7 / 2` → uint256 | `rational_const 7 / 2` not convertible (non-integer) |
| r02_frac_literal | `1.5` → uint256 | `rational_const 3 / 2` not convertible |
| r03_sci_neg_exp | `2e-2` → uint256 | `rational_const 1 / 50` not convertible |
| r04_fit_overflow | `1e18` → uint8 | `int_const …` too large to fit in uint8 |
| r05_neg_into_uint | `0 - 1` → uint256 | signed literal → unsigned type |
| r06_fit_256 | `256` → uint8 | too large to fit in uint8 |
| r07_frac_ether | `(1 ether)/3` → uint256 | `rational_const …/3` not convertible |
| r08_i8_underflow | `-129` → int8 | too large to fit in int8 |
| r09_frac_thirds | `1 ether / 3 * 2` → uint256 | `rational_const 2e18/3` not convertible |

Note r05 vs r08: `−1 → uint256` is rejected under rule (3) (sign), while
`−129 → int8` is rejected under rule (2) (range) — two different boundaries, both
confirmed.

---

## (b) Our interpreter's divergences

**What we already have.** `SolidCore/Solidity/Interface.lean` (namespace
`Executable`) contains a full exact-rational folder:

- `structure NumberRat where num : Nat; den : Nat` — **Nat**, not Int
  (Interface.lean:2624).
- `parseNumberRat?` / `parseDecimalRatChars?` / `decimalValueWithScaleRat?` —
  decimal, hex, **scientific notation** (`e±k`), fractional mantissa
  (Interface.lean:2641–2703).
- `parseUnitNumberRat?` scales by `UnitDenomination.factor`
  (Interface.lean:2721–2727; factors in `Ast.lean:153`).
- `NumberRat.add/sub?/mul/div?/mod?/pow/shl?/shr?/bitAnd?…` exact rational ops,
  with `exactNat?` gating the integer-only ops (Interface.lean:2705–2808).
- `Expr.numberLiteralRat?` folds `+ - * / % ** << >> & | ^` and unit/paren/cast
  over `NumberRat` (Interface.lean:2826–2836).
- `Expr.toCoreNumericLiteralAs?` is the typed accept/reject + fit check
  (Interface.lean:3313–3340): `uintLiteralFits`, `intPositiveLiteralFits`,
  `intNegativeLiteralFits` — these match solc's boundary rules (2)/(3) exactly
  (confirmed by B_U8_255, B_I8_MIN, r04, r06, r08, r05).

**Importer.** `scripts/solc_ast_to_lean_source.py` emits the *raw literal text*
into `Literal.number "<value>"` / `Literal.unitNumber "<value>" <unit>`
(`expr_from_node`, lines 1004–1027), so scientific/fractional/unit text survives
into Lean and is folded there — the naive `literal_number_nat` regex `[0-9]+`
(line 543) is **not** on the general expression path. It is used only for array
lengths and type-expression indices; the array-length path
(`array_length_nat_from_node`, line 552) has a `typeString` fallback that reads
solc's *already-folded* `uintB[10]` shape, so `uint8[1e1]` imports correctly as
`Ty.array (Ty.uint 8) (some 10)` (verified).

### Divergence classification (per probe)

Our-side outcome from `our_side_eval.lean` (`toCoreNumericLiteralAs?` = accept +
value, or `none` = reject):

| probe | solc | ours | class |
|---|---|---|---|
| SCI_1E18, SCI_1_5E3, SCI_2EM2X, SCI_10E0 | accept | accept, same value | **PARITY** |
| D_ETHER, D_GWEI, D_MINUTES, D_MIXTIME, D_WEI | accept | accept, same value | **PARITY** |
| F_ETHER3, F_7_2_2, F_10_4_4 | accept | accept, same value | **PARITY** |
| P_256_255, P_200_3 | accept | accept, same value | **PARITY** |
| M_ETHER5, M_HALFSUM | accept | accept, same value | **PARITY** |
| N_UNARY (`-3`→int256), B_I8_MIN (`-128`→int8) | accept | accept, same value | **PARITY** |
| B_U8_255, r01–r09, r04/r05/r06/r08 | reject | reject, same boundary | **PARITY** |
| **N_NEG5 (`0 - 5` → int256)** | accept −5 | **reject (`none`)** | **OVER-REJECT** |
| **N_SUB (`3 - 10` → int256)** | accept −7 | **reject (`none`)** | **OVER-REJECT** |
| **N_FRACNEG (`7/2*2 - 100` → int256)** | accept −93 | **reject (`none`)** | **OVER-REJECT** |

**Tally: 0 WRONG-VALUE, 3 OVER-REJECT, all other probes PARITY.**

- Most alarming WRONG-VALUE: **none exist.** The exact-rational fold + `exactNat?`
  gate structurally prevents the truncation-then-accept failure the registry
  feared. Concretely, `F_7_2_2` and `M_HALFSUM` — the classic truncation traps —
  both return solc's exact value (7 and 1), not the int-truncated 6 and 0.
- Most alarming OVER-REJECT: **N_FRACNEG** `int256 constant = 7 / 2 * 2 - 100;`
  — a fully legal solc program (folds to `−93`) that our checker rejects
  outright.

### Where the loss happens (file:line)

Root cause is a single representability gap: **`NumberRat` is over `Nat`.**

1. `structure NumberRat where num : Nat; den : Nat`
   — Interface.lean:2624–2626. No sign; cannot represent a negative value.
2. `NumberRat.sub?` returns `none` when `rhsNum > lhsNum`
   — Interface.lean:2709–2715. So `0 - 5`, `3 - 10`, `… - 100` fold to `none`.
3. The typed path only recognises a **top-level syntactic** unary minus via
   `Expr.negatedNumberLiteralNat?` (Interface.lean:3189–3193), which matches
   `Expr.unary neg …` and takes the inner magnitude. A *negative produced by
   subtraction* (or a unary minus nested inside a binary op) never reaches this
   case: it flows to `Expr.numberLiteralNat? → numberLiteralRat?` where
   `sub?`/absent-unary yields `none` (Interface.lean:3185–3187, 3313–3340).
4. Corollaries (same root cause, not separately probed but implied): `(-2)**2`,
   `5 * -1`, `-(a) - b` — any negative intermediate — over-reject.

**Second, narrower path (importer hard-fail, not a Lean reject):**
`type_from_expression_node` computes an array size in *type-expression* position
via `literal_number_nat(index)` with **no** typeString fallback
(solc_ast_to_lean_source.py:658) — so a scientific/unit-denominated length in
that position (e.g. an explicit `uintB[1e1]` type expression) aborts the import.
Low frequency; noted for completeness. The common array-length path
(VariableDeclaration `ArrayTypeName`) is already covered by the typeString
fallback and does **not** diverge.

---

## (c) Engine design spec (for the later implementation, not this audit)

The existing folder is ~90% of the engine and already exact for the
non-negative surface. The build is a **targeted `Nat → Int` widening of
`NumberRat`**, plus one syntactic simplification of the negative path.

### Representation

Replace `NumberRat` with a signed exact rational. Keep it total (no `partial`):

```
structure NumberRat where
  num : Int          -- signed numerator (was Nat)
  den : Nat          -- strictly-positive denominator; invariant den ≠ 0
  deriving Repr
```

Keep sign on `num` only (canonical: `den > 0`). Reduction is optional for
correctness (`exactNat?`/comparisons already divide), but reducing by `gcd`
keeps the huge-power intermediates (`2^256`) from ballooning — recommended for
performance, not soundness.

### Operations needing exact signed arithmetic

- `add` — `num := lhs.num*rhs.den + rhs.num*lhs.den` (already exact; just Int).
- `sub` — becomes **total** (no `?`): `num := lhs.num*rhs.den − rhs.num*lhs.den`.
  This is the whole fix for the 3 OVER-REJECTs. Update
  `BinaryOp.applyNumberRat?` (Interface.lean:2795) to `some (lhs.sub rhs)`.
- `mul`, `div?` (guard `rhs.num == 0`) — unchanged shape, Int num.
- `pow` — `num := base.num ^ exponent` over Int (negative base handled for free,
  fixing `(-2)**2`).
- `mod?`, `bitAnd?/Or?/Xor?`, `shl?/shr?/sar?` — solc requires **integer**
  operands here; keep gating on `exactNat?`, but `exactNat?` must now first
  require `num ≥ 0` (bit/shift ops on negatives are solc errors) and then divide.
  Define `exactInt? : NumberRat → Option Int` for signedness, and keep
  `exactNat?` = `exactInt?` filtered to `≥ 0`.
- Comparisons (`lt/eq/le`) — cross-multiply with sign care (multiply by
  positive `den`s only, so ordering is preserved).

### Sub-denomination scaling and the final integer-fit check — unchanged locations

- `parseUnitNumberRat?` (Interface.lean:2724) still scales by
  `unit.factor : Nat`; with signed `num` it composes with a leading unary minus.
- The single final check stays in `Expr.toCoreNumericLiteralAs?`
  (Interface.lean:3313). After widening, **collapse** the special
  `negatedNumberLiteralNat?` branch: fold the whole expression once to a signed
  `NumberRat`, take `exactInt?`, then apply the three boundary rules directly:
  - `uintB`: accept iff `0 ≤ v ≤ 2^B − 1`.
  - `intB` : accept iff `−2^(B−1) ≤ v ≤ 2^(B−1) − 1`.
  This makes rules (2) and (3) fall out of one signed range test and removes the
  syntactic top-level-unary-only limitation. `uintLiteralFits` /
  `intPositive/NegativeLiteralFits` (Interface.lean:3304–3311) are subsumed.

### Code paths replaced

- `NumberRat` struct + all `NumberRat.*` ops (Interface.lean:2624–2808): Nat→Int.
- `Expr.numberLiteralRat?` / `untypedNumberLiteralRat?` (2826, 3195): add a real
  `Expr.unary UnaryOp.neg` case returning `{ v with num := -v.num }` (the current
  `untyped` "only if zero" guard at 3199–3201 is removed).
- `Expr.negatedNumberLiteralNat?` (3189) and the split branch in
  `toCoreNumericLiteralAs?` (3325–3339): collapse into one signed fit test.
- Importer: give `type_from_expression_node`'s length (line 658) the same
  `typeString` fallback `array_length_nat_from_node` uses, so scientific/unit
  lengths in type-expression position import instead of aborting.

### Totality

All ops stay structural/total. Division/mod/shift keep `Option` for the genuine
partial cases (den 0, non-integer operand). No `partial`, no `decreasing_by`
obligations beyond what `Expr.numberLiteralRat?`'s existing mutual block already
discharges.

### Probe fixtures → pinned corpus lanes

`tests/rational-probes/` is the seed corpus. Wire each into `manifest.json` as a
paired Forge/solc lane:

- ACCEPTS: `accepts.sol` gains a Forge test reading each public `constant` getter;
  the expected value is the AST-folded value in §(a). N_NEG5/N_SUB/N_FRACNEG are
  the **red** lanes that go green when the engine lands (currently our importer
  imports them but the checker rejects → confirm red first).
- REJECTS: each `rejects/*.sol` is a lane asserting *both* solc and our checker
  reject (our side already rejects — these pin the boundary against regressions).

The engine is done when all ACCEPT lanes match solc's value, all REJECT lanes
stay red on both sides, and the full corpus stays green.
