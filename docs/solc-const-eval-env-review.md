# Divergence review: solc 0.8.35 constant evaluator + environment-value modeling vs Solidus

**Scope.** One re-derivation surface reviewed as a unit: solc's compile-time
constant evaluator (`libsolidity/analysis/ConstantEvaluator.cpp` +
`RationalNumberType` in `libsolidity/ast/Types.cpp`, pinned source 0.8.35 /
47b9dedd) against Solidus's exact-rational folder (`NumberRat` and its
consumers in `SolidCore/Solidity/Interface.lean`, the literal/constant gates in
`SolidCore/Solidity/TypeCheck.lean`). Secondary: environment/block/tx value
modeling. Method: read both sides, then probe pinned `solc-0.8.35`
(accept/reject + AST-folded `typeString` values). Read-only — no Solidus
build/run; Solidus-side outcomes are traced through the checker/lowering code
and marked CONFIRMED (both ends pinned by explicit code + solc probe) or
INFERRED (pipeline behavior read, not replayed). Builds on the earlier A1 audit
(`docs/rational-constants-audit.md`), whose Nat→Int widening of `NumberRat` is
landed; everything below is beyond A1.

## Executive summary

Surfaces read: `ConstantEvaluator.cpp` in full (all 472 lines: binary/unary
rational evaluation, precision guards, depth limit, identifier/tuple/erc7201
evaluation); `Types.cpp` `RationalNumberType` (literal parsing + exponent caps,
`binaryOperatorResult` incl. the 4096-bit cap and the comparison
`mobileType` path, `integerType`/`fixedPointType`, conversion rules);
Solidus `NumberRat` + `Expr.numberLiteralRat?`/`numberLiteralBool?`/
`toCoreNumericLiteralAs?`/`toCoreAs?` (Interface.lean), `literalTy?`, unary and
binary operator checking, `StateVarDecl.check`, `implicitLiteralFits`
(TypeCheck.lean), the importer's literal/operator emission
(`scripts/solc_ast_to_lean_source.py`), and the env-value model
(`Expr.abiTy?`, checker fork gates, `EnvWord.eval`, `calldataSelectorWord`).
37 solc probes run (18-constant accept file with AST value extraction, 19
reject probes, 4 follow-ups, depth-limit pair, env probe).

**NEW findings: 6 differentially-live (5 wrong-accept/reject over-rejects +
1 non-termination hazard), 3 importer-masked (wrong-accept families +
depth limit). No both-sides-accept wrong-VALUE divergence was found** — where
both sides accept a constant, the exact-rational fold (or the 256-bit runtime
path it falls back to) reproduces solc's folded value on every probed case.
The live divergences are all on the accept/reject boundary, in one root-cause
family: **Solidus gates several fold operators on `exactNat?` (non-negative
integer) where solc's evaluator is defined on signed integers or rationals,
and the folder has no unary `~` case at all.**

Ranked NEW findings (differentially-live first):

1. **CE-1 (over-reject, CONFIRMED): negative exponents in constant `**`.**
   solc inverts: `4 * 2**-1` = 2, `2**-2 * 16` = 4, and the quirk
   `0**-1` = 0 (base-0/1 short-circuit precedes the sign check). Solidus
   rejects all of these twice over: the checker requires an unsigned-typed
   exponent, and the folder requires `rhs.exactNat?`.
2. **CE-3 (over-reject, CONFIRMED solc / INFERRED lowering): negative
   operands in constant shifts and bitwise ops.** solc: `(-1) << 2` = −4,
   `-7 >> 1` = −4 (floor, not trunc), `-1 >> 100` = −1, `-4 | 1` = −3.
   Solidus's `shl?/shr?/bitAnd?/bitOr?/bitXor?` gate both operands on
   `exactNat?` → fold fails → raw-literal fail-closed lowering → reject.
3. **CE-2a (over-reject, CONFIRMED): unary `~` missing from the rational
   folder.** solc folds `~` on integer rationals: `~5` = −6, `~(-3)` = 2,
   `~5 & 0xFF` = 250 — all accepted into `int256`. Solidus types `~5` as
   `uint256` and cannot fold it, so every int-targeted use over-rejects.
4. **CE-4 (over-reject, CONFIRMED): fractional constant `%`.** solc:
   `7 % 2.5` = 2 (`x − trunc(x/y)·y`). Solidus `mod?` requires both operands
   to be exact integers → reject.
5. **CE-5 (over-reject, CONFIRMED): fractional denominated literals.**
   solc: `0.5 wei * 2` = 1. Solidus's `literalTy?` gates `unitNumber`
   literals through `parseUnitNumberNat?` (integer-only) → the literal itself
   is rejected before any folding.
6. **CE-6b (non-termination hazard on an accepted program, INFERRED):
   unbounded `pow` for base 0/1/−1.** solc exempts bases 0, 1, −1 from its
   `uint32` exponent cap, so `uint constant X = 1**(2**100);` **compiles**
   (= 1). Solidus's `NumberRat.pow` computes `1 ^ (2^100 : Nat)` with no
   special-casing; if Lean's `Nat.pow`/`Int.pow` is Θ(exponent) on this path
   the import pipeline hangs on a solc-accepted program.

Importer-masked (solc rejects first, so unreachable through the AST-import
pipeline; live only for source-level accept/reject differentials):

7. **CE-6a (wrong-accept family, CONFIRMED solc / INFERRED Solidus):** no
   4096-bit precision cap, no `uint32` exp/shift caps, no literal-exponent
   cap, and comparison folding beyond solc's `mobileType` limit. Solidus
   accepts (and folds exact values for) `2**5000 / 2**5000`, `10**1025 /
   10**1025`, `1e2000 / 1e2000`, `(1 << 4200) >> 4200`, `0 << 2**33`,
   `bool constant B = 2**300 < 2**301`, `bool constant B = 1/2 < 1` — solc
   rejects every one. Includes `uint x = ~0;` / `x + ~0` (CE-2b): solc
   rejects (`int_const -1` into unsigned); Solidus accepts and evaluates the
   256-bit runtime `~`, yielding `2^256−1`.
8. **CE-7 (unmodeled, CONFIRMED solc):** constant-evaluation depth limit 32 —
   a 34-deep constant chain used as an array length errors ("Cyclic constant
   definition (or maximum recursion depth exhausted)"), a 20-deep chain
   compiles. Solidus detects only true cycles; array-length contexts are
   importer-masked (lengths come from solc's folded `typeString`).
9. **CE-8 (wrong-accept, CONFIRMED solc):** hex literal with a denomination
   (`0x10 wei`) is a solc error; Solidus's `parseUnitNumberRat?` happily
   scales hex.

**Environment-value modeling: no new findings (earned).** Version gates,
`difficulty`/`prevrandao` Paris aliasing (warning-only in solc — probed),
`msg.sig` zero-padded 4-byte calldata prefix, `msg.data`, and the tx/block
word members all match solc/EVM semantics (§3).

---

## 1. The two models

**solc** folds constant (sub)expressions in unbounded signed rationals ℚ
(`boost::multiprecision`), but with explicit resource guards:

- After **every** binary op, numerator and denominator must fit 4096 bits
  (`Types.cpp:1128-1135`, error "Precision of rational constants is limited
  to 4096 bits.").
- `**`: exponent must be integer (`ConstantEvaluator.cpp:116-117`); bases
  0/1/−1 short-circuit **before** the sign/size checks
  (`ConstantEvaluator.cpp:120-129` — hence `0**-1` = 0, and unlimited
  exponents for these bases); otherwise |exp| ≤ `uint32` max
  (`:133-134`) and `fitsPrecisionExp` (`:46-64`, ≈ (msb(base)+1)·exp ≤ 4096 —
  so `10**1024` folds, `10**1025` errors; probed). **Negative exponents
  invert** (`:153-157`).
- `<<`: non-fractional, rhs ∈ [0, uint32max], `fitsPrecisionBase2`
  (`:161-179`). lhs may be negative. `>>` (SAR): rounds toward −∞ for
  negative lhs (`:182-213`), and shifts past the msb give −1/0 (`:195-196`).
- `%`: defined on fractionals as `x − trunc(x/y)·y` (`:103-113`); integer
  case is boost's truncated `%` (sign of dividend).
- `& | ^` operate on the signed numerators (two's-complement bigints,
  `:80-94`); `~` is defined on any integer rational (`:223-227`).
- Number literals: exponent must fit int32 and the scaled mantissa must pass
  `fitsPrecisionBase10` (`Types.cpp:938-962`) — `1e2000` is an
  **invalid literal** (probed).
- Comparisons are *not* folded: both operands convert to `mobileType()` and
  compare at runtime (`Types.cpp:1117-1126`); an integer constant that does
  not fit `u256`/`s256` has no `integerType()` (`Types.cpp:1218-1232`) so the
  comparison is a type error (probed: `2**300 < 2**301` rejected; `1/2 < 1`
  rejected — no ufixed/uint common type; but `1/2 == 0.5` **accepted**, both
  mobile to the same `ufixed`).
- Constant `VariableDeclaration` evaluation recurses with a depth limit of 32
  (`ConstantEvaluator.cpp:325-334`).

**Solidus** folds in `NumberRat` (`Interface.lean:2656-2658`, signed `Int`
numerator / positive `Nat` denominator since the A1 fix), with:

- ops `add/sub/mul` total, `div?/mod?` partial (`Interface.lean:2756-2798`);
- `pow` over a `Nat` exponent only (`Interface.lean:2800-2802`), gated by
  `rhs.exactNat?` in `BinaryOp.applyNumberRat?` (`Interface.lean:2853-2855`);
- `bitAnd?/bitOr?/bitXor?/shl?/shr?/sar` all gated on **both** operands'
  `exactNat?` (`Interface.lean:2804-2827`);
- the expression folder `Expr.numberLiteralRat?` handles literal / unit
  literal / unary **neg** / binary / type-cast-wrapper only — **no `bitNot`
  case** (`Interface.lean:2880-2893`); comparisons fold to `Bool` via
  `numberLiteralBool?` (`Interface.lean:2895-2900`);
- **no size caps anywhere** — `NumberRat` is unbounded;
- the typed accept/fit gate `Expr.toCoreNumericLiteralAs?`
  (`Interface.lean:3469-3487`) and the fail-closed raw-literal guard in
  `Expr.toCoreAs?` (`Interface.lean:4693-4698`): if the fold fails on a
  raw-number-literal-shaped expression targeted at an int/uint, lowering
  returns `none` (= program rejected), matching the A1-era behavior;
- checker side: number literals type as `uint 256` (`TypeCheck.lean:
  4072-4075`), `~` keeps its operand's type (`TypeCheck.lean:7011-7013`),
  unary `-` on a foldable literal types as `int 256` (`TypeCheck.lean:
  7014-7020`), `**` requires an unsigned-typed exponent
  (`TypeCheck.lean:7105-7108`).

## 2. Findings — constant evaluator

### CE-1 — negative constant exponents (incl. the `0**-1 = 0` quirk)
**OVER-REJECT · CONFIRMED · DIFFERENTIALLY-LIVE**

solc: `ConstantEvaluator.cpp:114-158`. Probes (AST-folded values):
`uint256 constant P1 = 4 * 2**-1;` → `int_const 2`;
`uint256 constant P2 = 0**-1;` → `int_const 0` (base-0 short-circuit at
`:124` precedes negative-exponent handling — no division-by-zero error);
`uint256 constant P17 = 2**-2 * 16;` → `int_const 4`;
`uint256 constant P4 = 8 * (1/2)**3;` → `int_const 1` (rational base, for
contrast — this one Solidus folds fine).

Solidus rejects at **two** layers: `TypeCheck.lean:7105-7108`
(`rhsChecked.expectUnsignedInteger` — `-1` types `int 256` via
`TypeCheck.lean:7014-7020`), and `Interface.lean:2853-2855`
(`rhs.exactNat?`). A legal solc program using a negative literal exponent
imports (importer emits raw `**`/unary-minus) and is rejected → visible in
the accept/reject differential. Fix shape: fold `**` over `exactInt?`,
inverting for negative exponents, and relax the checker for
rational-constant exponents (solc types the whole thing as a rational, so no
unsigned-type requirement exists for literal operands).

### CE-2 — unary `~` absent from the folder
**(a) OVER-REJECT · CONFIRMED · DIFFERENTIALLY-LIVE;
(b) WRONG-ACCEPT · CONFIRMED solc, INFERRED Solidus · IMPORTER-MASKED**

solc: `ConstantEvaluator.cpp:223-227` (`~` on any integer rational).
Probes: `int256 constant P10 = ~5;` → `int_const -6`;
`int256 constant P15 = ~(-3);` → `int_const 2`;
`int256 constant X = ~5 & 0xFF;` → `int_const 250` — all ACCEPTED.
Rejected by solc: `uint256 constant R = ~0;` ("Cannot implicitly convert
signed literal to unsigned type"), `uint256(~0)` ("Explicit type conversion
not allowed"), and even `x + ~0` for `uint256 x` ("operator + cannot be
applied to types uint256 and int_const -1").

Solidus: `Expr.numberLiteralRat?` has no `bitNot` case
(`Interface.lean:2880-2893`), and `~e` types as its operand's type — for a
bare literal, `uint 256` (`TypeCheck.lean:7011-7013`, `4072-4075`). Hence:

- (a) any int-targeted constant containing `~lit` fails
  `implicitLiteralFits` (fold `none`) and `uint256→int256` implicit
  conversion → **reject** where solc accepts (−6 / 2 / 250 above). Live: the
  importer emits `~` (`solc_ast_to_lean_source.py:938`).
- (b) `uint256`-targeted `~lit` sails through the checker
  (`uint256 == uint256`) and lowers through the *runtime* unary path
  (`Interface.lean:4397-4400`; typed path `Interface.lean:4699-4715` — the
  raw-literal fail-closed guard `Expr.isRawNumberLiteralExpression`
  (`Interface.lean:3405-3412`) has no `bitNot` case, deliberately or not, so
  it does NOT fail closed) → evaluates `~0` as `2^256−1` in a program solc
  refuses to compile. Masked in the import pipeline (no solc AST exists),
  but a checker-soundness gap.

Note the value-coincidence family: where the `~`-expression's rational value
is a *non-negative* integer that fits (e.g. `~~5` = 5, `~5 & 0xFF` = 250 into
`uint`), Solidus's 256-bit runtime path produces the same value as solc's
fold (two's-complement agreement) — so no wrong-value case was found, only
the boundary divergences above.

### CE-3 — negative operands in constant shifts/bitwise ops; `>>` floor
**OVER-REJECT · CONFIRMED solc, lowering INFERRED · DIFFERENTIALLY-LIVE**

solc: SHL `ConstantEvaluator.cpp:161-179` (lhs may be negative; only rhs is
sign/size-checked), SAR `:182-213` (**rounds toward −∞**: `(x+1)/2^n − 1`
for negative x; shifts past msb give −1/0), bitwise on signed numerators
`:80-94`. Probes: `int256 constant P6 = (-1) << 2;` → `int_const -4`;
`P7 = -7 >> 1;` → `int_const -4` (trunc would give −3);
`P8 = -1 >> 100;` → `int_const -1`; `P12 = -4 | 1;` → `int_const -3` — all
ACCEPTED.

Solidus: `shl?/shr?/bitAnd?/bitOr?/bitXor?` all gate **both** operands on
`exactNat?` (`Interface.lean:2804-2827`) → fold fails → the raw-literal
fail-closed guard in `Expr.toCoreAs?` (`Interface.lean:4693-4698`) rejects.
(Checker-side these pass — e.g. `<<` accepts an int lhs via
`Ty.isShiftLeftOperand`, `TypeCheck.lean:413-414` — so the reject surfaces at
lowering; same fail-closed pipeline the A1 audit exercised.) When widening,
`>>` must implement solc's floor-division rounding (and the "past-msb → −1"
rule), NOT `Int` truncated division — that would be the wrong-value trap.

### CE-4 — fractional constant `%`
**OVER-REJECT · CONFIRMED · DIFFERENTIALLY-LIVE**

solc: `ConstantEvaluator.cpp:103-113` — for fractional operands,
`x % y = x − trunc(x/y)·y`. Probe: `uint256 constant P9 = 7 % 2.5;` →
`int_const 2`, ACCEPTED. Solidus `NumberRat.mod?` requires both operands to
be exact integers (`Interface.lean:2789-2798`) → fold fails → fail-closed
reject. (The integer case is parity: `Int.tmod` = boost's truncated `%`;
`-7 % 3` = −1 on both sides.)

### CE-5 — fractional denominated literals rejected at the literal
**OVER-REJECT · CONFIRMED · DIFFERENTIALLY-LIVE**

solc: sub-denominations scale the rational (`Types.cpp:977-1004`);
`uint256 constant P14 = 0.5 wei * 2;` → `int_const 1`, ACCEPTED. Solidus:
`literalTy?` for `unitNumber` runs `parseUnitNumberNat?`
(`TypeCheck.lean:4076-4078`), which demands `exactNat?` — `0.5 wei` (= 1/2)
fails, so `checkExpr` errors "unsupported literal" before any fold. The
rational machinery underneath (`parseUnitNumberRat?`,
`Interface.lean:2773-2776`) handles it perfectly — only the `Nat` gate is
wrong (should be `parseUnitNumberRat?.isSome`). Rare shape
(`x.y wei` / fractional `seconds`), but legal and importable.

### CE-6 — missing resource caps (4096-bit / uint32) and comparison limits
**(a) WRONG-ACCEPT · CONFIRMED solc, INFERRED Solidus · IMPORTER-MASKED;
(b) NON-TERMINATION HAZARD · INFERRED · DIFFERENTIALLY-LIVE**

solc rejects (all probed):

| probe | solc error site |
|---|---|
| `2**5000 / 2**5000` | `fitsPrecisionExp`, CE.cpp:138 |
| `10**1025 / 10**1025` (10**1024 folds) | same, (msb+1)·exp > 4096 |
| `1e2000 / 1e2000` | invalid literal, Types.cpp:956 |
| `(1 << 4200) >> 4200` | `fitsPrecisionBase2`, CE.cpp:174 |
| `0 << 2**33` | rhs > uint32max (checked *before* the lhs==0 shortcut), CE.cpp:167 |
| `2**(2**40)` | exp > uint32max, CE.cpp:133 |
| `bool constant B = 2**300 < 2**301` | no `integerType()` ⇒ no mobile type, Types.cpp:1117-1126, 1218-1232 |
| `bool constant B = 1/2 < 1` | no ufixed/uint common type (yet `1/2 == 0.5` is ACCEPTED — both mobile to the same ufixed) |

Solidus has none of these caps: `NumberRat` is unbounded, the folder folds
all of the first six to small exact values (1, 1, 1, 1, 0, —) and
`numberLiteralBool?` (`Interface.lean:2895-2900`) folds the comparisons to
`true`, so all are ACCEPTED. Reachability: solc rejects ⇒ no AST ⇒ masked in
the import pipeline; a source-level accept/reject differential would flag
every row. Two sub-hazards are **live**, though:

- (b) solc's base-0/1/−1 exemption (CE.cpp:120-129) means `uint256 constant
  P5 = 1**(2**100);` **compiles** (probed, `int_const 1`). Solidus's
  `NumberRat.pow` (`Interface.lean:2800-2802`) computes `1 ^ (2^100 : Nat)`
  literally; whether this terminates quickly depends on Lean's `Nat.pow`
  path for astronomically large exponents. If it is Θ(exponent), a
  solc-accepted program hangs Solidus's checker/lowering. Same shape:
  `0**(10**60)`, `(-1)**(2**100)`. Needs a 30-second runtime test before any
  fix; special-casing bases 0/1/−1 in `pow` (as solc does) removes the risk
  regardless of caps.
- Even for solc-rejected inputs, feeding Solidus `0 << 2**33` or
  `2**(2**40)` directly makes `shl?`/`pow` attempt multi-gigabyte bignums —
  a DoS vector for any future source-level (non-importer) front end. Adopting
  solc's three caps (4096-bit post-op, uint32 exp/shift, int32 literal
  exponent) fixes CE-6a and this together.

### CE-7 — constant-evaluation depth limit 32
**UNMODELED · CONFIRMED solc · IMPORTER-MASKED · LOW**

`ConstantEvaluator.cpp:325-334`: evaluating a constant more than 32 levels
deep is a fatal error. Probed: a 34-long `C{i} = C{i-1} + 1` chain used as an
array length → "Cyclic constant definition (or maximum recursion depth
exhausted)."; a 20-long chain compiles. Solidus's
`StateVarDecls.constantsHaveCycle` (`TypeCheck.lean:8493-8519`) detects true
cycles only (matching solc's separate PostTypeChecker pass), not the depth
cap. All contexts where the cap can fire (array lengths, `bytesN` sizes…)
reach Solidus through solc-folded `typeString`s → masked.

### CE-8 — hex literal + denomination
**WRONG-ACCEPT · CONFIRMED solc · IMPORTER-MASKED · LOW**

`0x10 wei` is a solc scanner/parser error (probed: "Hexadecimal numbers
cannot be used with unit denominations"). Solidus `parseUnitNumberRat?`
scales hex text fine (`Interface.lean:2746-2754, 2773-2776`). The importer
can never produce this shape (solc rejects first).

### Parity results (probed, no divergence)

- Exact rational intermediates: `7/2*2` = 7, `1 ether/3*3` = 1e18,
  `(1/2)**3`, `(-2)**3` = −8, `2**255*4/4` (A1 + this review).
- Fit/sign boundary: `255+1`→uint8, `127+1`→int8, `2**256`→uint256, `1/0`,
  `1%0`, `7/2`→uint, `uint[7/2]`, negative into unsigned — reject on both
  sides; `uint[true?1:2]` solc-rejected (ConstantEvaluator has no
  conditional) and importer-masked for Solidus.
- `0**0` = 1 (`Nat`/`Int` pow convention matches CE.cpp:122-123).
- Integer `%` incl. negatives: `Int.tmod` ≡ boost truncated `%`.
- `>>` on non-negative: `Nat` floor division ≡ solc SAR non-negative branch;
  `(1 << 4000) >> 4000` = 1 both sides (4000 < 4096).
- Literal syntax: `.5 * 2` = 1 (empty integer part handled,
  `Interface.lean:2613-2617`); `1_0e1_0` = 1e11; underscore placement rules
  (`1__0`, `1_`, `_1`, `1_e5`, `1e_5` all rejected by both).
- `5 & ~0` = 5 and `~~5` = 5: value parity via the 256-bit runtime path
  (two's-complement agreement), despite the missing `~` fold.
- `1/2 == 0.5`: solc ACCEPTS (probed) and Solidus folds `true` — parity.
- Ternary-of-literals mobile typing (`untypedLiteralMobileTy?`,
  `Interface.lean:3449-3464`) — matches solc's Conditional common-mobile-type
  rule (previously reviewed surface, re-checked at this boundary).
- Cyclic constants (`A = B; B = A`) rejected both sides.

## 3. Environment-value modeling — no new findings

| member | solc 0.8.35 | Solidus | verdict |
|---|---|---|---|
| `block.difficulty` post-Paris | **warning** 8417 only, compiles to PREVRANDAO (probed: warning, accepted) | accepted (`Interface.lean:4783`); evaluates to the `prevrandao` field when `parisOrLater` (`Interpreter.lean:1868-1874`) | parity |
| `block.prevrandao` pre-Paris | warning 9432, treated as difficulty (TypeChecker.cpp:3461-3466) | evaluates to `difficulty` field pre-Paris (`Interpreter.lean:1881-1887`) | parity |
| `block.basefee` | error pre-London (TypeChecker.cpp:3449-3454) | checker gate `requireLondonOrLater` (`TypeCheck.lean:5386-5387`) | parity |
| `block.blobbasefee` | error pre-Cancun (TypeChecker.cpp:3455-3460) | `requireCancunOrLater` (`TypeCheck.lean:5388-5389`) + witness `blobbasefeePreCancunRejected` | parity |
| `block.chainid` | error pre-Istanbul | `requireIstanbulOrLater` (`TypeCheck.lean:5390-5391`) | parity |
| `msg.sig` | first 4 bytes of calldata (CALLDATALOAD(0) truncated; zero-padded when calldata < 4 bytes) | **re-derived**: `calldataSelectorWord` = `bytesPrefixRightPadded selectorBytes calldata` (`Interpreter.lean:56-57, 5959-5961`) — zero-pads short calldata | parity |
| `msg.data` | full calldata | `Expr.calldata` returns the whole context calldata (`Interpreter.lean:5957-5958`); `msg.data` in `receive` rejected (G10, `TypeCheck.lean:5343-5347`) | parity |
| `coinbase/gaslimit/number/timestamp/gasprice/origin` | context values | context-supplied `EnvWord` fields (`Interpreter.lean:1865-1896`); `gasleft` modeled as a resource query, not ambient (A3) | parity |

The only Solidus re-derivations here are `msg.sig` (from calldata) and the
Paris-era `difficulty`↔`prevrandao` aliasing; both match solc's codegen (the
same opcode 0x44 backs both members, so aliasing the *stored field* is the
correct model). Members that must be version-rejected are gated in the
checker **and** version-forked in the interpreter — consistent. No
divergence identified; classified as an earned "none."

## 4. Checklist of cases covered

Constant evaluator — probed against pinned solc (P/r/x/depth files in the
session scratchpad, values from AST `typeString`):

- [x] rational intermediates & integer-result requirement (`7/2`, `7/2*2`, `10/3`, `1 ether/3*3`)
- [x] constant overflow into target (`255+1`→uint8, `127+1`→int8, `2**256`→uint256; no wrap)
- [x] `**`: `0**0`, `0**-1` (=0 quirk), negative exponents (`2**-1`, `2**-2*16`), rational base (`(1/2)**3`, `(-2)**3`), base-0/1/−1 unlimited exponents (`1**(2**100)`), uint32 cap (`2**(2**40)`), `fitsPrecisionExp` boundary (`10**1024` ok / `10**1025` reject)
- [x] division/mod: trunc + sign (`-7%3`, `7%-3` semantics), fractional `%` (`7%2.5`=2), `1/0`, `1%0`
- [x] shifts: negative lhs `<<`/`>>`, floor rounding (`-7>>1`=−4), past-msb (`-1>>100`=−1), rhs uint32 cap (`0<<2**33`), `fitsPrecisionBase2` (`1<<4200` vs `1<<4000`)
- [x] bitwise on signed (`-4|1`, `5&~0`) and `~` (`~5`, `~(-3)`, `~0`, `~5&0xFF`, `uint256(~0)`, `x+~0`)
- [x] 4096-bit post-op cap (`2**5000/2**5000`) and literal exponent cap (`1e2000`)
- [x] comparisons: foldability limits (`2**300<2**301` reject, `1/2<1` reject, `1/2==0.5` accept, `1<2` accept)
- [x] special contexts: array sizes (`uint[7/2]`, `uint[true?1:2]`, constant-chain length), constant-eval depth 32 (34-chain reject / 20-chain accept)
- [x] literal edges: `.5`, `1e18`/`1.5e3`/`2e-2` (A1), `1_0e1_0`, underscore misplacements, hex (`0x10 wei` reject), denominations (`0.5 wei*2`=1, `2 minutes+30 seconds`, `1 ether+5` per A1)

Environment: `block.chainid`, `basefee`, `blobbasefee`, `prevrandao` /
`difficulty` (both directions of the Paris fork, probed warning-only),
`gaslimit`, `coinbase`, `number`, `timestamp`, `msg.sig` (short-calldata
padding), `msg.data` (incl. receive-function ban), `tx.gasprice`,
`tx.origin`, `gasleft`.

## 5. Suggested fix shape (not applied — review only)

One coherent widening of `BinaryOp.applyNumberRat?` +
`Expr.numberLiteralRat?`, mirroring `ConstantEvaluator.cpp` op-for-op:

1. `exp`: fold over `exactInt?`; special-case bases 0/1/−1 first (also fixes
   CE-6b); negative exponent inverts; then port the uint32 +
   `fitsPrecisionExp` caps. Checker: allow rational-constant exponents.
2. `shl?/sar`: operands via `exactInt?`; SHL sign-agnostic lhs; SAR with
   floor rounding + past-msb −1/0; rhs ∈ [0, uint32max] + base2 cap.
3. `bitAnd?/bitOr?/bitXor?`: `exactInt?` two's-complement (Lean `Int.land`
   etc. already match bigint semantics).
4. Add `Expr.unary UnaryOp.bitNot` to the folder (`~x = −x−1` on
   `exactInt?`), and add `bitNot` to `isRawNumberLiteralExpression` so
   uint-targeted `~lit` fails closed instead of evaluating at runtime
   (closes the CE-2b wrong-accept).
5. `mod?`: fractional case `x − trunc(x/y)·y`.
6. `literalTy?` for `unitNumber`: gate on `parseUnitNumberRat?` instead of
   `parseUnitNumberNat?`.
7. Port the three caps (4096-bit post-op, int32 literal exponent, uint32
   exp/shift) as `Option`-failures; this simultaneously kills CE-6a and the
   bignum-DoS hazard; and bound comparisons by solc's mobile-type rule
   (reject folding when either side exceeds u256/s256 or is fractional
   without a common ufixed shape) rather than folding every comparison.

Each item is probe-backed above; the probes in this doc are the seed lanes.
