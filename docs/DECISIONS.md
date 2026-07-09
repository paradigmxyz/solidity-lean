# Decisions log (autonomous cleanup run)

One dated entry per non-obvious decision taken while executing `ROADMAP.md`.
The run is fully autonomous; where the phases and implementation notes leave a
choice open, the most conservative behavior-preserving option was taken and
recorded here.

## 2026-07-08 — CE-family: constant folder re-derived over signed rationals with solc's resource caps

Acting on `docs/solc-const-eval-env-review.md`. solc's `ConstantEvaluator`
folds constants over signed rationals ℚ (not `Nat`); Solidus's folder gated
several ops on `exactNat?` and lacked unary `~`, over-rejecting a family of
valid constants, and lacked solc's resource caps, over-accepting another
family (and, for base-0/1/−1 exponents, risking a non-terminating import).
All fixes are op-for-op faithful to `ConstantEvaluator.cpp` /
`Types.cpp` / `libsolutil/Numeric.cpp` (thresholds read from source, not
guessed); every folded value was cross-checked against the pinned solc AST.

Differentially-live over-rejects now accepted (folder in `Interface.lean`):

- **CE-1** negative constant exponents. `NumberRat.expRat?` folds `**` over
  `exactInt?`, short-circuits bases 0/1/−1 *before* size checks (so `0**-1 = 0`,
  `4*2**-1 = 2`, `2**-2*16 = 4`), and inverts for negative exponents. The
  checker's `exp` arm no longer requires an unsigned-typed exponent when both
  operands are constant literals (solc types the exponent as `int_const`, not a
  signed integer *type*).
- **CE-2a** unary `~`. Added a `bitNot` arm to `Expr.numberLiteralRat?`
  (`~x = −x−1` on integer rationals): `~5 = −6`, `~(−3) = 2`, `~5 & 0xFF = 250`.
- **CE-3** negative operands in shifts/bitwise. `bitAnd?/bitOr?/bitXor?` fold
  over `exactInt?` via two's-complement (`intBitLand/Lor/Xor`, derived from the
  `Nat` bit ops since Lean core lacks `Int.land`); `shl?` allows a negative lhs;
  `sar?` implements solc's floor rounding (`-7 >> 1 = −4`, not −3) and the
  past-msb `−1`/`0` rule. `>>` (both `shr` and `sar`) maps to SAR, as solc does.
- **CE-4** fractional `%` = `x − trunc(x/y)·y` (`7 % 2.5 = 2`); integer parity
  with `Int.tmod` preserved.
- **CE-5** fractional denominated literals. `literalTy?` gates `unitNumber` on
  `parseUnitNumberRat?` (was the integer-only `…Nat?`), so `0.5 wei * 2 = 1`.
- **CE-6b (non-termination hazard)** removed: the base-0/1/−1 short-circuit in
  `expRat?` returns the value without materializing the exponent, so
  `1**(2**100)`, `0**(10**60)`, `(-1)**(2**100)` compile instantly.

Importer-masked over-accepts now rejected (solc's exact caps):

- **CE-6a** — `fitsPrecisionExp` (per-`**`, 4096-bit), `fitsPrecisionBase2`
  (per-shift), the uint32 exponent/shift bound, the 4096-bit post-op cap
  (`within4096`, on the reduced rational), and the int32 + `fitsPrecisionBase10`
  literal-exponent rule reject `2**5000/2**5000`, `10**1025/…`, `1e2000/…`,
  `(1<<4200)>>4200`, `0<<2**33`. `~0` into an unsigned type fails closed
  (`bitNot` added to `isRawNumberLiteralExpression` +
  `exprIsUntypedNumberLiteralExpression`), matching solc's `int_const −1`
  rejection while `~0` into a *signed* type still folds to −1. Comparisons with
  no common mobile type (`2**300 < 2**301`, `1/2 < 1`) are rejected by a checker
  gate (`Expr.numberComparisonFoldable?`) mirroring solc's `mobileType` rule,
  while `1 < 2` and `1/2 == 0.5` still fold.

Decisions / residue:

- The 4096-bit post-op cap checks the *reduced* rational (gcd-normalized) to
  match solc, which reduces at `makeRational`; `NumberRat` is otherwise
  unreduced.
- `fitsPrecisionBase10`'s `floor(exp·log2 10)` uses an exact 16-digit rational
  for `log2 10` rather than solc's `double`; this can disagree only at the
  (importer-masked) 4096-bit boundary, far from any lane.
- **CE-7** (depth-32 constant-eval limit) and **CE-8** (hex + denomination) are
  left as residue: both are importer-masked (solc rejects first) and neither is
  made easy by the cap machinery. CE-7 needs a constant-eval depth counter;
  CE-8 a scanner-level hex-denomination ban.

Lane `cefamily` (accepts contract imported from the solc AST + 7 solc-rejected
`invalid/` files + 25 named witnesses): `solc_rejects=ok forge=ok lean=ok`,
`forge_interpreter_compare=pass`. Smoke replay + 8 folder-adjacent lanes
(rational-constants, signed-literal-arithmetic, ternary-literal-mobile-type,
exp-by-squaring, compound-exponential-no-error, narrow-arith-widened,
fixed-point-boundary, literal-cast-conversions): all `lean=ok`, no regressions.
## 2026-07-08 — TC1 fixed: ternary `bytesN` common-type conversion in `abi.encode`/`abi.encodePacked`

Acting on `docs/solc-conversions-review.md` (TC1). A conditional `c ? x : y`
whose branches are `bytesN` of DIFFERENT widths takes the ternary's COMMON type
(the wider `bytesN`); solc inserts the implicit `convert_t_bytesM_to_t_bytesN`
on the narrower branch, and because `bytesN` is LEFT-aligned that widening moves
the content into the HIGH bytes (`bytes2 0xaabb` widened to `bytes4` →
`0xaabb0000`, not `0x0000aabb`).

Scope of the actual divergence (verified against pinned solc 0.8.35 + Forge):
- **Return values were ALREADY correct** — `return c ? x : y` routes through the
  typed env path `returnValuesCoreWithReturnTys? → Expr.toCoreAsWithEnv?`, whose
  ternary case lowers each branch to the return type (inserting the
  `fixedBytesCast`). The `f` control lane confirms this.
- **`abi.encode` / `abi.encodePacked` were wrong.** A `return abi.encode(...)` is
  matched by the member-call return case, which falls through to the env-LESS
  `Stmt.toCore?`; there the ABI argument helpers (`Args.toAbiEncode?` /
  `Args.toAbiEncodeSource?`) lower each argument with plain `toCore?` and no
  target type. `annotateAbi` wraps the whole conditional in its then-branch type
  but leaves the branch idents bare (their `abiTy?` is `none`), so no cast is
  inserted and the narrow branch keeps its right-aligned low-byte content.

Fix (`SolidCore/Solidity/Interface.lean`, Solidus-only — solc/Forge untouched):
- `Expr.abiEncodeFixedBytesTernary?` + `…Core?`: detect a `bytesN`-common-type
  conditional ABI argument (seeing through the redundant `bytesN(...)` wrapper
  `annotateAbi` inserts), recompute the true common type from BOTH branches via
  `Ty.commonImplicit?`, and lower each branch to it with the typed env path
  (`Expr.toCoreAsWithEnvBitAware?`), which inserts the `fixedBytesCast`. Gated on
  `Ty.fixedBytesSize?` — integer branches are stored full-width so their widening
  is a value no-op and they keep the exact env-less path (verified no-change).
- `Args.toAbiEncodeWithEnv?` / `Args.toAbiEncodeSourceWithEnv?`: env-carrying ABI
  arg lowering, byte-identical to the env-less helpers for every argument EXCEPT
  the `bytesN` conditional (delegates to `toAbiEncodeArg?`/`toAbiEncodeSourceArg?`
  otherwise; keeps source types so `Tys.packedTopWidths` is unchanged).
- `Expr.toCoreAsWithEnv?` gains `abi.encode`/`abi.encodePacked` cases that use the
  env arg helpers ONLY when `Args.anyAbiEncodeFixedBytesTernary?` finds such an
  argument; otherwise they call `toCoreAsWithEnvDirect?` (the prior behavior).
- The `Stmt.returnValues` dispatcher gains an `abi.encode`/`abi.encodePacked`
  member-call case that, when a `bytesN` conditional argument is present, routes
  the return through `Expr.toCoreAsWithEnv?` (reaching the fix); every other
  `abi.*` return keeps the env-less `Stmt.toCore?` lowering, byte for byte.

The common-type DERIVATION was NOT touched (already solc-consistent, incl. solc's
rejection of `c ? 1 : -1`); only the missing per-branch conversion was inserted.

Lane `ternary-bytesn-common-type` pins the fix differentially: `f` (return),
`enc` (`abi.encode`), `packed` (`abi.encodePacked`) with `bytes4`/`bytes2`
branches, plus an integer-ternary control `g` (uint8/uint256) locking in
no-regression. Forge (pinned solc + EVM) and imported Lean agree `forge=ok
lean=ok`; `smoke_replay.sh` (28 cases) green.

## 2026-07-08 — AGG1/AGG2 fixed, AGG3 locked: storage aggregate layout + bytesN mapping-key hashing

Acting on `docs/solc-storage-aggregate-layout-review.md`. All three verified
end-to-end (pinned solc 0.8.35 + Forge `vm.load` ground truth paired with a Lean
witness that reads the same abstract storage words via `State.loadSlot` at the
solc-computed slots). Three Forge-paired lanes added to the manifest.

- **AGG1 (fixed) — `mapping(bytesN => V)` key hashed right-aligned.** solc hashes
  the LEFT-aligned stack form (`FixedBytesType::leftAligned = true`,
  Types.h:701-702), so the slot is `keccak256(h(key) . slot)` with `h(key)` in
  the high n bytes; our internal bytesN convention is right-aligned, so every
  entry landed at the wrong slot. Fix: `mappingStorageSlotForKey`
  (Interpreter.lean) gains a `Ty.fixedBytes n` case that shifts the low 8n bits
  into the high bytes of the preimage word before hashing (n = 32 is a no-op).
  Lane `aggregate-bytesn-mapping-key` also pins that the right-aligned (pre-fix)
  preimage stays empty and a uint32 value-key control stays right-aligned.

- **AGG2 (fixed) — contract/interface-typed storage members had no lowering.**
  The `Ty.user` case fell through to `none`: contract-typed vars never packed,
  a struct with a contract-typed field got `layout? = none` (span collapsed to
  1, shifting later members), and `mapping(ContractType => V)` took the FNV
  fallback. Fix: at storage-lowering time a residual `Ty.user` (all UDVT/enum/
  struct users already resolved away) is a contract path = a 20-byte address
  (`ContractType::storageBytes() = 20`, Types.h:978), so it is added to
  `Ty.storagePackedBytes?` (=> 20) and `Ty.toCoreStorageWord?` (=> address) in
  Interface.lean. That single change fixes AGG2a (packing), AGG2b (struct span)
  and AGG2c (mapping-key keccak path) together. Lane `aggregate-contract-member`
  drives the witness through the whole imported source unit
  (`CheckedInput.callContract` on `importedSourceUnit`) so the sibling interface
  is in type-context scope — note that the single-contract `checkedOwnCallState`
  entry used by simpler lanes checks the target in isolation and would reject the
  external interface type.

- **AGG3 (locked, no code change) — fixed-array slot span.** The audit flagged
  the straddling span as in-flight-related; the current tree already computes
  `span = natCeilDiv size (floor(32 / widthBytes))` (Interpreter.lean:1406), the
  correct solc formula (`uint40[32]` => 6 slots, not the old
  `ceil(size*width/32) = 5`). Lane `aggregate-array-span` locks it so the
  trailing scalar's slot (7, not 6) is a differential regression sentinel.

Smoke replay (`scripts/smoke_replay.sh`) + the three lanes: 31 cases,
`forge_interpreter_compare=pass`, all three `lean=ok`, no regressions.
## 2026-07-08 — FB1 fixed: `bytesN <<` and `~bytesN` re-clean to the byte lane

`docs/solc-fixedbytes-ops-review.md` FB1 (wrong-VALUE family, Fable-confirmed).

**The bug.** solc stores `bytesN` **left-aligned** and wraps every `bytesN <<`
and `~bytesN` result in `cleanup_t_bytesN` (keep only the top-N-byte lane).
Solidus stores `bytesN` **right-aligned** (`SolidCore/Solidity/Interpreter.lean:468-475`),
so under its convention `<<` and `~` are exactly the ops that push meaningful
bits *above* the low N-byte lane — they must be masked to `2^(8*N)` afterward.
Solidus applied no such mask: runtime `shlWord`/`notWord` are raw 256-bit ops
(`Interpreter.lean:5511`, `~5658`), and `Ty.implicitCleanupCore?` inserted a
truncating cast only for `uint`/`int`, letting `fixedBytes` fall through with no
cleanup. Escaped bits are dropped by ABI-encode/return and index access (so
`return b << 4;` alone agreed) but became observable under comparison, a
following shift/bitwise op, or `&`/`|`/`^`. Three confirmed divergences (solc via
`--ir`): `(b<<4)>>4` on `bytes1(0xff)` → solc `0x0f`, Solidus `0xff`;
`(b<<4)==bytes1(0xf0)` with `b=0xff` → solc `true`, Solidus `false`;
`(~b)==bytes1(0xf0)` with `b=0x0f` → solc `true`, Solidus `false`.

**The fix (`SolidCore/Solidity/Interface.lean`).** The lane mask is
`fixedBytesCast size size` — it takes the low `size` bytes (a no-op for
`size = 32`, so full-width `bytes32` never over-masks). Because the env-less
`toCore?` shift/bitwise lowering is type-blind, a *nested* `<<` (divergence 1's
`(b<<4)>>4`) needs a typed recursive walk, added as
`Expr.toCoreFixedBytesBitOp?`: it lowers a `bytesN` shift/bitwise subtree,
wrapping every `<<` and `~` result in `fixedBytesCast size size`, recursing
through `>>`/`&`/`|`/`^` (no extra mask — those keep in-lane values in-lane) so a
nested `<<`/`~` beneath them is still cleaned, and delegating leaves to the
ordinary typed lowering at `bytesN size`. It is dispatched via
`Expr.toCoreAsWithEnvBitAware?` from (a) the top of `Expr.toCoreAsWithEnv?`
(returns/assignments/args — divergence 1) and (b) `Expr.binaryToCoreWithEnvTyped?`
operand lowering (comparison/bitwise operands — divergences 2, 3). As
defense-in-depth for any raw top-level `bytesN <<` reaching the cleanup helper,
`Ty.implicitCleanupCore?` also gained a `fixedBytes` arm that masks a left-shift
result (and leaves `>>` untouched). `>>` alone, index access, and ABI-encode
were verified unchanged (they already took the low N bytes and agreed).

**Pinned.** Three Forge-paired lanes (`fixedbytes-shl-shr-mask`,
`fixedbytes-shl-eq`, `fixedbytes-not-eq`), one per divergence, each a minimal
contract whose public function returns the observably-diverging value; the
differential harness (pinned solc 0.8.35 + Forge + imported Lean) now agrees
`forge=ok lean=ok` on all three.
## 2026-07-08 — CS1 fixed: selfdestruct performs the balance transfer

Gap CS1 (missing effect / wrong-value) in `Stmt.selfdestruct`
(`SolidCore/Solidity/Interpreter.lean`).

**solc-confirmed behavior (probed pinned solc 0.8.35 + Foundry).**
`selfdestruct(recipient)` transfers the contract's ENTIRE balance to
`recipient` unconditionally — this is independent of EIP-6780, which only
governs whether the account is DELETED (a same-transaction-created account is
deleted). Probe: a `Bomb` funded with 100 that `selfdestruct(sink)`s leaves
`address(bomb).balance == 0` and credits `sink` by 100; the
`selfdestruct(self)` edge ends at balance 0 (same-tx account deleted).

**The bug.** The interpreter faithfully recorded the selfdestruct facts
(`from`, `recipient`, the 6780 delete flag) via `State.recordSelfdestruct` but
moved NO balance — self was never zeroed and the recipient never credited
(asymmetric with call/create value transfer, which is modeled via the
responder's postWorld debit).

**The fix (`~:2525-2590`, `~:8781`).** Added `creditWorldAccount` /
`setWorldAccountBalance` open-world helpers and `State.selfdestructTransfer`:
on selfdestruct, snapshot the open world, credit the recipient by the self
balance, THEN zero self (both in the world and the `selfBalance` field).
Crediting before zeroing makes the self-destruct-to-self edge net to 0
(matching the EVM's deletion of the same-tx account) while a distinct recipient
is credited the full balance. The 6780 delete flag is still recorded, from the
PRE-transfer created-accounts set (unchanged).

**Forge-verified observable / lane.** New lane
`tests/forge-harness/selfdestruct-balance` (`SelfdestructBalance`). Forge
ground truth: transfer to a distinct sink → self 0, sink +100; self-recipient
edge → 0. The paired Lean witnesses import the same source, drive
`blow`/`blowSelf` under an empty responder, and assert the post-selfdestruct
balances (`selfBalance == 0`, recipient credited, self-recipient edge 0) plus
the recorded selfdestruct effect. `lake build SolidCore` green; smoke replay
green with identical values (28/28 `lean=ok`); lane `forge=ok lean=ok
compare=pass`; the selfdestruct-touching `terminal-statements` lane still
`lean=ok`.

## 2026-07-08 — CB1 + A2 fixed: try/catch dispatch by revert kind

Gap CB1 (wrong-branch + wrong-value) and gap A2 (dispatch order), both in the
try/catch clause matcher (`SolidCore/Solidity/Interpreter.lean`).

**solc-confirmed behavior (probed pinned solc 0.8.35 + Foundry).** solc's
`tryDecodeErrorMessage` (YulUtilFunctions.cpp:4676-4713,
IRGeneratorForStatements.cpp:3460-3521) treats revert data as `Error(string)`
ONLY when `returndatasize() >= 0x44` (68 bytes: selector + head-offset word +
length word) AND it decodes as a standard ABI string; otherwise the
`Error(string)` clause does NOT match. A callee reverting with a hand-crafted
36-byte `Error`-selector‖32 zero bytes routes to `catch (bytes …)` with the
raw 36 bytes (NOT `Error` with reason `""`); a well-formed `Error("x")`
(>= 68 bytes) routes to `catch Error(string)` with `"x"`; a `Panic(0x12)`
routes to `catch Panic`. Dispatch is by the revert KIND, so a revert whose
kind has no typed clause falls through to the byte / catch-all clause
regardless of clause source order (a `Panic` with no `Panic` clause →
`catch (bytes …)`).

**The bug.** `TryCatchClause.match?`/`findMatch?` re-derived the `Error` match
with the interpreter's ABI codec, whose structural minimum is 36 bytes
(selector + one word). A 36-byte `Error`-selector‖zeros payload therefore
matched the `Error(string)` clause with reason `""` (should route to
`catch (bytes)`), and matching walked the clauses in source order taking the
first structural match rather than dispatching by kind.

**The fix (`~:7429-7510`).** Added `RevertKind` + `revertClassify`: an
`errorString` classification now requires `raw.length ≥ 68` AND a successful
standard decode; `panic` requires `raw.length ≥ 36` AND a successful decode;
everything else is `lowLevel`. Rewrote `TryCatchClause.findMatch?` to dispatch
by that kind — run the matching typed clause if present, else fall through to
the `catch (bytes …)`/`catch { }` clause, else propagate — independent of the
clauses' written order.

**Forge-verified observable / lane.** New lane
`tests/forge-harness/catch-dispatch-by-kind` (`CatchDispatch` + assembly
reverters kept in a separate `Reverters.sol` so the Lean-imported caller stays
assembly-free). Forge ground truth: 36-byte Error+zeros → `catch(bytes)`
(tag 4, len 36); `Error("x")` → `catch Error` (tag 2, "x"); `Panic` →
`catch Panic` (tag 3); custom error → `catch(bytes)`; `Panic` with no `Panic`
clause → `catch(bytes)` (tag 4). The paired Lean witnesses import the caller
and drive it under a responder supplying each revert payload, asserting the
identical routing. `lake build SolidCore` green; smoke replay green (the one
non-`ok` case was a sibling-contention timeout, verified `lean=ok` in
isolation); lane `forge=ok lean=ok compare=pass`.

## 2026-07-08 — EO1 fixed: external-call argument/option evaluation ORDER

Gap EO1 (wrong-ORDER soundness bug) in the external-call boundary.

**solc-confirmed behavior (probed pinned solc 0.8.35 + Foundry).** For
`base.call{gas: g(), value: v()}(payload)` solc evaluates: the base/target
expression FIRST, then the FunctionCallOptions in their WRITTEN order
(gas-vs-value by whichever option is written first), then the calldata argument
LAST. A side-effecting order-trace (`t()`,`g()`,`v()`,`p()` each appending a
digit) gives `1234` for written order `{gas, value}` and `1324` for
`{value, gas}` — identically for the expression low-level `.call` and the
statement-form `try` call.

**The bug (`SolidCore/Solidity/Interpreter.lean`).** Two divergences:
1. The EXPRESSION low-level call (`Expr.lowLevelCall`, ~:6411) evaluated the
   component list as `[target, calldata, value, gas]` and IGNORED the
   `gasFirst` flag entirely. Worse, it threaded the ambient child-eval order
   (`yulCompatible` ≈ right-to-left) into that list, so the components came out
   scrambled (observed order-trace `321…`, calldata evaluated first, target
   last).
2. The STATEMENT external call (`Stmt.tryExternalCall`, ~:8419) respected
   gas-vs-value but evaluated the calldata BEFORE the options.

**The fix.** Both paths now evaluate the components strictly in solc order:
target, then options in written order (`gasFirst ? gas,value : value,gas`),
then calldata. The expression path was rewritten to evaluate each component
sequentially (rather than through the ambient-ordered `evalList`), so the
FIXED top-level order is imposed while each component's OWN inner children keep
the ambient child-eval order. The statement path moved the option evaluation
ahead of the calldata evaluation.

**Forge-verified observable / lane.** New lane
`tests/forge-harness/call-option-eval-order` (`CallOptionEvalOrder`): four
functions build the order-trace in a single storage slot (each of
target/gas/value/calldata appends its digit via an embedded assignment
expression). Forge ground truth: `exprGasFirst = tryGasFirst = 1234`,
`exprValueFirst = tryValueFirst = 1324`. The paired Lean witnesses import the
same source and, under a fail-open responder, assert the source-interpreter
returns the identical order-trace. Before the fix the expression witnesses
returned a scrambled trace (and the statement witnesses `1423`-style); after,
all four return `1234`/`1324`. `lake build SolidCore` green; smoke replay green
with identical values; lane `forge=ok lean=ok compare=pass`.

## 2026-07-08 — DL1 fixed: storage / constructor / initializer order = reverse C3

`docs/solc-implementation-divergences-7.md` DL1 (wrong-VALUE + wrong-ORDER
soundness bug).

**The bug.** Solidus laid out contract storage AND ran base constructors +
inline state-variable initializers in a naive left-to-right DFS post-order
keep-first-dedup traversal (`ContractDecl.storageOrder?` /
`storageOrderWithFuel?`, `SolidCore/Solidity/Interface.lean`). solc lays out
storage — and runs constructors/initializers — in `reverse(linearized
BaseContracts)` = reverse C3 = most-base-first (Types.cpp:2168-2172;
C3 in NameAndTypeResolver.cpp:422-497, pinned solc v0.8.35). The two orders
diverge whenever a contract lists a direct base that is ALSO an indirect base.
Repro `contract X{uint x;} contract Y{uint y;} contract M is X,Y{uint m;}
contract Z is Y,M{uint z;}`: pinned solc `--combined-json ast` gives
`C3(Z) = [Z, M, Y, X]`, so storage = reverse = `[X, Y, M, Z]` → x@0, y@1, m@2,
z@3. The old DFS produced `[Y, X, M, Z]` → y@0, x@1 (x/y SWAPPED) — wrong slot
(wrong read/write VALUES + wrong external layout) AND wrong constructor/
initializer execution ORDER.

**The fix (`SolidCore/Solidity/Interface.lean`).** Solidus already computes the
correct C3 linearization for DISPATCH (`ContractDecl.dispatchOrder?`, most-
derived-first). Storage order is simply its reverse. Deleted
`ContractDecl.storageOrderWithFuel?` and redefined

```
def ContractDecl.storageOrder? (contracts) (decl) : Option (List ContractDecl) :=
  (ContractDecl.dispatchOrder? contracts decl).map List.reverse
```

Single touch point: every consumer (slot assignment via `stateVars :=
concatMapList directStateVars storageOrder`; constructor/initializer composition
via `pieces := mapOption … storageOrder`; transient via `stateVars.filter
isTransient`; `findImmediateDerivedInOrder?`) flows from `storageOrder?`, and all
require only a most-base-first topological order, which the reverse preserves.
Verified on the repro that `dispatchOrder?` = solc's C3 `[Z,M,Y,X]`, so
`reverse` = `[X,Y,M,Z]` matches solc slot-for-slot.

**Before → after slots (repro Z).** before (DFS): y@0, x@1, m@2, z@3;
after (reverse-C3): x@0, y@1, m@2, z@3 — matches pinned solc `--combined-json
storage-layout`. Constructor order: before ran Y before X; after runs X before Y
(most-base-first), confirmed via an order-sensitive `trace` accumulator (correct
1234 vs buggy 2134 on the paired shape).

**Coincidence / no-regression checks.** Linear chains and simple diamonds have
DFS = reverse-C3, so they are unaffected (smoke stayed green, identical values).
Transient storage and cross-boundary packing inherit the same corrected
traversal; pinned-solc probe confirms solc packs across the contract boundary in
reverse-C3 order (e.g. `y1` from `Y` and `m1` from `M` share one slot), which the
fix reproduces (within-contract var order unchanged).

**Lane.** `tests/forge-harness/storage-order-linearization` (manifest case
`storage-order-linearization`): the shared direct+indirect base repro (`Dl1ShZ is
Dl1ShY, Dl1ShM` where `Dl1ShM is Dl1ShX, Dl1ShY`) plus a linear control
(`Dl1LinC`) and simple-diamond control (`Dl1DiaG`). Asserts each var's raw slot
(Lean `state.loadSlot` / Forge `vm.load`) AND the constructor-order `trace`
side-effect, Forge-paired. Harness: `forge=ok lean=ok compare=pass`.

**Gates.** `lake build SolidCore` green; `scripts/smoke_replay.sh` green
(28 cases, all `lean=ok`, compare=pass, identical values); inheritance/storage/
constructor lanes re-checked lean-only green (openzeppelin-erc20 needed
`--timeout 900` for elaboration, then `lean=ok`). No storage-order sub-case
remains.
## 2026-07-08 — M1/M2/M3/M4 fixed: memory reference-type alias/copy soundness

Four memory soundness bugs from `docs/solc-memory-semantics-review.md` (M1) and
`docs/solc-memory-semantics-review-2.md` (M2/M3/M4). M1/M2/M3 are wrong-alias
(memory→memory reference-type assignment deep-copied where solc pointer-aliases);
M4 is a spurious revert (abi.encode/keccak of ref-nested nested-dynamic memory).

**solc ground truth (pinned solc 0.8.35 + Forge, all PASS).** Every
reference-type memory assignment is a pointer copy
(`libsolidity/codegen/ExpressionCompiler.cpp` `visit(Assignment)` →
`MemoryItem::storeValue`): a memory-ref RHS (ternary, array element, struct
member, plain var), each tuple-destructuring component, and a memory ref stored
into a memory aggregate element/field all ALIAS the source; a later mutation
through either name is visible through the other. abi.encode/keccak256 of a
`bytes[]` / `uint[][]` / `string[]` memory local encodes without reverting.
Value types still copy; storage↔memory still deep-copies. Probed and confirmed
in `tests/forge-harness/memory-alias-fixes` (Forge PASS).

**Root cause (M1/M2/M3, one defect).** The store paths already ALIAS a bare
`Value.memoryRef` (`Runtime.memoryStoreValue`/`assignLocal?`/`storeMemory?`,
`Interpreter.lean:~1187/1251`), but assignment RHS evaluation *dereferenced* a
memory ref to a bare object, and the store paths then reallocate a fresh cell for
a bare object → deep copy. The fix threads memory-ref values through as
`Value.memoryRef` so the existing alias paths fire.

**Alias-vs-copy boundary (the decision).** A ref-preserving evaluation is used
ONLY where the assignment TARGET is a memory location; storage/immutable targets
and value-type locals keep ordinary (dereferencing/copying) evaluation, so
storage↔memory and value-type semantics are unchanged. The memory-target test is
`LValue.wantsMemoryRefRhs` (`Interpreter.lean`): true for a memory-ref local
(`lookupMemoryRef?`) or a memory aggregate element (an `index` whose base is not a
storage/storage-alias root); false otherwise.

**Fix (`SolidCore/Solidity/Interpreter.lean`).**
- M1: `Expr.memoryRefOrValueWithRuntimeOrderFuel` gains an `Expr.ternary` arm
  (recurse into the taken branch) and is made total (never `none,none`), so the
  declaration path (`Stmt.memoryVarDecl`) and internal-call arg temps alias
  ternary RHSs. New `Expr.evalMemoryRefPreservingWithRuntimeOrder` yields the
  `memoryRef` pointer for memory-ref exprs. `Stmt.assign` evaluates the RHS
  through it, gated by `wantsMemoryRefRhs`, covering ternary/index/member RHS into
  a memory var. (Memory-returning internal calls and index/var already aliased
  via the reference-signature return path — unchanged.)
- M2: `Stmt.assignTuple` with an `Expr.tuple` RHS evaluates each component
  ref-preservingly (per-target gate) via `Expr.evalTupleComponentsRefPreserving`,
  all components before any write, so destructuring/declaration alias and
  `(a,b)=(b,a)` performs a genuine pointer swap.
- M3: subsumed by the `Stmt.assign` change — a memory ref flows as `memoryRef`
  into `ResolvedLValue.valueIndex.write`, whose `memoryStoreValue` already
  aliases a `memoryRef` unchanged.
- M4: the `abi.encode` / `abi.encodeWithSelector` / `abi.encodePacked` /
  `keccak256` arms deep-materialize their arguments (`derefMemoryValuesDeep` /
  `derefMemoryValueDeep`) before encoding, so ref-nested memory elements resolve
  to concrete value trees instead of hitting an unmatched `memoryRef` → revert.

**Lanes (`tests/forge-harness/memory-alias-fixes`, ADDED — corpus frozen).**
Forge-paired: M1 ternary decl/assign + index + member alias; M2 tuple + swap +
decl; M3 into-field + into-element; M4 non-revert + solc byte-lengths for
`bytes[]`/`uint[][]`/`string[]` (`abi.encode` length 256 / 288); plus value-copy
controls (`valueCopyControl`, `valueElementCopyControl`) and storage↔memory
independence controls (`storageToMemoryIndependence`, `memoryToStorageIndependence`).
`case_result=memory-alias-fixes forge=ok lean=ok`. `scripts/smoke_replay.sh`
green (28 cases, `forge_interpreter_compare=pass`) — no over-aliasing regression.

**Residual (unfixed, importer-masked / niche).** `abi.encode` of a *struct*
value and struct construction with a call-argument field are untranslatable by
the solc-AST importer (pre-existing, unrelated to the memory model) — so the M4
struct-with-dynamic-field shape is not corpus-testable here (the interpreter arm
handles it via the same deep-deref). `string(bytes)`/`bytes(string)` reinterpret
aliasing (M1-family, niche) is not covered — a conversion RHS is neither
`var`/`index`/`ternary`, so it still deep-copies; flagged for a follow-up.
try/catch/modifier end-to-end memory aliasing inherits M1/M2/M3 and was not
probed end-to-end.

## 2026-07-08 — UF1/UF2/UF3 fixed: `using ... for T global` legality

`docs/solc-implementation-divergences-4.md` UF1 (live differential over-reject),
UF2/UF3 (importer-masked over-accepts). All three concern
`TypeChecker::endVisit(UsingForDirective)`.

**UF1 — non-UDVT `global` target over-rejected (COMPLETENESS, live edge).**
solc (`libsolidity/analysis/TypeChecker.cpp:4006-4021`): a file-level
`using ... for T global` admits any T whose `Type::typeDefinition()` is non-null
and defined in the same source unit. `Type::typeDefinition()` is overridden only
for `StructType`, `EnumType`, `UserDefinedValueType` (`libsolidity/ast/Types.cpp:
2490/2630/2703`) — so **struct, enum, UDVT** are legal `global` targets; a
built-in / elementary type raises 8841 and a cross-file type raises 4117. A
**contract** type has no `typeDefinition()` and is rejected (8841) — the round-4
doc's claim that a contract is a legal target was WRONG; pinned-solc probe
`using {f} for D global;` (D a contract) → 8841. Solidus
(`SolidCore/Solidity/TypeCheck.lean` `UsingDecl.checkFileLevel`) gated the
`global` target through `isUserValueTypePath`, admitting only UDVTs and rejecting
struct/enum globals — a mainstream library idiom.

**Fix** (`TypeCheck.lean` `UsingDecl.checkFileLevel`): the `global` target gate
now accepts `isStructPath || isEnumPath || isUserValueTypePath`. The UDVT-only
restriction stays where solc keeps it — for OPERATOR bindings, enforced
separately in `UsingFunction.check` (unchanged), so an operator binding on a
struct global still rejects (probe: "Operators can only be implemented for
user-defined value types"). Built-in and cross-file globals still reject.

**UF2 — operator binding params must BOTH be the target type (masked
over-accept).** solc (`TypeChecker.cpp:4158-4186`, error 1884): an operator
function's parameters must ALL equal the target UDVT (both params for binary, the
one param for unary) and it must return the operator's result type. Solidus
`FunctionSig.matchesUserDefinedOperatorDecl` required only `hasParamTy` (target
in ≥1 position), wrongly accepting `f(T, uint) as +`. **Fix**: replaced
`hasParamTy` with `sig.params.all (· == targetTy)` (length already pinned to 2/1;
return-type match was already enforced). Probe: `addMixed(T,uint) as +` → 1884;
`add(T,T) as +` accepts.

**UF3 — duplicate operator binding rejected at the directive (masked
over-accept).** solc (error 4705): binding the same operator for the same type
more than once in visible scope is a directive-level error. Solidus caught it
only lazily at a use site. **Fix**: new `UsingDecls.checkNoDuplicateOperator
Bindings` collects every `(operator, targetTy)` from all file-level using
directives and rejects a repeat; wired into `SourceUnit.checkWithEvmVersion`
after `checkSourceUsingDecls`. Operator bindings must be `global` (file
level), so the file-level scan covers every binding in scope. Probes: same op
same type across one or two directives → 4705; same op different types, or
different ops same type → accept.

**Boundary verified**: new manifest case `using-for-global-nonudvt`.
- Forge accept + VALUE lane (pinned solc 0.8.35): `using {doubled, plus} for
  Amount global;` on a STRUCT — `computeDoubled(21)==42`, `computePlus(21,8)==29`
  equal Forge; imported Lean `importedGlobalUsingMemberValues` pins the same
  words. The imported source also carries `using {rank} for Color global;` on an
  ENUM whose acceptance is pinned by `importedContractAccepted` and the common
  checker (enum-target member DISPATCH at execution is a pre-existing
  interpreter-layer gap unrelated to this typecheck fix, so the value lane
  exercises the struct only).
- solc-reject fixtures (all confirmed rejected by pinned solc AND now by the
  common checker): `invalid/OperatorOnStructGlobal.sol` (UF1 neighbor),
  `invalid/BuiltinTargetGlobal.sol` (UF1 neighbor), `invalid/OperatorMixedParams
  .sol` (UF2), `invalid/DuplicateOperatorBinding.sol` (UF3).
- Lean witness `usingForGlobalNonUdvtDisciplineMatches`
  (`SolidCore/Witness/TypeCheck.lean`): struct/enum/library-form globals accepted;
  operator-on-struct, built-in-global, mixed-param and first-param operator
  functions, and single- and split-directive duplicate bindings all rejected;
  correct UDVT operator bindings (`globalUsingPriceOperatorAccepted`) still
  accepted.

Must-hold neighbors: `library-type-uses`, `udvt-operator-dispatch`,
`narrow-udvt-arithmetic` stay green in smoke (Lean=ok, compare=pass).

**Lane**: new manifest case `using-for-global-nonudvt` — Forge accept+value lane +
4 solc-reject fixtures + common-checker witness. UF1/UF2/UF3 marked Fixed.
## 2026-07-08 — V1 Fixed: calldata-slice OOB reverts with EMPTY data (not Panic 0x32)

`docs/solc-implementation-divergences-6.md` V1 (CONFIRMED, SOUNDNESS wrong-value,
the campaign's first wrong-VALUE bug): a calldata slice `a[i:j]` with `i > j` or
`j > a.length` must revert with **empty data** (`revert(0, 0)`) in solc's default
(non-debug) mode; Solidus instead reverted with **Panic(0x32)** (36-byte
returndata), reusing the array-INDEX-access OOB constant for the slice-RANGE check.

**solc rule** (`libsolidity/codegen/YulUtilFunctions.cpp:2523-2539`, the slice
bounds check `if gt(startIndex, endIndex) …` / `if gt(endIndex, length) …`): both
route to `revertReasonIfDebugFunction`, whose body (`:4598-4605`) under
`RevertStrings::Default` (< Debug) emits literally `revert(0, 0)` — empty
returndata, no `Panic`. `Panic(0x32)` is emitted only for a regular array/bytes
**index** access `a[k]` OOB (a different Yul helper), never for a slice range.

**Fix** (one edit, `SolidCore/Solidity/Interpreter.lean`, `sliceListByWords?`): the
out-of-range arm now returns `Except.error RevertData.empty` (the existing empty
`revert(0, 0)` constructor, encoded to 0 bytes by `Contract.encodeRevertData?`
in `ABI.lean:485`) instead of `RevertData.indexOutOfBounds` (= `panic 0x32`). The
in-bounds value path `(drop start).take (stop - start)` and the array/bytes INDEX
access path (`Value.index?`/`setIndex?`, still `RevertData.indexOutOfBounds`) are
untouched.

**Boundary verified** (pinned solc 0.8.35 + Forge): lane `calldata-slice-oob`
low-level `.call`s `slice(bytes,uint256,uint256)` with `(1,100)` and `(3,1)` →
`success == false` AND `returndata.length == 0` (empty revert); an in-bounds
`slice(input,1,4)` returns the correct sub-array; and `indexAt(bytes,uint256)`
with an OOB index → `returndata.length == 36` equal to
`abi.encodeWithSignature("Panic(uint256)", 0x32)` (Panic 0x32 unchanged). Lean
imports the same contract: OOB slice → `CallResult.reverted _ RevertData.empty`,
in-bounds → `Value.bytes [20,30,40]`, OOB index → `RevertData.panic 0x32`.

**Lane**: new manifest case `calldata-slice-oob` (forge-paired: empty-revert
observable + in-bounds value + index-OOB Panic(0x32) neighbor) + solc_import +
Lean evals. Harness: `forge=ok lean=ok forge_interpreter_compare=pass`. No
regression: smoke green, `entrypoint-slice-control` (in-bounds slices) and
`memory-allocation-overflow` (Panic 0x41) `lean=ok`.

## 2026-07-08 — A1 Fixed: type(AbstractContract).interfaceId now lowers

`docs/solc-implementation-divergences-6.md` A1 (COMPLETENESS wrong-reject,
differentially-live): solc accepts and computes `type(T).interfaceId` for any
NON-deployable contract — an interface **or an abstract contract** — but Solidus
failed to LOWER it for an abstract contract (`interfaceIdEntry?` returned
`some none` for non-interfaces, and `Ty.typeInfoExpr?` had no `interfaceId` arm),
rejecting a program solc compiles — despite the (post-lowering) typechecker
already accepting it (`TypeCheck.lean:5486-5499`).

**solc rule** (`Types.cpp:4271-4285`: member exposed iff `!canBeDeployed()`;
`ContractDefinition::interfaceId()` `AST.cpp:315-321`): `interfaceId` = XOR of the
4-byte selectors of `interfaceFunctionList(false)` — the externally-visible
functions AND public state-variable getters declared DIRECTLY in the contract
(`false` excludes inherited); internal/private functions excluded. Probe (pinned
solc + Forge): an abstract contract with external `foo`/`bar` and public
`stateVar` → `interfaceId = sel(foo) ^ sel(bar) ^ sel(stateVar())`; an internal
function does NOT contribute; a concrete deployable contract has no `.interfaceId`.

**Fix** (one edit, `SolidCore/Solidity/Interface.lean`): `isNonDeployable :=
isInterface || decl.abstract` now gates `interfaceId?`/`interfaceIdEntry?` (so the
`interfaceIdEnv` includes abstract contracts and `resolveInterfaceIds` folds them
to a `bytes4` literal — no `Ty.typeInfoExpr?` arm needed). `interfaceId?` was
generalized past the interface-only shortcut: it XORs the selectors of the
externally-visible **functions** (`FunctionDecl.isInterfaceFunction` — ordinary
function, not internal/private) AND the public state-variable **getters**
(`StateVarDecl.selectorEntry?`), matching `interfaceFunctionList(false)`. For an
interface the getter fold is vacuous and every function is external, so the
interface path (F2) is byte-for-byte unchanged.

**Boundary verified** (pinned solc 0.8.35 + Forge): lane `abstract-interface-id`
— `type(AbstractLedger).interfaceId` (external `transfer`/`balanceOf`, public
`totalSupply`, internal `_settle`) == `0xc1b31357` ==
`sel("transfer(address,uint256)") ^ sel("balanceOf(address)") ^ sel("totalSupply()")`;
pinned solc rejects `type(Deployable).interfaceId` on a concrete contract
(`invalid/ConcreteInterfaceId.sol`, "Member \"interfaceId\" not found"). Lean now
LOWERS the source unit (`importedContractAccepted`) and `checkedCallWordMatches`
of `abstractLedgerId()` == `0xc1b31357`.

**Lane**: new manifest case `abstract-interface-id` (forge accept lane + concrete
`solc_rejects` + solc_import + Lean accept/value evals). Harness:
`solc_rejects=ok forge=ok lean=ok forge_interpreter_compare=pass`.

## 2026-07-08 — PK1 fixed: abi.encodePacked of a nested static array

`docs/solc-implementation-divergences-3.md` PK1 (CONFIRMED, live differential
edge): solc **accepts** `abi.encodePacked` of a nested STATIC array whose
ultimate element is a static value type (`uint[2][3]`, `uint[2][]`,
`uint[2][2][2]`), rejecting only an array whose *base/element* is itself a
dynamically-sized array. Solidus over-rejected all nested arrays.

**solc rule** (`libsolidity/analysis/TypeChecker.cpp:2166-2174` gate on
`typeSupportedByOldABIEncoder`, defined `:55-68`): an array is packed-supported
iff its base is supported AND the base is not `(Array && isDynamicallySized)`.
Recurses on base; structs rejected. Probe (pinned solc 0.8.35): `uint[2][3]`,
`uint[2][]`, `uint[2][2][2]`, `bytes32[2][2]` ACCEPT; `uint[][3]`, `uint[2][][2]`,
`bytes[]`, `string[]` REJECT (9578 "Type not supported in packed mode").

**Fix** (two edits, `gap/round3-pk1-cl1`):
- `SolidCore/Solidity/TypeCheck.lean` `Ty.isAbiEncodePackedArrayElementShape`
  gained a `Ty.array element size` case: accept iff `size = some _` (static inner
  dimension) and recurse on `element`; a `none` (dynamic) inner dimension stays
  rejected. This is exactly solc's "base must not be a dynamically-sized array"
  boundary, applied recursively.
- `SolidCore/Solidity/Interpreter.lean` `abiEncodePackedArrayElement?` now
  recurses into a `fixedArray` element (padding each innermost value to a 32-byte
  word in-place, matching solc's "array elements are padded but encoded
  in-place"); `dynamicArray`/`tuple` elements stay unencodable (rejected upstream
  by the type-shape check).

**Boundary verified**: Forge lane `packed-nested-static-array` (pinned solc
0.8.35) — `packMatrix(uint8[2][2])` / `packDynamicOuter(uint8[2][])` equal solc's
own `abi.encodePacked` and are 128 bytes (4 words). Lean value witnesses
`abiEncodePackedNestedStaticArrayValueMatches` /
`abiEncodePackedDynamicOuterStaticInnerValueMatches` pin the same padded bytes.
Must-hold neighbors: `abiEncodePackedStaticElementArrayAccepted` (`uint8[]`) and
`badAbiEncodePackedNestedArrayRejected` (`uint[][]`) unchanged. Over-accept guard:
`invalid/PackedDynamicInnerArray.sol` (`uint8[][3]`) — solc-reject fixture, Lean
witness `abiEncodePackedDynamicInnerArrayRejected`.

**Lane**: new manifest case `packed-nested-static-array` — forge accept lane +
two solc-reject fixtures (PK1 dynamic-inner, CL1 bare-modifier) + solc_import +
Lean evals. Harness: `solc_rejects=ok forge=ok lean=ok forge_interpreter_compare=pass`.

## 2026-07-08 — CL1 fixed: bare modifier-style base-constructor call rejected

`docs/solc-implementation-divergences-3.md` CL1 (CONFIRMED, importer-masked
acceptance-oracle over-accept): solc errors 1563 on a bare modifier-style
base-constructor call (`constructor() Base {}`, no argument list); it must be
`Base()` (or `Base(args)` in the inheritance list). Solidus accepted the bare
form because `ModifierInvocation` could not distinguish solc's `arguments == null`
(bare) from `[]` (`Base()`).

**solc rule** (`libsolidity/analysis/ContractLevelChecker.cpp:366-382`,
`checkBaseConstructorArguments`): for each modifier on a constructor that resolves
to a base contract, `!modifier->arguments()` (null arg list) is **always** a 1563
error — independent of whether the base has a constructor or how many parameters
it takes. Probe (pinned solc 0.8.35): bare `Base` REJECT for base-with-ctor,
base-without-ctor, and base-ctor-with-params; `Base()` and inheritance-list
`Base(args)` ACCEPT.

**Fix** (`gap/round3-pk1-cl1`):
- `SolidCore/Solidity/Ast.lean`: `ModifierInvocation` gained `hasArgList : Bool
  := true` (default `true` keeps hand-built ASTs behaving like an explicit arg
  list).
- `scripts/solc_ast_to_lean_source.py`: emits `hasArgList := isinstance(arguments,
  list)`, preserving solc's null-vs-`[]` distinction.
- `SolidCore/Solidity/TypeCheck.lean` `ModifierInvocation.check`: a
  base-constructor modifier with `hasArgList = false` is rejected ("modifier-style
  base constructor call without arguments"), before the arg-typechecking path.

**Boundary verified**: this is importer-masked (solc emits no AST for the rejected
program), so it is validated via the Lean typechecker directly. Witnesses (differ
ONLY in `hasArgList`): `bareModifierBaseConstructorRejected` (bare, REJECT) vs
`parenModifierBaseConstructorAccepted` (`Base()`, ACCEPT). Must-hold neighbors
unchanged: `baseConstructorModifierArgsAccepted` (`Base(args)` modifier form) and
`baseConstructorArgsAccepted` (inheritance-list base). Solc-reject fixture
`invalid/BareModifierBaseConstructor.sol` (solc emits 1563).

**Lane**: folded into the `packed-nested-static-array` manifest case (solc_rejects
+ the four CL1 typecheck witnesses in the discipline eval).

## 2026-07-08 — CF2 fixed: revert-pruning of always-reverting callees

`docs/solc-implementation-divergences-2.md` CF2 (INFERRED, confirmed by the
round-2 review): solc runs `ControlFlowRevertPruner` before the
storage/calldata-pointer-return definite-assignment check (error 3464), so a
`returns (T storage p)` whose only obligation-unmet path runs through an
ALWAYS-REVERTING internal callee is accepted (that path can't reach the exit).
Solidus modelled a call as a normal returning node and over-rejected.

**solc mechanism read** (`libsolidity/analysis/ControlFlowRevertPruner.cpp`
+ `ControlFlowBuilder.cpp`): a function is `AllPathsRevert` iff its CFG entry
cannot reach the exit node (BFS over a call-graph fixpoint; leftover-unknown =
recursion is treated as reverting). `ControlFlowBuilder::visit(FunctionCall)`:
`revert`/`throw` → revert node; an INTERNAL call sets `functionDefinition` and
the pruner reroutes it to the revert node iff the callee `AllPathsRevert`;
`require`/`assert` connect to BOTH the revert node and a following node (so they
are NOT always-revert terminators); external/member calls are never resolved,
so never pruned.

**Always-reverts definition implemented** (`SolidCore/Solidity/TypeCheck.lean`):
a monotone Kleene fixpoint (`computeAlwaysRevertNames` / `alwaysRevertFixpoint`
/ `alwaysRevertStep`, ~:11225-11290) over the contract's own + file-level free
functions. A statement's `(falls, exits)` bits (`Stmt.revertFlowFuel` /
`Stmts.revertFlowFuel`, ~:11190) are OVER-approximated so `alwaysReverts` is
UNDER-approximated (sound): only `revert`/`selfdestruct` and a call to an
already-known-always-reverting internal function are `(false,false)`; `return`
is `(false,true)` (reaches the EXIT, not the revert node, so it does NOT make a
function always-revert); `if`-without-`else`, loops, `try/catch`, inline
assembly stay `(true,true)`. Sequencing threads control only past a
fall-through statement and always accumulates `exits`, so a returning path is
never lost — this is what keeps `pick` itself (which returns on one branch) out
of the always-revert set. The set is stored in `CheckEnv.alwaysRevertNames`;
`Stmt.pointerReturnFlowFuel`'s `Stmt.expr` arm (~:10975) now treats a call to
such a name as terminating (no `normal?`), exactly like the pre-existing
`revert`/`selfdestruct` terminal.

**Accept/reject boundary — pinned solc 0.8.35 probed, Solidus matches (Lean
witnesses `SolidCore/Witness/CF2RevertPruning.lean`):**
- helper always-reverts (`alwaysReverts(); }`) → ACCEPT (the fix);
- direct inline `revert` → ACCEPT (regression guard, pre-existing);
- transitive helper (`outer` calls always-reverting `inner`) → ACCEPT;
- all-branches-revert helper (`if(q) revert; else revert;`) → ACCEPT;
- genuinely-unassigned fall-through → REJECT (3464);
- helper that only SOMETIMES reverts (`if(q) revert;`) → REJECT;
- `require(false)` helper → REJECT (`require` is not an always-revert terminator);
- external callee (`this.boom()`) → REJECT (member call, not resolved/pruned).

**Soundness.** Acceptance-loosening, so the risk is over-accepting; the analysis
is a sound under-approximation of always-reverts (only provable terminators
mark `(false,false)`; every `return` is preserved). Residual sound over-rejects
(solc accepts, Solidus still rejects — never the reverse), matching PT1's
per-contract-scope precedent: (a) a helper reached only via non-terminating
recursion (solc treats unresolved recursion as reverting; our monotone fixpoint
from `∅` never marks it); (b) an always-reverting callee that is an INHERITED
base helper or a loop/try-catch-based always-revert (out of the per-contract +
file-level decl scope / conservatively `(true,true)`); (c) the same divergence
in the sibling uninitialized-LOCAL-storage-pointer check (`pointerLocalFlowFuel`)
is left unthreaded — its large mutual block would need invasive param
threading; it remains a sound over-reject.

**Lane.** `tests/forge-harness/cf2-revert-pruning/` — Forge-paired accept lane
(`src/CF2RevertPruning.sol`: the helper-revert `pick` returns `xs=[11,22,33]` on
the non-reverting path; Forge is the value ground truth because the Lean source
Core interpreter does not lower a storage-pointer-returning internal function —
pre-existing, orthogonal to CF2) + four `invalid/` solc-reject fixtures for the
must-still-reject neighbors. Manifest case `cf2-revert-pruning`; witnesses in
`SolidCore.Witness.CF2RevertPruning`. `importedContractAccepted` confirms the
Lean typechecker now accepts the fixed program.

## 2026-07-06 — Phase 1: pinned Keccak is FFI/opaque, keep the pure local spec

`danrobinson/EVMYulLean @ 3c5c44a6` ships Keccak256 as an FFI symbol, not a
pure Lean function:

- `EvmYul/SpongeHash/Keccak256.lean` in the pin is an empty stub (a comment:
  "Use FFI in the meanwhile").
- The actual hash is `@[extern "keccak256"] opaque keccak256 (input : ByteArray)
  (len : USize) : ByteArray` in `EvmYul/FFI/ffi.lean`.

An `opaque`/`@[extern]` function is unusable from this repo's total, purely
computational fuel interpreter: it does not reduce, cannot be `#eval`'d without
native linking, and carries no equational content for future theorems.

Decision (matches ROADMAP Phase 1 specifics fallback, verbatim: "If the pinned
implementation turns out to be `partial`/IO-backed and unusable from a total
interpreter, keep the local pure implementation, rename it to make local-ness
explicit, and add a corpus-checked byte-parity witness against the pinned one —
do not silently keep a shim"):

- Only `EvmYul.UInt256` retargets to the real pinned type (it is a pure,
  reducible `structure ... deriving`, and exposes every named op
  `SharedSemantics.Word` uses).
- The pure Keccak stays, moved out of the `EvmYul.*` namespace into a clearly
  repo-owned module, so nothing masquerades as an upstream shim.
- A byte-parity witness against the pinned FFI keccak is added where the build
  can link it; if native linking of the extern symbol is not available in the
  witness/harness path, that is recorded as a limitation here rather than
  silently skipped.

## 2026-07-06 — Phase 1: reuse the sibling build's prebuilt dependency tree

`../evm-compiler` already has `danrobinson/EVMYulLean @ 3c5c44a6` + its Mathlib
pin built against the exact same toolchain (Lean v4.28.0) this phase moves to.
Rather than a multi-hour from-scratch Mathlib + EVMYulLean build, this repo's
`.lake/packages` is seeded by an APFS copy-on-write clone of the sibling's
prebuilt package tree, and the dependency section of the sibling's
`lake-manifest.json` is reused verbatim (same revs). This is a build-cache
reuse only: `../evm-compiler` is never written to, the `require evmyul from
git ... @ 3c5c44a6` in the lakefile is the real dependency of record, and Lake
remains free to refetch/rebuild from it.

## 2026-07-06 — Phase 1: toolchain-downgrade (4.29.1 → 4.28.0) mechanical fixes

The v4.28.0 downgrade surfaced three purely mechanical, behavior-preserving
breakages. None changes what the interpreter computes; each was fixed without a
new pinned lane because there is no observable-behavior delta.

1. **`alias` is a reserved token in v4.28.0.** The struct field
   `InternalFunctionAliasBinding.alias` and a few local `let`/pattern binders
   named `alias` (Interface/TypeCheck/Checked.lean) no longer parse as bare
   identifiers. Escaped in place as `«alias»` (guillemet identifier) rather than
   renamed, so the field name — and therefore any `Repr`/derive output — is
   byte-identical. `alias?` binders and `"alias"` string literals are distinct
   tokens and were left untouched. No manifest change (the manifest references
   `alias` only in prose/variable names, never the field).

2. **`decreasing_by … omega` over-solves.** In `TypeCheck.lean` one termination
   proof (`checkMemberCallArgs`, ~line 7385) used `all_goals (simp_wf; omega)`;
   under v4.28.0 `simp_wf` already closes some goals, so `omega` errors with
   "No goals to be solved". Changed the lone bare `omega` to `try omega`
   (the file's other 20 termination proofs already used `try omega`).
   Termination proofs are irrelevant to the function's computational content.

3. **`to` is a reserved token in v4.28.0.** The hand-authored `openzeppelin-erc20`
   eval expression in `tests/forge-harness/manifest.json` bound a local
   `let to := 0xbeef` (a transfer-recipient address) and referenced it as
   `Value.word to`; `to` no longer parses as a bare identifier, so the generated
   `interpreter.lean` failed with `unexpected token 'to'` (the sole `lean=exit_1`
   in the first full replay). Alpha-renamed the local binder to `toAddr` in that
   one expression only (3 unique substrings). This is a local-variable rename
   inside a single eval; it changes no assertion and no expectation, and the
   manifest eval count is unchanged (420). The `"to"` strings that name the
   Solidity parameter live in generated AST-importer output, not the manifest,
   and were not touched.

## 2026-07-06 — Phase 1: Keccak byte-parity witness runs and passes

The `lean_exe keccakParity` (native-linked via the pinned `libleanffi`) compares
the repo-owned pure Keccak against the pinned FFI `ffi.KEC` on 11 representative
inputs (empty, real ABI selectors, event-topic signatures, and byte ranges
crossing the 136-byte rate boundary). `lake exe keccakParity` prints
`keccak parity: OK` and exits 0, discharging the roadmap's byte-parity
requirement directly rather than leaving it as an assumption.

## 2026-07-06 — Phase 2: shared package separates cleanly; no vendoring needed

The extraction closure is exactly the three files
`EvmCompiler/Simulation/{Interaction,OpenWorld,Outcome}.lean`. Their only imports
are the pinned `evmyul` package (`EvmYul.SharedState`, `EvmYul.StateOps`,
`EvmYul.Data.Stack`, `EvmYul.MachineStateOps`, `EvmYul.Operations`), Mathlib, and
each other — **no** other `EvmCompiler.*` module, and nothing Yul/EVM-semantics
shaped beyond what `evmyul` already provides. So the roadmap's entanglement
fallbacks (vendor-in-repo, or give up on the sibling) were not needed: a real
sibling package separates cleanly.

- Sibling repo created at `/Users/dan/Projects/evm-interaction` (own git repo,
  first commit), consumed here via `require «evm-interaction» from "../evm-interaction"`.
- The three files are byte-identical verbatim copies (same `EvmCompiler.Simulation.*`
  namespaces and declaration names), so evm-compiler's frozen theorem statements
  stay textually unchanged when it later adopts the package.
- All composition-critical vocabulary is present: `Interaction`/`Transcript`,
  `Query`/`Answer`/`ResourceQuery`, `ExternalRequest` + `Call/CreateRequest` +
  `Call/CreateResponse`, `OpenWorld` (+ `ofYulShared`/`ofEVMShared`), and
  `ForwardRel` with `strengthen_right`/`bind_right`/`mono`/`trans`
  (in `namespace …Simulation.Interaction.ForwardRel`).
- `ForwardRel` is nested under `namespace Interaction`, so its full name is
  `EvmCompiler.Simulation.Interaction.ForwardRel` (not `…Simulation.ForwardRel`);
  the bridge module aliases it accordingly.
- The sibling lakefile mirrors evm-compiler's `moreLeanArgs` (the same set of
  disabled linters) so the verbatim files compile under identical conditions.
- `scripts/check_shared_interaction_hashes.py` sha256-compares the sibling's
  three files against `../evm-compiler`'s live sources (read-only); it currently
  reports `shared_interaction_hashes=pass`. If the reference checkout is absent it
  reports `skip` rather than failing, so the check is enforceable in CI where the
  reference is present without blocking here when it is not.
- `SolidCore/Solidity/Interaction.lean` is the in-repo bridge: it imports the
  package and aliases `Interaction`/`Query`/`Answer`/`OpenWorld`/`ForwardRel`
  under `SolidCore.Solidity.Shared`. It is reachable from the `SolidCore.lean`
  root (so `lake build` verifies linkage) but not from the corpus build path, so
  Phase 2 is corpus-neutral (full replay green, cases=98, paired_cases_passed=yes).

## 2026-07-06 — Phase 3a: witness extraction is a clean verbatim move

No `open`/`variable`/`section` context existed at the `Examples` block sites, so
the blocks moved verbatim with only their enclosing namespaces reproduced. Import
edges are acyclic (Witness.Interface ← Witness.TypeCheck ← Witness.Checked,
mirroring the base modules). Manifest `lean.imports` gains `SolidCore.Witness.Checked`
per case (harness reads imports from the manifest, so nothing else changed).

## 2026-07-06 — Phase 3b: rename + AST split

- `SolidCore.Spine.L00_SourceSolidity` → `SolidCore.Solidity` everywhere,
  three-sided (6 Lean files, manifest's 1775 occurrences, and the 3 scripts'
  hardcoded namespaces/imports). No collision with the pre-existing
  `SolidCore.Solidity.Source.*` runtime layer (distinct sub-namespaces). The
  vestigial `SolidCore/Spine/` directory (and its stale READMEs describing the
  removed compiler-spine layout) is deleted; base modules moved to
  `SolidCore/Solidity/{Interface,TypeCheck,Checked}.lean`.
- The surface AST (the pre-`namespace Executable` section, ~430 lines: Literal,
  Expr, Stmt, FunctionDecl, SourceUnit, …) is split out into
  `SolidCore/Solidity/Ast.lean`; `Interface.lean` keeps `namespace Executable`
  (elaboration + the Phase-4-doomed observation layer) and imports Ast. Zero
  forward references from the AST section into `Executable`, so the split is at a
  clean namespace boundary. Verified end-to-end on one case via the harness
  (generator + manifest + eval), then full replay.

## 2026-07-06 — Phase 3d (evaluator consolidation) reordered after Phase 4

ROADMAP allows Phases 3 and 4 to interleave. Analysis of `Interpreter.lean`
showed the three older evaluator generations (`Expr.eval`,
`Expr.evalWithRuntime*`, `Expr.evalWithRuntimeOrderFuel*`) sit in mutual blocks
**separate** from the kept `evalWithRuntimeByContext`/`...Order` family, but their
remaining call sites are overwhelmingly inside `observe*` walker functions
(`observeShortCircuitEvaluation`, `observeTernaryEvaluation`,
`observeTryExternalCallEvaluation`, …) — which Phase 4 deletes — plus 3 sites in
`Stmt.eval` and 2 pure constant-eval sites in `Interface.lean`. Deleting the
observation layer first removes most of the old-evaluator references, making the
consolidation a small, low-risk port of the residual sites. So the order is:
3a, 3b, 3c, **Phase 4**, then 3d, then Phase 5.

## 2026-07-06 — Phase 3c: SharedSemantics folded into SolidCore.Solidity.Shared

SharedSemantics is a real, heavily-used dependency (Word/norm/Block/Call/Account/
Precompile/Log/External — 477 occurrences), not dead adapters. Folded it wholesale:
files moved to `SolidCore/Solidity/Shared/*.lean`, the namespace/module token
`SharedSemantics` → `SolidCore.Solidity.Shared` everywhere (all Lean files + the
manifest's 46 eval-expr occurrences), and the lakefile reduced to a single
`lean_lib SolidCore` (+ the keccakParity exe). The folded primitives share the
`SolidCore.Solidity.Shared` namespace with the interaction bridge's aliases with
no leaf collisions. Pure rename, no behavior change: build green + one
`Shared`-referencing case (`packed-storage`) passes end-to-end through the
harness. Its full-corpus validation is folded into Phase 4's replay (which builds
directly on this rename) rather than spending a separate ~20-min run on a
pure-rename step.

## 2026-07-06 — Run status and Phase 4 analysis (handoff point)

Completed, each green (full `compare_forge_solc_interpreter.sh` =
`forge_interpreter_compare=pass`, `cases=98`, `paired_cases_passed=yes`) and
committed:
- Phase 1 — substrate unification (Lean v4.28.0 + EVMYulLean @ 3c5c44a6).
- Phase 2 — shared `evm-interaction` package + hash-check.
- Phase 3a — witness corpus out to `SolidCore/Witness/`.
- Phase 3b — `Spine/L00_SourceSolidity` → `SolidCore.Solidity` rename + `Ast.lean`.
- Phase 3c — SharedSemantics folded into `SolidCore.Solidity.Shared`; single lib
  (validation bundled into the pending Phase 4 replay).

Phase 4 (delete observation layer) — analyzed, not yet executed. Findings that
make it safe and cheap to resume:
- The layer is **86 `*Observation` structures** (Interface 33, Interpreter 48,
  ABI 5) and **~215 `observe*` walkers** (Interface 75, Interpreter 118, ABI 22),
  interspersed with live code (not contiguous blocks).
- It is a **parallel reporting layer**: the ONLY live (non-`observe`, non-witness)
  caller of any `observe*` is `SharedPrimitiveRequest.eval`
  (`Interpreter.lean:2184`), which calls `context.observeLowLevelCallResolution`
  and `context.observeContractCreationResolution` **and takes only `.result`**.
  These two are dual-use (they compute the real low-level-call / creation result,
  not just report it) — exactly the roadmap's "changes what it computes" trap.
  Resolution: extract the `.result`-computing core of each into a plain function
  `SharedPrimitiveRequest.eval` calls, then delete the observation wrapper. (Note:
  these are the very choke points Phase 5 rewrites into `Query.external` /
  `Query`-create nodes, so the extracted cores feed directly into Phase 5.)
- **Do NOT delete** the storage-layout machinery (`StorageLayout`,
  `StorageLayoutCursor`, `slotSpan`, `Context.storageSlot?`, packing/path
  resolution) — it is core semantics Phase 5 depends on, not observation code.
- Manifest assertions referencing observations to reclassify (behavior →
  re-express against `CallResult`/`State`/logs and keep; record-structure-only →
  drop), recording each disposition in `docs/phase4-assertion-delta.md`:
  `arrayObservation`, `checkedBinaryArithmeticObservation`,
  `checkedTerminalEvaluationObservation`, `fixedObservation`, `pairObservation`,
  `scalarObservation`, `SourceUnitDeploymentAbiObservation` /
  `observeDeploymentAbiAtFrom`.

Phase 3d (evaluator consolidation) — analyzed; deferred until after Phase 4 (its
residual old-evaluator call sites are mostly inside `observe*` walkers). After
Phase 4, port the 3 `Stmt.eval` + 2 `Interface.lean` (pure constant-eval) sites
that use `Expr.eval`/`evalWithRuntime*` to `evalWithRuntimeByContext` and delete
the three now-dead mutual blocks (`Interpreter.lean` ~5024–7279).

Phase 5 (external world as the shared interaction monad) and Phase 6
(documentation/freeze) — not started; Phase 5 depends on Phases 2–4.

The repository is left green and committed at Phase 3c. `../evm-compiler` was
never modified. `../evm-interaction` was created and committed.

## 2026-07-06 — Phase 4 executed (observation layer deleted), green

Deleted all `*Observation` structures + `observe*` walkers (~294 declaration
blocks, ~12k lines) from `ABI.lean`/`Interface.lean`/`Interpreter.lean` and the
witness corpus. Method and lessons:

- **Declaration-level deletion, not line-range.** A parser removed whole
  top-level blocks whose name/text matched the observation pattern. No
  observation code was inside a *mixed* mutual block, so this was clean.
- **Pattern breadth matters.** The first pass required a word boundary after
  "Observation" and so missed `*ObservationStatus`/`*ObservationBoundary*` names
  and `.observe` (lowercase) methods; broadened to match "Observation" anywhere
  and `\.observe\b`.
- **Dual-use choke points.** `observeLowLevelCallResolution` /
  `observeContractCreationResolution` computed the real `.result` consumed by the
  live `SharedPrimitiveRequest.eval`; extracted plain
  `Context.lowLevelCallResult` / `Context.contractCreationResult` first (faithful
  copies of the `.result` match), then deleted the observe wrappers.
- **Dead-aggregator fallout.** Deleting observation defs orphaned 5 surviving
  witness aggregators that only combined them (`checkedSourceSolidityCoreSemanticsMatch`
  etc.). A transitive-broken sweep (delete surviving witness defs that reference a
  deleted name) removed exactly those 5, with a safety assert that no
  manifest-referenced def was caught. (Scoped to broken defs — did NOT garbage-
  collect the whole unreachable witness corpus, which stays in scope for the
  frozen regression suite.)
- **Manifest reclassification (420 → 419).** See `docs/phase4-assertion-delta.md`.
  The subtle one: 8 evals read the external-call transcript via
  `(CallResult.observe self).state.externalInteractions`. `externalInteractions`
  is a real `State` field and the deleted `State.observeEffects` copied it
  verbatim (no filtering by `self`), so this was faithfully re-expressed with a
  new plain accessor `CallResult.resultState : CallResult → State`. These are the
  very transcripts Phase 5 will formalize as the `Query` sequence.

Full corpus replay green: `forge_interpreter_compare=pass`, `cases=98`,
`paired_cases_passed=yes`. Storage-layout machinery untouched (Phase 5 needs it).

## 2026-07-06 — Phase 3d: evaluator consolidation (one expression evaluator)

A Fable review agent audited Phases 1–4 (confirmed the `resultState` and
choke-point extractions definitionally exact, zero dangling refs, all
manifest-referenced witnesses resolve) and **caught a plan error**: my earlier
handoff note said to delete `evalWithRuntimeOrderFuel`, but that is the *engine*
of the kept evaluator (`evalWithRuntimeByContext → evalWithRuntimeOrder →
evalWithRuntimeOrderFuel`). Deleting it would have broken the build. Corrected.

Consolidation executed:
- Ported the 5 remaining call sites off the old generations to
  `evalWithRuntimeByContext` (same `Except (Value × Runtime)` shape): the 3
  `value:`/`gas:` call-option sites in `Stmt.eval` (siblings already used
  ByContext — an unfinished migration) and the 2 pure constant-eval sites in
  `Interface.lean` (`Expr.evalLayoutBaseCore?` and `CoreExpr.evalWord?`, both over
  `Context.empty`/`State.empty`; projecting `.1` of the pair).
- Deleted the two dead old expression-evaluator families: gen-1
  (`Expr.eval`/`Expr.evalList` mutual) with its old `LValue.read/write/
  writeContainer/applyIncDec` + `LValues.writeTuple?` helpers (which called gen-1
  via `idx.eval` and had no kept callers), and gen-2 (`Expr.evalWithRuntime`/
  `evalListWithRuntime`/`memoryRefOrValueWithRuntime`/`resolveLValueWithRuntime`
  mutual). Kept: `Value.oneLike?` (used by the kept `ResolvedLValue.applyIncDec`),
  all `ResolvedLValue.*`, and the entire `...Order`/`...OrderFuel`/`...ByContext`
  engine. Build green confirms nothing kept referenced the deleted set.
- Per the roadmap, a divergence at the ported sites would be a latent bug to pin;
  the full replay is the arbiter (the call-option and erc7201-layout sites are the
  ones to watch). Result recorded on completion. **Replay green** (cases=98,
  paired_cases_passed=yes) — the ports are behavior-identical, no divergence.

## 2026-07-06 — Phase 5 scoping finding: storage is already word-addressed

Before starting the Phase 5 rewrite, confirmed the actual external-world shape,
which **de-risks the roadmap's central "snapshot problem"**:

- `State.storage : WordMap` where `WordMap := List (Word × Word)` — storage is
  **already word-addressed**, not typed. There is no `TypedStorage`/storage-tree
  representation anywhere. The `StorageLayout`/`Context.storageSlot?`/packing
  machinery *computes* which word slot a typed source access lands on during
  execution, but the stored state is words. So the OpenWorld word-storage
  snapshot is a near-direct read of `State.storage` (self account), and
  re-projection of `CallResponse.postWorld` back is trivial (words in, words
  out) — the roadmap's "layout encoding E has no computable inverse" concern is
  largely moot as the code stands. The fail-closed re-projection remains the
  right *policy* (an answered word not attributable to a touched slot is still a
  distinguished failure), but it is not blocked on inverting a typed encoding.
- The external-world environment lives in `Context` (Interpreter.lean 1487):
  `accountBalances`/`accountCodes`/`accountCodehashes : WordMap`/`ByteMap`,
  `contractAddresses`/`contractCreationCodes`/`contractRuntimeCodes` (named maps),
  block/tx env, `gasleft`. These become the `OpenWorld`-shaped environment read
  as state (no query), post-answer replaced by `postWorld`.
- The oracle-record fields Phase 5 deletes are exactly
  `Context.lowLevelCallResults : List LowLevelCallResult` and
  `contractCreationResults : List ContractCreationResult` — the tables that
  `Context.lowLevelCallResult`/`contractCreationResult` (the Phase-4 choke-point
  functions) read. Those two functions are precisely where `Query.external` node
  emission goes.
- Type bridging needed at the boundary: interpreter `Word` (Nat) ↔ shared
  `EvmYul.UInt256` (Fin); interpreter `List Byte` calldata/output ↔ shared
  `ByteArray`. Both are total conversions.

Implication: Phase 5 is still a real monadic rewrite (thread `Interaction`
through the `Expr`/`Stmt` mutual block so the two choke-point functions emit
`Query.external` and resume on `Call/CreateResponse`), but the snapshot/
re-projection machinery is far cheaper than the roadmap's worst case.

## 2026-07-06 — Phase 5 prep: corrected choke points; dead cluster removed; rewrite is mechanical

Two corrections/findings while starting the rewrite:

- **The real choke points are NOT the ones Phase 4 refactored.**
  `SharedPrimitiveRequest`/`SharedPrimitiveResult`/`SharedPrimitiveRequest.eval`
  (and therefore the Phase-4-extracted `Context.lowLevelCallResult`/
  `contractCreationResult`) were **dead** — unreferenced anywhere in the repo.
  The Phase-4 refactor was still behavior-preserving (it faithfully transformed
  dead code), but the earlier "choke point" identification (mine and the review
  agent's) was wrong. The **live** external-effect sites are
  `Context.resolveLowLevelCall` (Interpreter.lean ~1708) and
  `Context.resolveContractCreation` (~1724), consumed synchronously inside
  `Expr.evalWithRuntimeOrderFuel` (sites ~5345/5362, ~6929, ~7016). Each reads the
  oracle table (`context.lowLevelCallResults`/`contractCreationResults`) inline,
  returns a `LowLevelCallResult`/`ContractCreationResult`, and records the effect
  via `runtime.recordExternalInteraction` into `state.externalInteractions`.
  Deleted the entire dead `SharedPrimitiveRequest` cluster (~63 lines); build
  green (dead code, so corpus-neutral — validation folds into the sub-step-1
  checkpoint).

- **The rewrite is mechanical, not a from-scratch monad plumb.** The shared
  `Interaction Error` already has `Monad` and `MonadExceptOf Error` instances
  (evm-interaction `Interaction.lean` 785/790). The evaluator today is effectively
  `Interaction` with only `done` leaves (it returns `Except RevertData (Value ×
  Runtime)`). So the conversion is: change the return type to
  `Interaction SolidityFailure (Value × Runtime)`; `Except.ok x → pure x`,
  `Except.error e → throw (…revert e)`; the expression evaluator's `fuel = 0` arm stays a
  `.revert typeMismatch` (behavior-preserving); `outOfFuel` is reserved for the
  future `Stmt.eval`-level truncation the roadmap wants; and at the ~4 live sites emit `Query.external world (CallRequest/…)` and
  resume on `Call/CreateResponse` (sub-step 1: answered from the Context
  environment so fixtures run unchanged). `do`-notation carries over via the Monad
  instance. The change is pervasive (every `Except.ok`/`error` and result-match in
  the mutual block, then propagation through `Stmt.eval`/`Contract.call`/
  `callTransaction`/ABI entries, with `?`-named Option adapters kept for the
  manifest through sub-step (2)), but each edit is mechanical.

## 2026-07-06 — Phase 5 foundation landed (green)

Built and proved the shared-alphabet foundation in `Interpreter.lean` (additive,
build green, corpus-neutral — validation folds into the sub-step-1 checkpoint):

- `SolidityFailure` (revert | outOfFuel) and `abbrev SolI := Interaction
  SolidityFailure` — the interaction monad the external boundary emits into.
- Total bridges: `wordToU256`/`u256ToWord`, `bytesToByteArray`/`byteArrayToBytes`,
  `wordToAddress`/`addressToWord`, `lowLevelKindToCallKind`/`callKindToLowLevel`.
- `buildCallRequest` (fills `requestedGas` from `{gas:}` else ambient `gasleft`)
  and `decodeCallResponse`.
- `emitLowLevelCall`: emits `Query.external default (.call request)` and resumes on
  the `CallResponse` (checkpoint-1: world snapshot is placeholder `default`).
- `answerCall`/`contextAnswer`: replay-from-Context answerer (gas-lenient — try
  the oracle without gas, else the sent `requestedGas`). `SolI.runFromContext`
  folds the tree (fuel-bounded); `SolI.queryTranscript` exposes the query sequence.
- `phase5DemoTree`: a two-external-call interaction tree. Verified end-to-end —
  `phase5DemoTranscriptLength Context.empty = 2`; `runFromContext` folds it to
  `some [false, false]` against the empty oracle (fail-closed); transcript length
  2. This is the Phase 5 acceptance "demo witness shows a two-call execution as an
  explicit Interaction tree with its query transcript" in foundation form.

Remaining Phase 5 work is the evaluator wiring: change `Expr.evalWithRuntimeOrderFuel`
(+ mutual companions, `Stmt.eval`, `FunctionDef.call?`, `Contract.call?`/
`callTransaction?`) return types to `SolI`; replace the synchronous
`resolveLowLevelCall`/`resolveContractCreation` reads (Interpreter.lean
~5345/5362/6929/7016) with `emitLowLevelCall`/an `emitContractCreation` analog;
keep `?`-named Option adapters (via `SolI.runFromContext`) for the manifest; then
sub-steps (2) scripted responders and (3) delete the oracle `Context` fields.

## 2026-07-06 — Phase 5 sub-step-1a: expression evaluator emits Query.external (green)

Converted the expression evaluator's return type `Except RevertData (Value ×
Runtime)` → `SolI (Value × Runtime)` across the `...OrderFuel` mutual block, the
`...Order` wrappers, and the `evalReturn*Order` family. Mechanical: `Except.ok →
pure`, `Except.error e → throw <| SolidityFailure.revert e`, aided by
`instance : MonadLift (Except RevertData) SolI` (pure helpers auto-lift in
do-blocks). The 2 live low-level-call sites now `emitLowLevelCall` (emitting a
`Query.external default (.call request)` node) instead of a synchronous
`resolveLowLevelCall`. The `...ByContext` functions (the boundary `Stmt.eval`
matches on) stay `Except`-returning and fold the SolI tree via `SolI.foldExpr fuel
context` (= `runFromContext` then `.revert e → .error e`, `.outOfFuel →
typeMismatch`), with `fuel = orderFuel expr + 1`.

A Fable review of this increment: **fuel bound verified safe** (query count ≤
syntactic `Expr.lowLevelCall` node count ≤ `orderFuel`, since `Expr` has no
repetition constructs — loops/internal calls are in `Stmt`, re-folded per use — so
`.outOfFuel` is unreachable; my earlier "steps ≤ fuel" framing was wrong but the
syntactic-count argument holds); `decodeCallResponse` verified faithful
(success/output exact modulo the norm the oracle already applies). Two dormant
bugs it caught, both fixed before commit:
- `callKindToLowLevel .callcode` mapped to `.call` (would misroute callcode oracle
  keys under scripted responders) → now maps to `.callcode`.
- `answerCall` gas ordering: tried the `gas?=none` oracle row first for every
  request, which could shadow an exact `gas?=some g` row → now exact-gas-first
  (`some requestedGas`), then no-gas resolution.
Correction to the earlier "prep" note: the evaluator's `fuel = 0` arm stays
`.revert typeMismatch` (behavior-preserving); `outOfFuel` is reserved for the
future `Stmt.eval`-level truncation.

**Not yet converted (recorded residue, sub-step-1b):** a third live external site
in `Stmt.eval` (high-level call / try-catch path, ~7041) and the 2 contract-create
sites (~5493/5513, still reading `lookupContractCreation?`). Creates are soluble in
the shared alphabet via `initCode := creationCode ++ constructorArgs` (responder
recovers the name by prefix-match) — no shared-type change needed. Sub-step (3)
(delete oracle `Context` fields) is gated on converting all three.

Full corpus replay green: `forge_interpreter_compare=pass`, `cases=98`,
`paired_cases_passed=yes`.

## 2026-07-06 — Dev-loop smoke replay added

`scripts/smoke_replay.sh`: a curated ~29-case subset run Lean-only
(`--skip-forge`) for the edit/build/check dev loop; the full replay stays the
commit gate. Rationale: only the Lean interpreter changes during development, so
re-running Forge (per-case solc-compile + Foundry-EVM run, the dominant cost) is
waste — `--skip-forge` still generates each witness from the solc AST and
validates the Lean `#eval`s return `true`, catching any Lean regression. The set
covers the full Phase 5 external-effect surface plus broad
evaluator/statement/storage/reference/ABI/event sentinels, excluding the
minute-plus heavy contracts (erc721-royalty, erc1155-supply variants, checkpoints,
uniswap-v3-math, frontend-frontier) which run only in the full replay.
`SMOKE_WITH_FORGE=1` re-enables Forge for the subset.

## 2026-07-06 — Replay parallelism (`--jobs`), ~2.8× faster dev loop

Diagnosed replay slowness by measurement: per case ≈ 0.07s solc-AST-import +
~4s fixed `SolidCore` olean load + variable `#eval` (heavy OZ contracts run a
minute+ in the pure-Lean interpreter). The harness ran cases **sequentially on 1
of 14 cores**. Sequential smoke (28 cases, Lean-only) = **770s**.

Added an opt-in `--jobs N` flag to `scripts/run_forge_interpreter_harness.py`
(default `1` = byte-identical to the original sequential loop, so the official
full-replay gate command is unchanged). Cases run in a `ThreadPoolExecutor`;
per-case stdout is captured via a **thread-routing stdout** (a proxy that sends
writes to the current thread's buffer, else the real stdout) and replayed in
manifest order. (First attempt used `contextlib.redirect_stdout`, which swaps the
process-global `sys.stdout` and corrupted capture across threads — only 1 of 28
case lines survived; the thread-local router fixes it. Verified `--jobs 5`
emits all cases in manifest order with the correct pass summary.)

`smoke_replay.sh` now passes `--jobs 10` (override `SMOKE_JOBS`): smoke ≈ **272s**
(2.8× — the floor is the single longest heavy case, not the 10× core count).
Dropped `solmate-erc20` from the smoke set (redundant with `openzeppelin-erc20`).
The `--jobs` flag also speeds the full replay (~20 min → a few min) when opted in;
the commit gate keeps the default sequential command.

## 2026-07-06 — Phase 5 stage 0: repair library build left red by sub-step-1a

A Fable agent designing the Phase 5 propagation plan (`docs/phase5-propagation-plan.md`)
found that `lake build SolidCore` was **red at HEAD** (commit a6d3f7d): two
witnesses in `SolidCore/Witness/Interface.lean` (`unspecifiedBinaryOrderEval`,
`unspecifiedTupleOrderEval`, ~20834/20893) still matched `Except.ok` against
`Expr.evalBinaryWithRuntimeOrder`/`evalWithRuntimeOrder`, which sub-step-1a
changed to return `SolI`. **The replay harness generates per-case witness files
and never builds `SolidCore.Witness.*`, so sub-step-1a's green replay did not
catch the library break.** This is a process gap: a green replay ≠ a green
`lake build`.

Fix (validated): wrap both scrutinees in `SolI.foldExpr (Expr.orderFuel core + 1)
unspecifiedBinaryOrderContext (…)` exactly as the `…ByContext` adapters do; the
match arms stay byte-identical. Both witnesses still `#eval` to `some true`
(constant-eval, empty state — the fold answers no queries, so behavior is
identical); they are not referenced by the manifest. `lake build SolidCore` green.

Hardening: `scripts/smoke_replay.sh` now runs `lake build SolidCore` first, so a
library/witness break can never again hide behind a green replay. The Phase 5
propagation plan (model A refined; 8 buildable stages; build-validated PoC) is
committed as the roadmap for the remaining work.

## 2026-07-06 — Phase 5 stage 1: thread `SolI` through `Stmt.eval` + call chain

Executed stage 1 of `docs/phase5-propagation-plan.md` (model A refined). The
statement evaluator and function/contract call chain now produce a propagating
`Interaction` tree; a single top-level adapter folds it back to
`Option`/`Except`.

- Added `SolI.run` (fuel-free structural fold over `Interaction`, answering each
  query from `Context` via `contextAnswer`) and `SolI.caught` (reifies a
  throw-revert Expr tree's revert leaf into an `Except RevertData` value while
  re-throwing `outOfFuel`). `caught` is the ONLY `tryCatch` in the interpreter.
- `LValue.resolveWithRuntime` and `LValues.writeTupleWithRuntime` (renamed from
  `writeTupleWithRuntime?`) now return `SolI`.
- The whole `Stmt.eval`/`evalList`/`evalWhile`/`evalDoWhile`/`evalFor` mutual
  block returns `SolI Result`. The four `fuel = 0 → none` arms became
  `throw SolidityFailure.outOfFuel` (the only throw that escapes `Stmt.eval`);
  recursive `some/none` matches became do-binds; `…ByContext` scrutinees became
  `← (…WithRuntimeOrder tree).caught`; the 9 resolve/writeTuple sites became
  `← (…).caught`.
- `Stmt.tryExternalCall`/`tryContractCreate` kept their `…ByContext`/oracle
  reads synchronous (that is stage 1b/1c); only their Option/Except plumbing was
  threaded (leaves `some → pure`, the four recursive `Stmt.eval` sites do-bind).
- `FunctionDef.evalBodyEntry` : `Option (SolI Result)`, `FunctionDef.call` :
  `Option (SolI CallResult)`, and `Contract.call`/`Contract.callTransaction` :
  `Option (SolI CallResult)`. The frozen `?`-named adapters (`FunctionDef.call?`,
  `Contract.call?`, `Contract.callTransaction?`) keep their exact signatures and
  fold via `SolI.run`, so the manifest, ABI.lean, Checked.lean, and Context stay
  unchanged. `FunctionDef.call?_reverted_rolls_back` was restated against the
  tree (`= pure (Result.reverted …)`) and reproved with the extended simp set.

Why behavior-preserving: `contextAnswer` is a pure function of `Context`, so
answering a query at the per-call fold (now) or the per-expression fold (before)
yields identical answers; the only delta is `fuel = 0` propagation, invisible
through the `Option`/`Except` adapters. Full `lake build SolidCore` and
`scripts/smoke_replay.sh` (28 cases, `forge_interpreter_compare=pass`) are green.

Scope deviation (necessary for a green library build): besides
`SolidCore/Solidity/Interpreter.lean`, three direct `Stmt.eval` callers outside
the plan's type table had to be adapted to the new tree type, each a minimal
signature-preserving fold at the boundary (`(SolI.run ctx …).toOption`):
`Stmt.eval?` in `SolidCore/Solidity/Interface.lean` (a frozen witness-facing
`?`-adapter) and two hand-written witness helpers in
`SolidCore/Witness/Interface.lean` (`abiEncodeCoreExprResult`,
`unspecifiedTupleOrderStmtEval`). No fixtures, manifest, ABI.lean, Checked.lean,
TypeCheck.lean, or Context were touched.

## 2026-07-06 — Phase 5 stage 1b: high-level external-call site emits

`Stmt.tryExternalCall`'s remaining synchronous `context.resolveLowLevelCall`
became `← emitLowLevelCall context kind target calldata value gas?`, matching the
two Expr-evaluator sites. The `missingCode` extcodesize guard (a state read, no
query) stays *before* the emit; `recordExternalInteraction` keeps consuming the
decoded result. The high-level external-call / try-catch transcript is now real.
Behavior-preserving (`contextAnswer` answers from the same oracle). Build + smoke
(28 cases, `forge_interpreter_compare=pass`) green.

Extends R7 (gas-key erasure): the high-level call site now shares the sub-step-1a
no-gas vs `{gas: gasleft}` transcript ambiguity — a recorded, deferred `gasleft`
limitation, no new mechanism.

## 2026-07-06 — Phase 5 stage 1c: contract creation emits (name-encoded initCode)

Creates now emit `Query.external default (.create request)`. The source semantics
creates by contract *name* (pre-compilation; fixtures key the oracle by name and
do not populate `contractCreationCodes`), so identity is encoded canonically:
`creationInitCode name args` = 32-byte big-endian UTF-8-name-length ‖ name bytes ‖
args (injective); `decodeCreationInitCode?` inverts it fail-closed (length
overrun or non-UTF-8 → `none`).

- `buildCreateRequest`: `kind := .create2` iff a salt is present, else `.create`;
  `creator := wordToAddress context.self`; `value`; `initCode := creationInitCode`;
  `salt := salt?.map wordToU256`; `permission := true`.
- `emitContractCreation : … → SolI ContractCreationResult`. `CreateResponse` has
  **no `success` field**, so `decodeCreateResponse` sets `success := address ≠ 0`
  (EVM convention); name/args/value/salt are carried through for oracle keying and
  `recordExternalInteraction`, mirroring `decodeCallResponse`.
- `answerCreate` decodes the name from `initCode`, calls `lookupContractCreation?`
  (no keying reimplementation) else `ContractCreationResult.failedRequest`, and
  encodes back with `address := if success then address else 0`. The `.create` arm
  was added to both `contextAnswer` and `SolI.runFromContext`.
- The 3 sites converted: two `Expr.contractCreate` (salt-less and salted) and
  `Stmt.tryContractCreate`. Failure branches stay equivalent —
  `RevertData.fromRawBytes [] = RevertData.empty`, so the Expr sites' old explicit
  `none → RevertData.empty` branch collapses into `¬success → fromRawBytes output`;
  `resolveContractCreation`'s `none → failedRequest` matched `answerCreate` exactly
  at the Stmt site.

Deferred limitation recorded here and in `ROADMAP.md`'s gap registry: the emitted
`initCode` is source-canonical, not compiled creation bytecode — a transcript-level
mismatch analogous to `gasleft` erasure, resolved at the future lowering.

Build + smoke green.

## 2026-07-06 — Phase 5 stage 1d: precompile builtins emit (open-world staticcalls)

`ecrecover`/`sha256`/`ripemd160` are, in the EVM, a `STATICCALL` to address
1/2/3 — ordinary external calls, not a residue family. Their evaluator sites now
emit `Query.external default (.call request)` via a new `emitPrecompileWord`
helper (`kind := .staticcall`, `recipient/codeAddress := Precompile.address kind`,
`calldata := input`, `value := 0`, `gas? := none`), decoding the output word with
`Precompile.outputWord?` — exactly what `lookupPrecompileOutputWord?` did inline.
`keccak256` is the KECCAK256 opcode (computed in-EVM), so it stays local — no
query.

The result is computed **in the responder**: `answerCall` already reaches these
rows — `LowLevelCallResult` and `Precompile.Result` are the same type
(`Call.Result ExternalCallKind`), and `answerCall → lookupLowLevelCall? →
Call.Result.lookup? context.lowLevelCallResults` reads the very rows
`Precompile.lookup?` keyed (kind=staticcall, target=address, calldata=input,
value=0, gas?=none), resolved through the existing exact-gas-first-then-no-gas
fallback. No `answerCall` extension and no fixture-row change were needed.

The two converted sites (`Expr.externalHash`, `Expr.ecrecover`) leave
`Context.ecrecoverAt`, `ExternalHashKind.lookup?`, `lookupPrecompileOutputWord?`,
and `lookupPrecompileCall?` unused on the execution path; they still read
`context.lowLevelCallResults` and are deleted at stage 3 with the oracle fields.
Required before stage 3 (they blocked deleting the field) and for the eventual
ForwardRel composition (the Yul side emits these precompile staticcalls).

Build + smoke green.

## 2026-07-06 — Precompiles: match evm-compiler exactly (no special Solidity handling)

Directive: precompiles should be treated exactly as evm-compiler's Yul/EVM
interaction semantics treat them — as ordinary external calls, emit-and-
environment-answer, with NO precompile-address special-casing in the semantics.
Confirmed evm-compiler's model: `EvmCompiler/Yul/InteractionSemantics.lean:129`
turns a CALL into `.request (.external world (.call request))` with zero
precompile logic anywhere in its Simulation/Yul interaction layer.

Current state after stage 1d (`eb60734`): the *emit* side already matches
(`ecrecover`/`sha256`/`ripemd160` source builtins emit a staticcall to address
1/2/3; ecdsa case passes `forge=ok lean=ok`). The residual "special stuff" to
remove, folded into **Stage 2 (scripted responders)** where the answer path is
reworked:
- `Context.lookupLowLevelCall?`'s `builtinStaticcallResult?` fallback (computes
  identity 0x4 / modexp 0x5 in the semantics) — remove; precompiles answered
  uniformly from the responder like any external call. No corpus case exercises
  identity/modexp, so this is corpus-safe.
- `emitPrecompileWord` — unify into the ordinary external-call emit
  (`buildCallRequest`/`emitLowLevelCall`); the only legitimately Solidity-specific
  part is recognizing the builtin *name* (`ecrecover`/`sha256`/`ripemd160`),
  since Yul has no such builtins.
- `SolidCore/Solidity/Shared/Precompile.lean` computation — remove from the
  semantics (the open-world environment owns precompile results). Keep only the
  address constants needed to build the staticcall target.

## 2026-07-06 — Phase 5 stage 2: scripted responders + precompile alignment + kind-dependent call requests

Landed the stage-2 machinery. Manifest UNCHANGED (R5): the responder conversion
of the manifest is deferred to stage 3; stage 2 adds the machinery and validates
equivalence out-of-band.

**Scripted responder (`SolI.runWith`, fail-closed).** `ScriptedResponder :=
List OracleRow` (`OracleRow.call LowLevelCallResult | .create ContractCreationResult`).
`SolI.runWith` folds a tree structurally (no fuel, like `SolI.run`), answering
external call/create queries from the responder rows and **failing closed** on a
total miss (`ResponderFailure.unmatched request`, carrying the request for a
diff) instead of the old fail-open `failedRequest`. `ScriptedResponder.ofContext`
derives the responder mechanically from a `Context`'s oracle fields. Matching
mirrors `answerCall`/`answerCreate` keying **exactly** (target recovered from
`codeAddress`; exact-gas-first then no-gas; create name/args/value/salt from the
name-encoded initCode, fail-closed on malformed), so on any tree whose external
requests all have a matching row the responder answers identically to
`contextAnswer`.

Design note — **find-first, not strict-ordered.** The plan floated an
order-consuming responder (out-of-order ⇒ failure). We match `List.find?`-first
(same as the retired `contextAnswer`) to *guarantee* behavioral equivalence:
several fixtures list duplicate-key rows (e.g. uniswap
`importedSafeTransferFromRejectsFalseAndFailedCall`) whose order a consuming
responder would diverge on. The substantive win — a loud failure on any external
request the fixture did not anticipate — is retained via fail-closed-on-miss.

**Fail-open reliance: NONE.** Enumerated every intentional-failure witness in the
corpus; all supply an explicit `success := false` row (uniswap failed-call,
vesting/refund-escrow/payment-splitter rollbacks, multicall delegatecall
failure). The one call-with-no-row case (dapphub-weth9 second withdraw) reverts
on a `require` guard *before* issuing the call, so it never reaches the fail-open
path. No positive assertion in the 98-case corpus exercises the fail-open miss,
so making the responder fail-closed changes no expectation.

**Precompile alignment (match evm-compiler).** Removed
`Context.lookupLowLevelCall?`'s `builtinStaticcallResult?` fallback and deleted
the in-semantics identity/modexp computation from `Shared/Precompile.lean`
(`successfulStaticcall`/`identityStaticcall`/`expMod`/`expModAux`/`modexpOutput`/
`modexpStaticcall`/`builtinStaticcallResult?`). `modexpInput` (calldata encoding,
not computation) stays. Precompiles are now ordinary external calls answered by
the environment/responder — no special-casing in the semantics. Corpus-safe: no
case computes identity/modexp; the two now-unasserted `checked{Identity,Modexp}
PrecompileStaticcallMatches` witness defs are dead (not referenced by manifest or
any `#eval`/theorem). `keccak256` stays local (opcode).

**Kind-dependent `buildCallRequest` (+ `answerCall` inversion).** delegatecall:
`recipient := self`, `transferValue := 0`, `apparentValue := context.value`;
staticcall: `transferValue := 0`; call/callcode unchanged. `codeAddress := target`
for every kind, and `answerCall`/`ScriptedResponder.answerCall?` recover the
callee from `codeAddress` (not `recipient`) so the oracle round-trips for
delegatecall (whose recipient is now the caller). All corpus delegatecall/
staticcall rows carry `value = 0`, so the round-trip is exact.

**Validation (the stage-2 gate).** `scripts/check_responder_equivalence.py`
regenerates every oracle-bearing witness (40 evals across 18 cases) with each
tree-folding checked entry name-swapped to its `*RespCheck` twin (fold under
`ScriptedResponder.ofContext` instead of `contextAnswer`) and asserts each still
prints the case's expected value — equivalence of results AND the recorded
external-interaction transcripts the assertions check. Result:
`responder_equivalence_check=pass`, `oracle_cases=18 equivalent=18`. Plus
`lake build SolidCore` + smoke (28 cases, `forge_interpreter_compare=pass`).

## 2026-07-06 — Phase 5 stage 3: oracle Context fields deleted; manifest + witnesses fold under scripted responders

The fixture oracle left `Context`. `Context.lowLevelCallResults`/
`contractCreationResults` are gone (fields, both initializers), together with
every reader: `lookupLowLevelCall?`, `resolveLowLevelCall`,
`lookupContractCreation?`, `resolveContractCreation`, `lookupPrecompileCall?`,
`lookupPrecompileOutputWord?`, `Context.ecrecoverAt`, `ExternalHashKind.lookup?`,
`answerCall`, `answerCreate`, and `ScriptedResponder.ofContext`. In
`Shared/Precompile.lean` the row-lookup family (`request`/`callKind`/`lookup?`/
`lookupOutputWord?`/`ecrecover?`/`ecrecoverAt`) is deleted; only `address`,
`ecrecoverInput`, `outputWord?`, `modexpInput` (encodings, not lookups) remain.

**`contextAnswer` collapses to `Query.defaultAnswer`.** `defaultAnswer`'s
call/create shapes decode to exactly the old fail-open `failedRequest`
(success = false / address = 0, empty output), and `decodeCallResponse`/
`decodeCreateResponse` rebuild results from the original emit params — so the
frozen `?` adapters are bit-identical on the row-less contexts that remain.
`SolI.runFromContext` likewise answers everything with `defaultAnswer` (kept
fuel-bounded for `foldExpr`/transcript utilities).

**Two responder folds, by design:**
- Corpus manifest: fail-closed `SolI.runWith` via `*UnderResponder` wrappers
  (responder right after fuel). All 40 oracle evals across 18 cases converted;
  rows moved verbatim from context literals into `responderOfResults` args;
  eval count unchanged (419). Direct-literal sites, let-bound-context sites
  (every consuming entry of the context var swapped), and locally-bound `call`/
  `construct`/`wordOk` lambdas (responder threaded as a lambda parameter,
  row-less sites pass `[]`) — validated by the stage-2 equivalence check
  re-run just before the flip (18/18); the full replay gates the follow-up entry.
- Witness sentinels: fail-open `SolI.runFailOpen` via `*FailOpen` twins — rows
  answer find-first with the retired `contextAnswer`'s exact keying; misses take
  `defaultAnswer` (≡ the old fail-open `failedRequest`). Several sentinels
  deliberately exercise the miss path (`lowLevelCallGasMismatchReturnsFalse`,
  `externalFunctionPointerTryCatchCatchMatches`, …), so fail-open preserves
  every recorded truth value by construction; verified — 138 witness evals
  byte-identical to the pre-stage-3 baseline (including three pre-existing
  `some false` and one `none`).

Stage-2 scaffolding removed with the fields: the `*RespCheck` twins and
`scripts/check_responder_equivalence.py` (its job — proving responder ≡ context
answers on the corpus — was done; final run 18/18 pass).

Zero `lowLevelCallResults`/`contractCreationResults` references remain in
SolidCore/, scripts/, tests/. Gates: build green; smoke 28 cases pass (+ the two
oracle cases outside the smoke set, `openzeppelin-ecdsa` and
`typechecker-calldata-origins`, pass via `--only`); witness baseline identical;
the full sequential 98-case replay + AST audit gate run was IN PROGRESS at
commit time (committed early at the user's request, on the strength of
build/smoke/equivalence/baseline gates and an independent review of the diff);
its result and wall-clock are recorded in a follow-up entry.

## 2026-07-06 — Phase 5 stage 3 follow-up: full-gate results

The gates left in progress at the stage-3 commit (`49a20f3`) both passed
against that exact tree:

- **Full corpus replay**: `forge_interpreter_compare=pass`, `cases=98`,
  `paired_cases_passed=yes`, zero case failures. Run with `--jobs 10`
  (~16 min wall-clock; a first sequential attempt was killed by the session's
  background-task reaper at 74/98 after ~60 min — nothing about the corpus).
- **AST frontend audit**: `rendered_sources=97`, `render_failures=0`,
  `unknown_source_scalar_value_fields=0` (no unimplemented constructs).

With these, the complete stage-3 gate battery is green: build (1091 jobs),
smoke (28 cases) + the two oracle cases outside the smoke set via `--only`,
witness truth-value baseline (138 evals byte-identical), stage-2 responder
equivalence re-run just before the flip (18/18), full replay, and AST audit.
## 2026-07-06 — Lowering-prep cleanup pass (N1/N2/N4 from the readiness study)

Executed on branch `cleanup/lowering-prep` (worktree, based at 56f59fa), per
`docs/compile-to-yul-readiness.md` §5's "do now" list. Every "zero uses" claim
was re-verified against the current tree (post-Phase-5-stage-3) before any
deletion, since the study predates the stage-1e/2/3 commits.

- **N1 — landed.** Deleted the 18 dead observation-era classifier enums from
  `Interpreter.lean` (`LowLevelCallEvaluationStatus` … `CallExitMode`; full
  list in the commit). Re-verification: rg across `SolidCore/`,
  `tests/forge-harness/manifest.json`, `scripts/` found zero references
  outside the inductive declarations themselves (type names and all
  constructors). Interspersed live types (`TernaryBranch`,
  `RevertPayloadSource`, `RequireCheckSource`, `TryCatchMatchKind`,
  `SwitchBranchSelection`) kept.
- **N2 — SKIPPED: the readiness doc's dead-code claim is stale.** The doc
  says the `Runtime` byte-memory shadow (`memoryByteMap`/`memoryBytesUsed`/
  `memoryFreePointer`/`memoryAllocations`, readers `loadMemoryByte?`/
  `readMemoryBytes?`) is "written only at newBytes/newDynamicArray and read
  nowhere". On the current tree it has a live reader: the witness
  `memoryAllocationFootprintMatches` (+ 4 helper defs,
  `SolidCore/Witness/Interface.lean:1600–1661`) asserts on all four fields
  and both readers. Nothing *semantic* reads the shadow, so retiring it is
  still right eventually — but it now requires deleting witness defs in the
  same witness territory the concurrent main-tree agent's final Phase-5 work
  touches (the reason N3 was deferred), so it is skipped here rather than
  half-done. Revisit after Phase 5 merges, together with N3.
- **N3 — deferred by instruction**, not attempted: the in-file example defs at
  the tail of `Interpreter.lean` are inside the main-tree agent's uncommitted
  final work; moving them in parallel guarantees conflicts.
- **N4 — landed.** `Ast.lean` no longer imports `SolidCore.Solidity.ABI`.
  The dependency turned out to be **entirely vestigial for Ast itself**: the
  surface AST uses no ABI/Interpreter/Keccak name (it builds unchanged
  without the import; `Word`/`Byte` are local abbrevs over
  `Shared.Word`/`Nat`). The real consumer was `Interface.lean`, which
  imported only `Ast` and received ABI/Interpreter/Keccak transitively; it
  now imports `SolidCore.Solidity.ABI` explicitly. No import cycle
  (ABI → Interpreter/Keccak/Word; Ast → Shared only), no declaration renamed,
  manifest untouched.
- **Doc corrections** (same pass): fixed the readiness doc's Sm seam note —
  the free-memory pointer *lives at* `0x40` and initially *points to* `0x80`;
  softened `function-boundary-refactor-plan.md` §1.5's "solc inlines
  modifiers" to the accurate split: the *semantics* is placeholder
  substitution; legacy codegen inlines, via-IR may emit modifier inner bodies
  as per-layer Yul functions (an emission choice, not a semantic one).
- **ROADMAP**: added the recursion/internal-call acceptance gap to the known
  semantic gaps registry (internal-linkage calls inlined with fuel 64;
  recursion/deep nesting silently rejected at elaboration while solc
  accepts; status "Deferred — plan exists",
  `docs/function-boundary-refactor-plan.md`).

Gates per landed item: `lake build SolidCore` + `scripts/smoke_replay.sh`
(28 cases, `forge_interpreter_compare=pass`, all `lean=ok`).
## 2026-07-06 — A1 rational constants: over-reject (completeness) fix, no unsoundness

The audit (`docs/rational-constants-audit.md`, commit `5c26c24`) corrected the gap
registry's suspicion. A1 was recorded as **suspected unsoundness** ("may currently
mis-evaluate"). It is not: a `NumberRat` exact-rational folder already existed
(Phase 3b), folds in unbounded-precision ℚ, and gates integer-only results on
exact division — **0 WRONG-VALUE divergences** across the whole probe set. The
classic truncation traps (`7/2*2`, `1/2 + 1/2`) already return solc's exact `7`
and `1`, not `6`/`0`.

The real, live gap was **OVER-REJECTION** (a completeness gap): `NumberRat` was
over `Nat`, so any constant whose folded value is negative — formed by subtraction
or a nested unary minus — was rejected even though solc accepts it. Confirmed on
three probes: `int256 = 0 - 5` (−5), `int256 = 3 - 10` (−7),
`int256 = 7 / 2 * 2 - 100` (−93, a negative fractional intermediate).

**The fix (engine):** widen `NumberRat` to a signed exact rational
(`num : Int`, `den : Nat` strictly positive; `mk?` canonicalizes the sign onto
the numerator). Consequences:

- `NumberRat.sub` is now **total** (`some (lhs.sub rhs)` in
  `BinaryOp.applyNumberRat?`) — a negative result is representable. This is the
  whole fix for the three over-rejects.
- `div?` routes the (possibly signed) denominator through `mk?`; `pow` over
  signed `Int` handles negative bases for free.
- New `NumberRat.exactInt? : Option Int`; `exactNat?` is `exactInt?` filtered to
  `≥ 0`, so bit/shift/mod ops (which solc errors on for negatives) and unsigned
  targets still reject negatives.
- `Expr.numberLiteralRat?` / `untypedNumberLiteralRat?` gained a real
  `unary neg` case (negate the numerator; the old untyped "only if zero" guard is
  gone). New `Expr.numberLiteralInt?` folds to a signed integer.
- `Expr.toCoreNumericLiteralAs?` **collapsed**: fold once to a signed `Int`, then
  one signed range test per target — `uint`: `0 ≤ v < 2^bits`; `int`:
  `−2^(bits−1) ≤ v ≤ 2^(bits−1) − 1`. solc rules (2) range and (3) sign fall out
  of this single test, removing the old syntactic-top-level-unary-minus branch
  (`negatedNumberLiteralNat?`, `uint/intPositive/NegativeLiteralFits` deleted).
- `TypeCheck.fixedPointLiteralRaw?` adjusted for the signed numerator (positive
  path; negatives still handled by the sibling `negatedFixedPointLiteralRaw?`).
- Everything stays **total** (no `partial`); `Option` kept only for the genuine
  partial ops (den 0, non-integer operand).

**The fix (importer):** `type_from_expression_node`'s array-length in
type-expression position (`solc_ast_to_lean_source.py`) gained the same
already-folded `typeString`/`typeIdentifier` fallback the VariableDeclaration
array-length path already had, so a scientific/unit length like `uint8[1e1]` in
that position imports instead of aborting.

**Regression guard:** new `rational-constants` corpus lane
(`tests/forge-harness/rational-constants/`, manifest case): a Forge test pins
solc's EVM values for the folded constants (incl. −5 / −7 / −93); `solc_rejects`
pins solc's rejection of `7/2 → int256` (non-integer) and `0-1 → uint256` (signed
→ unsigned); Lean witnesses (`SolidCore.Witness.RationalConstants`) pin the three
folds to their exact signed values, their acceptance into `int256`, and that the
two rejection-boundary probes still return `none` — so the Int-widening does not
over-correct into unsoundness.

`lake build SolidCore` green; the new lane is green
(`solc_rejects=ok forge=ok lean=ok`).

## 2026-07-06 — Phase 6 item 8: delete 3 orphan `*UnderResponder` wrappers

`CheckedContract.constructUnderResponder`, `constructFromUnderResponder`, and
`callCalldataUnderResponder` (`Checked.lean`) were thin wrappers over
`constructResponder`/`constructFromResponder`/`callCalldataResponder` left behind
by the Phase-5 stage-3 responder conversion. Re-verified zero references anywhere
(SolidCore/, manifest.json, scripts/ — each name appeared only on its own `def`
line) and deleted them. The used siblings
(`callTargetWithContextUnderResponder`, `callCalldataAtFromWithContextUnderResponder`,
`callFunctionWithContextUnderResponder`) are kept.

Gate: `lake build SolidCore` + smoke.

## 2026-07-06 — Phase 6 item 6: machine-checked two-external-call demo witness

Phase 5's acceptance included a *synthetic* demo tree (`phase5DemoTree`,
`Interpreter.lean` ~2204) that calls `emitLowLevelCall` twice with hardcoded
addresses — it never runs the evaluator. Item 6 hardens this: a **real**
two-external-call execution as an explicit interaction tree.

`SolidCore/Witness/Phase5Demo.lean` (new, imported by the `SolidCore.lean`
library root so `lake build SolidCore` compiles it) elaborates the existing
hand-built `lowLevelStaticDelegateFunction` (`probeBoth`: a `staticcall` then a
`delegatecall`) to a core `FunctionDef`, drives it through the real evaluator
(`FunctionDef.call`, the tree-returning entry), and:

- `phase5RealDemoTranscript` folds `SolI.queryTranscript` under the scripted
  responder answerer, exposing the raw ordered `Query` transcript over the shared
  alphabet;
- `phase5RealDemoTranscriptMatches` asserts the transcript is exactly two
  external-call queries to `0xcafe` **plus** the folded results
  (`lowLevelStaticDelegateMatches`).

**Observed / pinned:** the deterministic child-evaluation order emits the
`delegatecall` **first**, then the `staticcall`, even though the source tuple is
`(staticcall(...), delegatecall(...))`. The responder keys on
kind/target/calldata (not order), so results are unaffected; the transcript pins
the emission order, which the roadmap flags as load-bearing.

**Machine-check without axioms, without touching the frozen manifest.** Chosen
route: built-but-not-manifest. An in-kernel `decide` proof of
`phase5RealDemoTranscriptMatches = true` is infeasible (the kernel cannot reduce
the interpreter through `FunctionDecl.toCore?` + fuel-8 execution — `decide`
fails in ~1.5 s), and `native_decide` is avoided to keep the axiom set empty.
Instead a throwing `#eval` guard (`throw (IO.userError …)` on `false`) is enforced
by the compiled evaluator exactly like a harness `#eval`: `lake build SolidCore`
fails if the demo regresses (negative test confirmed — flipping the expected
kind order fails the build with the guard's message), and no proof axioms are
introduced. The frozen conformance manifest (99 cases / 426 evals) is untouched.

Gate: `lake build SolidCore` + smoke (28 cases, `forge_interpreter_compare=pass`).

## 2026-07-06 — Phase 6 item 7: harden the frozen `?` adapters (fail-open → fail-closed)

`FunctionDef.call?`, `Contract.call?`, `Contract.callTransaction?`
(`Interpreter.lean`) and `Stmt.eval?` (`Interface.lean`) folded their
interaction tree with `SolI.run context` (equivalently `contextAnswer`, i.e.
`Query.defaultAnswer`), which answers *any* stray external query fail-open with
the default (failed-call) answer and continues. Redefined all four to fold
**fail-closed** under an empty scripted responder, `SolI.runWith []`: an external
request with no matching row aborts with `ResponderFailure.unmatched` →
`.error _ → none`. `FunctionDecl.call?` inherits the fix (it delegates to
`FunctionDef.call?`).

**Why it is safe / behaviour-identical today.** These entry points reach only
query-free paths (no external call/create is emitted on them — the corpus's
oracle-bearing witnesses fold under real responders via the `*UnderResponder` /
`*FailOpen` twins, not these adapters). Verified: **zero** manifest evals
reference any of the four `?` adapters, so no eval can regress. The point is
forward-looking: a future fixture edit that routes an external call through a
non-responder entry now fails **loudly** instead of silently continuing on a
fail-open failed call.

**One proof updated (not a behaviour change).** `FunctionDef.call?_reverted_rolls_back`
(`Interpreter.lean`) `simp`ed with `SolI.run`; its revert path is a
`.done (.ok (CallResult.reverted …))` leaf, on which `SolI.runWith [] = SolI.run`
definitionally, so the theorem still holds — the `simp` lemma was switched
`SolI.run → SolI.runWith`. (This is the repo's one interpreter-side theorem; the
witness/example folds that call `SolI.run` directly are unaffected — only the `?`
adapters changed.)

Gate: `lake build SolidCore` + smoke; witness truth values unchanged.

## 2026-07-06 — Phase 6 item 9 (N2): delete the byte-memory shadow

The `Runtime` byte-memory shadow (`memoryByteMap`, `memoryBytesUsed`,
`memoryFreePointer`, `memoryAllocations` + readers `loadMemoryByte?`/
`readMemoryBytes?`, writer `noteMemoryAllocation`/`noteMemoryBytes`) was written
at `Expr.newBytes`/`newDynamicArray` and read by **nothing semantic** — only by
the witness `memoryAllocationFootprintMatches` (+ its `Expected*` helpers), which
is **not** manifest-referenced (verified 0 across manifest.json). Per the
roadmap's no-speculative-interfaces rule (the shadow misleads future
memory-refinement work), deleted together:

- The 4 `Runtime` fields, `noteMemoryAllocation`/`noteMemoryBytes`,
  `loadMemoryByte?`/`readMemoryBytes?`, and their now-dead support
  (`MemoryByteMap` abbrev + its 4 methods, `MemoryAllocation` struct,
  `initialFreeMemoryPointer`, `roundUpToWordBytes`, and the four
  `dynamic{Bytes,Array}Memory{Footprint,Content}` helpers — all shadow-only,
  verified). `bytesPrefixRightPadded` (widely used) and the **semantic**
  `Context.checkMemoryAllocation` guard (can revert on over-allocation) are kept.
- The two allocation call sites drop the `noteMemoryAllocation` write, keeping
  `checkMemoryAllocation` and threading `runtime'` unchanged (the shadow was the
  only thing the write touched — behaviour-preserving for every semantic field).
- The witness `memoryAllocationFootprintMatches` + `memoryAllocationFootprint{
  Expected,ExpectedFreePointer,ExpectedRegions,ExpectedBytes}` in
  `Witness/Interface.lean`. Kept `memoryAllocationFootprintBody`/`…Function`,
  which are shared with the (non-shadow) `checkedMemoryAllocationFootprint*`
  witnesses that just run the function and check its return value.

Gate: `lake build SolidCore` + smoke; witness truth values unchanged.

## 2026-07-06 — Phase 6 item 9 (N3): move in-file examples out of `Interpreter.lean`

De-monolith: the example/demo defs living inside the semantics file moved verbatim
(names + `SolidCore.Solidity.Source` namespace preserved) to a new
`SolidCore/Witness/InterpreterExamples.lean` (imported by the `SolidCore.lean`
root). Moved: the synthetic `phase5DemoTree`/`phase5DemoTranscriptLength` demo and
the statement/expression example corpus (`compositionalControlExample`,
signed-arithmetic, ternary/do-while, revert/require/assert, `captureReturn`,
`writesThenReverts`, …) with their little AST-builder helpers (`uint256`,
`Expr.add`, `Stmt.seq`, …). Verified zero external references to any moved def
(none manifest-referenced; the builder helpers are not called outside the block),
so the move is behaviour-neutral. `Interpreter.lean` no longer carries example
scaffolding.

Gate: `lake build SolidCore` + smoke.

## 2026-07-06 — Phase 6 status: awaiting the final sequential replay gate

All Phase 6 work items are committed (docs 1–5 at `2c3262d`, item 8 at
`50f1ca4`, items 6/7/9 at `e687bed`). Two things remain, and neither is
pre-claimed here:

1. **Item 10** — the clean sequential full replay + AST audit is RUNNING
   (nohup-detached, started 18:06 PDT) against exactly this tree. Phase 6 is
   complete only if it ends `forge_interpreter_compare=pass`, `cases=99`,
   `paired_cases_passed=yes`, with a clean audit.
2. **Item 11** — the final run-summary entry (phases, corpus status, every
   deviation, open items) is drafted and will be committed as the follow-up
   entry to this one, with the replay result and sequential wall-clock number
   (vs the ~20–25 min pre-Phase-5 baseline; >~2× triggers the recorded
   fused-run deferral) filled in from the actual run.

This entry exists so the tree can be branched from now: any worktree taken
from this commit carries the complete Phase 6 code/docs state; only the gate
verdict and the summary text land after it.

## 2026-07-06 — B/C soundness backlog: fix the three Forge-confirmed WRONG-VALUE bugs (W1/W2/W3)

Landed the three WRONG-VALUE soundness fixes from `docs/bc-soundness-audit.md`
(all Forge-confirmed against pinned solc 0.8.35). Each fix ships with a
regression lane pinned in the SAME commit; the corpus freeze exception for
pinning discovered bugs was used. Eval-count delta: **+6 Lean evals** (99 cases
unchanged; no new case created — the lanes extend the two most-fitting existing
families).

**W3 — signed-base exponentiation crash.** `applySignedWord` had no `exp` arm,
so `(-2)**2` hit the `typeMismatch` sentinel (panic 0). Added `checkedSignedExp`
/`checkedSignedExpLoop` (Interpreter.lean): two's-complement modular
exponentiation over the exponent magnitude, per-step int256-range check in
checked mode (`RevertData.overflow`), wrapping via `signedToWord` unchecked.
Added the `exp` arm to `applySignedWord` and to the `Value.int`/`Value.word`
dispatch. Narrow-type (`intN`) result overflow is enforced by the enclosing
`intCleanup` the importer already inserts — Forge-pinned boundary:
`int8(-2)**7 == -128` (fits), `int8(-2)**8` panics `0x11` (checked),
`== 0` unchecked. Lane: `checked-arithmetic` gains `negBaseEven`(=4),
`negBaseOdd`(=-8), `negExpOverflow`(panic 0x11) + 3 Lean evals.

**W2 — narrow left-shift spurious overflow panic.** Solidity shifts truncate to
the operand width with NO overflow check, even in a checked block; we wrapped the
shift result in the checked `uintCleanup`/`intCleanup`. Fix: `Ty.implicitCleanupCore?`
(Interface.lean) now detects a left-shift (`Source.Expr.binary BinaryOp.shl`) and
cleans it with the truncating `uintCast`/`intCast` (never-panic) instead of the
checked cleanup; the compound-assign path (`<<=`) applies its `ValueCleanup`
unchecked for `shl` in the `assignOpCleanupExpr` interpreter arm. Right shifts
(`shr`/`sar`, magnitude non-increasing) are untouched. Forge-pinned:
`int8(64)<<1 == -128`, `uint8(255)<<1 == 254` (no revert). Lane:
`checked-arithmetic` gains `shlWrapSigned`, `shlTruncUnsigned` + 2 Lean evals.

**W1 — `abi.encodePacked` narrow-width loss.** Top-level narrow `uintN`/`intN`
packed to a full 32-byte word instead of N/8 bytes, corrupting every
`keccak256(abi.encodePacked(...))`. Design chosen: **thread the surface top-level
byte width into the packed-encode node** rather than adding narrow constructors
to the core `Source.Ty` (which would have rippled into every exhaustive `Ty`
match — `defaultValue`, `coerceValue?`, `abiStaticBytes?`, decode, … — the
"balloon" the audit warned against). Concretely: `abiEncodePacked` now carries a
parallel `List Nat` of per-argument packed widths (`0` = "type-directed packing",
which stays correct for `bool`/`address`/`bytesN`/`bytes`/`string`/arrays/
`uint256`/`int256`); `Ty.packedTopWidth` computes N/8 for narrow `uintN`/`intN`;
`abiEncodePackedNarrowScalar?` emits the two's-complement low bytes (correct for
both `uintN` and `intN`, e.g. `int8(-1) -> 0xff`). **Array/struct elements are
deliberately left on the 32-byte-padded path** — that is exactly solc's packed
encoding of aggregates (confirmed: the pre-existing `packedUint8Array` lane
expects `encodeWord 1 ++ encodeWord 2`), so the corpus-green array/`uint256`/
`address`/`bytesN`/`bytes` behavior is undisturbed. All six call sites (two
`abi.encodePacked`, four `bytes/string.concat`) and both witness call sites
(`Witness/Checked.lean`, `Witness/Interface.lean`) updated. Forge-pinned:
`encodePacked(uint8 0x12, uint8 0x34) == hex"1234"`, `uint16+uint24 -> 5 B`,
`int8(-1) -> ff`, `uint32 -> 4 B`, `(true,false,uint8 7) -> hex"010007"`. Lane:
`abi-encoding-helpers` gains 5 narrow-scalar functions + 1 Lean eval.

**Known residual (documented, not a regression):** `abi.encodePacked(<enum>)`
still emits 32 bytes rather than 1. Enums always pack to 1 byte in solc, but the
env-less packed elaboration path (`Args.toAbiEncodeSource?` -> the
`storageNames`-only `Expr.abiTy?`) does not resolve an enum member expression to
`Ty.enum`, so `packedTopWidth` sees a width-0 type. Resolving it needs the enum
declaration env threaded into that path — beyond the surgical W1 fix and not a
regression (it was 32 bytes before). The `packedEnum` function + its Forge
assertion are kept (solc-truth = `hex"02"`); only the Lean side omits the enum
assertion. Filed as a follow-up.

**Gates.** `lake build SolidCore` green (1094 jobs). `scripts/smoke_replay.sh`
green. All three lanes green via `--only` (`checked-arithmetic`,
`abi-encoding-helpers`: `forge=ok lean=ok`, `forge_interpreter_compare=pass`).
Re-run probe outcomes now match Forge: `packedU8 -> [0x12,0x34]`,
`packedMixedWidth -> [..0x9a]`, `packedNegInt8 -> [0xff]`, `packedUint32 -> 4 B`,
`packedBoolMix -> [1,0,7]`; `negBaseEven -> 4`, `negBaseOdd -> -8`,
`negExpOverflow -> panic 0x11`; `shlWrapSigned -> -128`, `shlTruncUnsigned -> 254`.

## 2026-07-07 — Latent red lane: `openzeppelin-ecdsa` eval #4 emitted an unanswered ecrecover query under the fail-closed plain adapter

**Symptom.** `--only openzeppelin-ecdsa` errored on one eval with
`TypeError.unsupported "checked executable contract call OpenZeppelinECDSAHarness"`
— a fail-closed diagnostic escaping to the eval result (RC=1). Latent on
`codex/solidity-semantics-only` since Phase 6 `e687bed`.

**Root cause (traced, cited).** The ecdsa manifest has 5 evals. Evals #1/#2
(`tryRecoverVRS`/`recoverVRS`/`recoverShort` success paths) were already
converted to `callFunctionWithContextUnderResponder` with an `ecrecover`
oracle row. Evals #3 (high-S) and #4 (invalid-signer) still used the plain
`CheckedContract.call` with `State.empty` and NO responder. `e687bed` hardened
the plain adapter from fail-open (stray query answered with failure) to
fail-closed (`SolI.runWith []` -> `ResponderFailure.unmatched` ->
`TypeError.unsupported`, via `optionToExcept ("contract call " ++ decl.name)`,
`Checked.lean:290`). The catch: **whether a query is emitted depends on the
input**:

- Eval #3 (high-S, `s > halfOrder`): `OpenZeppelinECDSA.tryRecover`
  (`src/OpenZeppelinECDSA.sol:57-62`) returns `InvalidSignatureS` **before**
  reaching `ecrecover` at line 64. `recover` -> `_throwError` reverts, also
  before `ecrecover`. **No query is emitted** -> the plain fail-closed call
  succeeds. Eval #3 is therefore a *meaningful* fail-closed assertion that the
  high-S path never touches the precompile; left as plain `call` deliberately
  (converting it would mask a future regression where high-S wrongly reaches
  ecrecover).
- Eval #4 (invalid signer, `v = 29`, `s = 0xbbbb < halfOrder`): passes the
  S-check, reaches `ecrecover(hash, 29, r, s)` at line 64, which **emits a
  staticcall query to precompile 1** (`emitPrecompileWord`,
  `Interpreter.lean:1831`). `recoverVRS` emits a second. With no responder the
  first query is `unmatched` -> the observed error. **This is the failure.**

**Fix (manifest-only, no Lean change).** Converted eval #4 to
`CheckedContract.callResponder` (`Checked.lean:619`) — the fail-closed
responder-folding twin of the plain `call` (folds `callTree` =
`Source.Contract.call`, so the target-based semantics and the
`CallResult.reverted (RevertData.custom "ECDSAInvalidSignature" [])`
representation are byte-identical to the old plain path). Rows:
`responderOfResults [ecrecoverResult] []` with `ecrecoverResult` keyed on the
exact `(staticcall, precompile-1, ecrecoverInput hash 29 r s, value 0)` the
source emits, `success := true`, `output := []` (empty). Real EVM ecrecover on
an invalid `v` (=29) returns success with empty data;
`Precompile.outputWord?` (short output -> `none`) then yields signer =
`address(0)`, so `tryRecover` returns `(0, InvalidSignature, 0)` and `recover`
reverts `ECDSAInvalidSignature` — matching both the Forge assertions
(`test/OpenZeppelinECDSA.t.sol:70-98`: `recovered == address(0)`,
`RecoverError.InvalidSignature`, `ECDSAInvalidSignature` revert) and the
eval's pre-existing expectations. Kept as target-based `callResponder` rather
than switching to `callFunctionWithContext*` to preserve the exact revert
shape; no new Lean wrapper needed, so no build required. Eval count unchanged
(5).

**Did any expectation encode fail-open behavior contradicting Forge? No.** Under
the retired fail-open path the stray ecrecover query was answered with
failure (success=false / empty), which also decodes to `address(0)` — so
fail-open here *coincided* with Forge's real assertion rather than
contradicting it. The eval's expected values (`signer 0`, `err 1`, `arg 0`,
`ECDSAInvalidSignature`) were already Forge-truthful; only the plumbing
(unanswered query) was wrong. No expectation was weakened; the fail-closed
hardening was not touched.

**Process lesson.** The `e687bed` fail-closed hardening was gated by
`smoke_replay.sh` + witness baseline, **neither of which includes
`openzeppelin-ecdsa`**. Its true gate — the full sequential replay that
exercises every corpus case's every eval — kept getting killed, so the
regression shipped and stayed latent for the commits between `e687bed` and
`223e4d8`. Input-dependent query emission (eval #3 emits nothing, eval #4
emits) is exactly the class of bug a curated smoke cannot see. Lesson: a
fail-open -> fail-closed flip must be gated by the *full* replay, not the
smoke subset, before landing; if the full replay can't be run to completion,
the flip is unverified.

**Gates.** `lake build SolidCore` green (1094 jobs, no-op — manifest-only).
`--only openzeppelin-ecdsa`: `forge=ok lean=ok`,
`forge_interpreter_compare=pass`; all 5 evals `Except.ok true`.
`scripts/smoke_replay.sh` green.
## 2026-07-06 — Function-boundary refactor, stage 0: pin the recursion/deep-nesting gap

Branch `refactor/function-boundary` (worktree, based at Phase-6 checkpoint
`1a69f5d`), executing `docs/function-boundary-refactor-plan.md`.

Stage 0 records and pins the acceptance gap from the plan §1.4 with a paired
corpus lane, `recursion-gap` (100th case):

- Fixture `tests/forge-harness/recursion-gap/src/RecursionGap.sol` has
  (a) a genuinely recursive `factorial` (→120 at n=5), (a') `sumTo` whose
  runtime recursion depth itself exceeds the 64 inline horizon (`sumTo(70)=2485`),
  and (b) a **static, non-recursive** call chain of depth 70 (`step0..step70`,
  `deepChain()=70`). Forge test asserts all three; solc 0.8.35 accepts and
  Foundry-EVM runs them (3/3 pass).
- The recursive functions are `public` (not `external`): solc rejects internal
  self-calls by name on `external` functions ("undeclared identifier … not yet
  visible"), so recursion must be `public`/`internal`. Recorded because it is a
  non-obvious fixture constraint. `deepChain` stays `external` (it calls an
  `internal` chain, does not self-recurse).
- **Honest Lean expectation, pinned today**: the gap lives in *elaboration*, not
  typechecking — `importedContractAccepted` (the typechecker) is `true` (asserted
  as `importedContractTypechecks`). Elaboration (`toCoreContract?`) returns
  `none` because `defaultInternalCallInlineFuel = 64` runs out on the recursion /
  deep nesting, so `CheckedInput.ownCall?` returns `none` for **every** function
  of the contract. The three `*RejectedToday` witnesses assert exactly that
  (`(ownCall? … ).isNone = true`), each documented to FLIP to the concrete value
  at stage 5. Using the Option-returning `ownCall?` + `.isNone` (rather than the
  `Except`-returning `checkedOwnCallWordMatches`, whose failure is an
  `Except.error` with a fragile message) keeps the pin a clean `Bool`.
- ROADMAP gap-registry row updated (Deferred → In progress, pinned by this lane).

Gate: `lake build SolidCore` green (baseline); single-lane Lean replay
`forge_interpreter_compare=pass`, `paired_cases_passed=yes`; Forge suite 3/3.
Full replay deferred (the main tree is mid sequential replay; CPU caution).

## 2026-07-06 — Function-boundary refactor, stage 1: core node + table + evaluator arm (dead code)

Landed the target representation as dead code — nothing emits `Stmt.internalCall`
yet (elaboration still splices), so the corpus is neutral by construction.

Interpreter (`SolidCore/Solidity/Interpreter.lean`):
- New `Stmt.internalCall : List String -> String -> List Expr -> Stmt`
  (targets, resolved callee name, arg exprs).
- `InternalFunction` (name/params/returns/body) + `abbrev FunctionTable`
  + `FunctionTable.lookup?`, defined before the eval block (they cannot live in
  `Context`, which precedes `Stmt`). `FunctionDef.toInternal` projects the
  entry-only `FunctionDef` onto it; `Contract.table` maps all functions.
- The `Stmt.eval` mutual block (eval/evalList/evalWhile/evalDoWhile/evalFor)
  gained a `FunctionTable` parameter (2nd, after `fuel`), threaded through every
  recursive call.
- `internalCall` arm (§3.1): eval args in the caller runtime; look up callee;
  build the callee frame; **REPLACE** `runtime.locals` with `[frame]` (state
  shared); recurse `Stmt.eval (fuel-1) table …`; map the body `Result` exactly as
  the entry `callBodyResult` for returned/normal (restoring the caller's saved
  locals, keeping the callee's state), propagate `selfdestructed`/`reverted`, and
  map `broke`/`continued` to `reverted typeMismatch` (fixing the latent
  `captureReturn` passthrough).
- R3 mitigation: `collectReturnBindings`/`coerceReturnBindings` are the single
  source of truth; `FunctionDef.collectReturns`/`coerceReturnValues` now delegate
  to them, so the entry mapping and the internal-call arm cannot drift.
- `table` threaded through `evalBodyEntry`/`call`/`call?`/`callUnspecifiedResults`/
  `CallsUnspecified` (after `fuel`) and the rollback theorem. `Contract.call`
  passes `contract.table`.

Caller updates:
- ABI.lean (6 fallback/receive sites) pass `contract.table`; Checked.lean (9
  sites) pass `contract.core.table`; Interface.lean constructor sites pass
  `contract.table`, the two bare single-function adapters pass
  `[function.toInternal]`; `Stmt.eval?`/`Stmt.evalFailOpen?` gained a
  `table := []` default (their ~40 witness callers are unchanged).
- `FunctionDef.callFailOpen?` puts `table` LAST with default `[]` so its ~24
  external-effect witness sites in `Witness/Interface.lean` compile unchanged.
  This is correct while elaboration still splices (stages 0–1: bodies contain no
  `internalCall` nodes). At stage 2 the sites whose bodies gain internal calls
  get `contract.table`, guarded by the full replay. (The value-producing
  `call`/`call?` adapters keep `table` after `fuel` and already pass real
  tables.)

Witnesses: `SolidCore/Witness/InternalCall.lean` (imported by `SolidCore.lean`)
pins the arm with `#guard`s on hand-built tables: direct recursion
(factorial 5=120, 3=6, 1=1), frame isolation (a callee reading the caller's
`secret` reverts; the caller's locals survive), state sharing (a callee's storage
write reads back 42), `broke`→`reverted typeMismatch`, `selfdestruct`
propagation, the fuel bound (value at 64, `outOfFuel` at 3), and a missing-callee
defensive revert.

Gate: `lake build SolidCore` green (1095 jobs); `scripts/smoke_replay.sh`
behaviour-green — all 28 curated cases compute the expected values
(`Except.ok true` / `true`), including the external-effect query paths
(low-level/high-level calls, contract creation, create options) confirming
transcript invariance. Corpus neutral (no node emitted yet).

Environmental note (not a correctness issue): the smoke's `reference-assignments`
lane reported `timeout_after_600s` when run at `jobs=10` — the main tree's
long sequential replay was still competing for CPU/RAM, and ~20 concurrent
`lake env lean` processes (each ~700 MB) caused swapping that pushed this heavy
case's *wall*-clock past the 600 s per-case cap while its CPU need is ~245 s.
Re-run **solo** on the freed machine it passes cleanly:
`case_result=… lean=ok`, `forge_interpreter_compare=pass`,
`paired_cases_passed=yes`, `5:11.99` wall. The other heavy cases
(`openzeppelin-erc20`, `openzeppelin-vesting-wallet`) completed in the concurrent
run. Recorded as an R1 perf datapoint to compare at stage 2's full replay +
wall-clock (the plan's R1 measurement point); Stage 1 changes are behaviour-
neutral (elaboration still splices, no `internalCall` nodes emitted), so this is
not attributable to the node/arm as a correctness matter.

## 2026-07-06 — Function-boundary refactor, stage 2 handoff: verified edit surface (no code changes)

Stages 0–1 are committed (`e5a9876`, `58b6cf0`); stages 2–5 were deliberately
not attempted this run (each `Interface.lean` iteration is a ~7–20 min compile
and stage 2 is full-replay-gated). This entry records the VERIFIED edit surface
for stage 2, mapped against the committed tree, so the implementer starts from
checked anchors. Key facts (line numbers as of `58b6cf0`):

- `CoreStmt` IS the interpreter's `Stmt` (`Interface.lean:27` abbrev), so
  elaboration emits `Source.Stmt.internalCall` directly; the constructor exists
  (`Interpreter.lean:6155`) and the evaluator arm handles it (`:7038–7091`).
  **No other exhaustive core-`Stmt` match needs a new case** — the eval-block
  helpers delegate to `Stmt.eval`, and every `Interface.lean`/`TypeCheck.lean`
  `Stmt` traversal (renameIdents, toCore?, expandUsing, annotateAbi, …) is on
  the *surface* AST `Stmt`, a different type. No Yul/Sc lowering file exists yet.
- `FunctionDecl.internalCallParts?` (`Interface.lean:10401–10516`, two symmetric
  branches: contract functions `:10408–10460`, freeFunctions `:10461–10515`).
  At the emit point: the resolved callee decl is in scope (`callee`), and the
  ordered surface arg exprs are `sourceArgs` — but the current code produces
  arg-temp DECLS (`toStorageAwareCoreArgDeclsWithInternalAliases?`), not core
  arg exprs. Stage-2 work at this site = compute the callee table key + elaborate
  `sourceArgs` to `List CoreExpr` + return an `internalCall`-shaped result; the
  10 wrapper callers (`:10518–10869`: internalStatementCallCore?,
  internalSingleReturnCallCore?, …AssignReturn…, …Tuple…, internalReturnCallCore?)
  each own the `targets`.
- **Table key**: `FunctionDecl.coreName?` (`:8684–8689`) is what
  `FunctionDecl.toCore?` puts in `FunctionDef.name` (`:16502`), so it is the
  consistent key. Library helpers are already mangled uniquely
  (`libraryHelperName`/`…ForIndex` `:15078–15086`) and super-helpers are named by
  `FunctionDecl.superHelpers` (`:473`) BEFORE `internalCallParts?` runs. The one
  real gap: **plain contract-internal overloads share `coreName?`** — stage 2
  must add a disambiguating key (signature suffix or an overload index like the
  library scheme) used identically at the call-site emit and the table emit (R6:
  enforce by a single shared helper, not convention).
- **Table construction**: `ContractDecl.directCoreFunctions?`
  (`:18054–18080`) currently filters to
  `FunctionDecl.isCoreEntrypoint && body.isSome` (`:18078–18079`;
  `isCoreEntrypoint` `:8701–8705` returns false for internal/private). Relaxing
  this filter to also map `FunctionDecl.toCore?` over non-entrypoint direct
  functions + the helper sets already assembled in `toCoreFromOrders?`
  (`ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers`,
  `:18457–18468`) emits the internal-linkage `FunctionDef`s; `selector? := none`
  falls out automatically (`abiSelector?` at `:16563` is none for internal), and
  `Contract.table` (`Interpreter.lean:7745`) then materializes the table with NO
  `CoreContract` shape change. Dedup caution: library/super helpers repeat across
  the dispatch order — dedup by name when emitting, or table keys collide.
- **Stage-4 deletion list** (after stages 2–3 replays are green):
  `defaultInternalCallInlineFuel` (`:10129`) + its 4 consumption sites
  (`:14680, :16551, :18155, :18200`), the fuel decrement in `internalCallParts?`
  (`:10446–10457`/`:10501–10512`), and the fuel-0 fallback
  `functionExpandModifiersToCoreWithStorageRefsOnly?` (`:9991`) whose `[]` case
  reaches `Expr.toCore?`'s `| _ => none` — the exact rejection the stage-0
  `recursion-gap` lane pins.

## 2026-07-06 — Function-boundary refactor, stage 2: node emission for value-signature contract-internal + free functions

Elaboration now emits `Stmt.internalCall` nodes (instead of splicing callee
bodies) for internal calls whose resolved callee has a **pure stack-value
signature** — every parameter and return has no data location (`location.isNone`)
— and whose name is not a synthetic `__`-prefixed helper. All other callee kinds
(storage-ref / memory-ref / function-pointer parameters or returns; library
`__library_*`, super/base helpers) keep the existing inline-splice path; they
move to the boundary in stage 3 or stay spliced where the frame model cannot
represent them yet.

**R6 table-key scheme (the handoff's open design item), decided:**
`FunctionDecl.internalTableKey? = "__internal_" ++ abiSignature?`
(e.g. `__internal_factorial(uint256)`), one shared helper used identically at
the call-site emit (`valueBoundaryCallParts?`) and the table build
(`directCoreFunctions?` / `toCoreFromOrders?`). Chosen over the library
`_overload_<index>` scheme because `abiSignature?` (the existing canonical
param-type renderer, already the selector source) is order-independent —
immune to decl-list reordering — and the `__internal_` prefix makes collision
with a plain entrypoint `FunctionDef.name` impossible. Entrypoint names stay
plain: name-based dispatch (`Contract.findFunctionByName?`, `CallTarget.name`,
used by Checked/ABI/witness paths) requires them.

Mechanics:
- `FunctionDecl.valueBoundaryCallParts?` returns the same
  `(returnBindings, returnStorageRefs, prefixCore, bodyCore)` 4-tuple shape as
  `internalCallParts?`, with `bodyCore := Stmt.internalCall returnNames key
  argVars` — so all 10 wrapper callers are byte-unchanged: `captureReturn`
  around the node is a harmless passthrough (the arm maps callee returns to
  `Result.normal` internally). Guarded `return` at the top of BOTH branches of
  `internalCallParts?` (contract functions and freeFunctions).
- Arg temps use a fresh `_ic_arg_<i>` prefix, never the parameter name: the
  evaluator binds arguments to callee params positionally (`initialFrame?`), and
  param-named temps could shadow a same-named caller local read by a later
  argument expression (a hazard the old α-renaming splice masked).
- Table build: `directCoreFunctions?` additionally elaborates every
  value-boundary ordinary function (any visibility) via the same
  `FunctionDecl.toCore?` and stores it under the mangled key with
  `selector? := none` **forced** — `abiSelector?` is visibility-blind (a
  handoff-map gap: internal functions would otherwise get spurious selectors
  into `findFunctionBySelector?` dispatch). Public functions therefore get two
  entries: plain-name selector-bearing entrypoint + mangled selector-less table
  entry. `toCoreFromOrders?` appends value-boundary FREE-function entries after
  the contract groups and dedups (`CoreFunctionDefs.dedupInternalByName`,
  first-wins = most-derived-wins across the C3 dispatch order, and
  contract-over-free on key collision, matching resolver precedence).
  Constructor path needs nothing: `constructWithBases…` already passes
  `contract.table` from `toCoreFromOrders?`.
- Modifiers untouched (substitution machinery byte-stable). The callee body in
  the table is elaborated once by `toCore?` (modifier expansion included), so a
  modifier-wrapped internal callee behaves as before.

Recursion-gap lane flip pulled forward from stage 5 (recorded deviation): the
fixture's functions are all `uint256`-typed, so at stage 2 they elaborate —
`toCoreContract?` is no longer `none` and the stage-0 `.isNone` pins would now
FAIL. The manifest lane was flipped to the concrete-value witnesses the stage-0
entry promised: `checkedOwnCallWordMatches` at fuel 4000 asserting
factorial(5)=120, sumTo(70)=2485, deepChain()=70 — verified against Forge
(solo replay: `forge=ok lean=ok`, `forge_interpreter_compare=pass`,
`paired_cases_passed=yes`). Stage 5 still owns the ROADMAP registry row update
and the final full-replay confirmation.

Gate note: per Dan's instruction this run, the smoke and full replays are
DEFERRED until all stages are implemented; stage-2 gate here = full
`lake build SolidCore` green (1095 jobs, all compile-time `#guard` witnesses
intact) + the recursion-gap solo replay above.

## 2026-07-06 — Function-boundary refactor, stage 3: library/`using`/`super`/base helpers onto the boundary (value-signature slice)

- `FunctionDecl.isValueBoundaryCallee` no longer excludes `__`-prefixed names:
  library helpers (`__library_<Lib>_<f>[_overload_<i>]`), super helpers, and
  base helpers with pure stack-value signatures now node-emit through the same
  `valueBoundaryCallParts?` guard in both `internalCallParts?` branches (their
  mangled names are already overload-unique, so `internalTableKey?` stays
  collision-free: `__internal___library_Lib_f(uint256)` etc.).
- `toCoreFromOrders?` emits selector-less table entries for value-boundary
  members of `superHelpers ++ baseHelpers ++ libraryHelpers`, elaborated once
  via `FunctionDecl.toCore?` with the full contract context (storageNames,
  stateEnv, modifiers, availableFunctions) — helper bodies are pre-contextualized
  (super-rewrites and library `using`-surface expansion already applied by
  `contextualSuperHelpers?`/`libraryHelperFunctions`), matching the splice-era
  treatment which also ran no contract-name rewrites on them. Dedup order:
  contract groups, then helpers, then free functions (first-wins).
- **Expression-position hoisting: deliberately NOT generalized (deviation from
  the plan's stage 3).** The splice-era wrapper set (`internalSingleReturnCall*`,
  `internalTwoSingleReturnCalls*`, unary/binary/abi variants) already
  sequentializes every expression-position call shape this semantics accepts;
  `valueBoundaryCallParts?` slots into exactly that sequentialization, so
  observable evaluation order is inherited from the splice era rather than
  re-implemented — R4's order-fidelity risk is structurally avoided (same
  temp-decl order, same conditional structure; only the callee body's execution
  site moved). Shapes the wrappers reject (e.g. calls in loop conditions /
  short-circuit operands that the current elaboration refuses) were rejected
  BEFORE this refactor and remain rejected: no acceptance widening beyond the
  recursion/depth fix. New-shape hoisting is future work, tracked with the
  remaining-splice items below.
- **Residual splice (kept deliberately)**: callees with storage-ref, memory-ref,
  or function-typed params/returns still inline-splice (the frame model passes
  arguments by value; storage-pointer args are lowered as `storageAlias*`
  statements, not value-producing expressions). Consequence for stage 4: the
  splice machinery and `defaultInternalCallInlineFuel` CANNOT be deleted yet —
  ref-signature recursion also remains rejected (registry row will say so).
- Gate (per this run's instruction, full replays deferred to the end):
  `lake build SolidCore` green (1095 jobs); solo lanes recursion-gap,
  modifier-order, uniswap-transfer-helper, openzeppelin-multicall all
  `forge=ok lean=ok`, `forge_interpreter_compare=pass`.

## 2026-07-06 — Function-boundary refactor, stages 4-5: deletion deferred (splice still live for ref signatures); recursion lane green; registry updated

**Stage 4 (splice deletion): deferred, deliberately.** The plan's deletion list
(`defaultInternalCallInlineFuel` + 4 consumption sites, the fuel decrement in
`internalCallParts?`, `functionExpandModifiersToCoreWithStorageRefsOnly?`)
assumed ALL internal-linkage calls moved to the boundary. Under the
value-signature slice actually implemented (stages 2-3), the splice path is the
LIVE elaboration for callees with storage-ref / memory-ref / function-typed
params or returns (the corpus exercises storage-ref library callees heavily —
OZ `using`-for fixtures), so nothing on the deletion list is dead
(9 remaining references, verified). Deleting becomes possible only after the
boundary covers ref signatures: the blocker is elaboration (storage-ref args
are lowered as `storageAlias*` statements, not value-producing core
expressions), NOT the interpreter (storage pointers already exist as runtime
`Value.storageRef`/`storagePathRef`). Recorded as the follow-up work item.

**Stage 5 (flip + registry):** the `recursion-gap` lane was flipped at stage 2
(the fixture is all-`uint256`, so it elaborates as soon as contract-internal
value calls are on the boundary) and passes against Forge with the concrete
values (factorial(5)=120, sumTo(70)=2485, deepChain()=70). ROADMAP registry row
updated: **Fixed for value-signature callees; residual gap = ref-signature
callees** (recursion through storage/memory-ref signatures is still silently
rejected via the retained inline fuel). Readiness-doc D1 note: Sc now has a
source IR for value-signature internal calls (`Stmt.internalCall` +
`Contract.table`).

Final combined gate (smoke + full replay + wall-clock vs baseline) runs at the
end of this working session per Dan's instruction; results recorded in the next
entry.

## 2026-07-07 — Function-boundary refactor: final gates, R1 wall-clock, and a pre-existing ecdsa lane failure pinned to the base commit

Final combined gate (per Dan's instruction to defer per-stage replays):

- **Full replay** (100 cases, `--jobs 10`, tip `ad2a78a` + perf/semantic fixes):
  **99/100 pass in 627s wall**, `recursion-gap` green with the concrete Forge
  values, all 35 `solc_rejects` acceptance-rejection lanes still reject, all
  previously-timing-out heavy lanes (openzeppelin-erc20 / access-control /
  erc1155-pausable-supply / erc721-royalty, reference-assignments) pass.
- **The single failure is NOT this refactor's**: `openzeppelin-ecdsa`'s
  invalid-signer eval expects `ecrecover` with v=29 to yield signer 0 without a
  scripted responder row. `ecrecover` is emitted as a precompile STATICCALL
  `Query.external`; under the Phase-6 item-7 **fail-closed** adapters
  (`e687bed`, on this branch's base) an unanswered call is `unmatched` →
  `Contract.call?` = none → `executableFailure` — the eval's expectation
  depends on the retired fail-OPEN default (miss → failed call → empty output →
  `outputWord?` none → `.getD 0` → signer 0). Verified by rebuilding the
  stage-1 baseline `58b6cf0` (node emission entirely absent): the lane fails
  IDENTICALLY there. The Phase-6 checkpoint was "awaiting sequential replay
  gate" — this is what that gate would have caught. Left unfixed here
  (out of refactor scope; likely already addressed on main): fix = either a
  scripted responder row for the precompile miss in the lane eval, or a
  deliberate deterministic-precompile answering layer in the responder.
- **R1 (performance) final numbers** (erc20 probes, per-eval interpretation):
  pre-refactor 7.3s (balanceOf-shaped) / 43.3s (construct-shaped); first cut
  36.1s / 218s (~5x — eager helper elaboration + double toCore?); after the
  single-elaboration reuse + demand-driven super/base helper entries:
  12.1s / 74.4s (**~1.7x**, within the roadmap ~2x rule). Residual overhead =
  the eager internal-linkage table entries per dispatch-order contract, kept
  eager deliberately: constructors call internal functions (`_mint`) that no
  entrypoint body demands, so demand-driving them from entrypoint seeds would
  silently break construction. The harness generator now sets
  `set_option maxHeartbeats 8000000` per generated file (the 200k default was
  an implicit ~50s-per-#eval CPU ceiling that construct-heavy lanes sat just
  under pre-refactor; the per-case wall cap remains the perf gate).
- **R2 note**: fuel is now uniform statement-recursion depth — an internal call
  costs one unit and the callee body runs at `fuel - 1`. No corpus witness
  moved (fuels are generous; the recursion-gap lane runs at 4000).
- **R3/R4 evidence**: zero value drift anywhere in the corpus — the only
  behavioural fix needed was checked-ness lexicality (callee bodies run
  `checked := true` regardless of the caller's enclosing unchecked block,
  matching the splice's `Stmt.checked` wrapper; caught by inspection, pinned by
  the OZ lanes that exercise unchecked arithmetic). Evaluation order is
  inherited from the splice-era wrapper sequentialisation (no new hoisting
  shapes were introduced), so the order witnesses pass unchanged.
## 2026-07-06 — A3: `gasleft` as `Query.resource .gas` (behaviour-preserving)

`EnvWord.gasleft` no longer reads the ambient `context.gasleft` constant directly
in the expression evaluator. It now emits `Query.resource .gas` (the shared
alphabet's reserved resource arm — `EvmCompiler.Simulation.ResourceQuery.gas`,
`Answer (.resource _) = InteractionWord`) via a new `emitGasleft : SolI Word`,
resuming on the answered word. The query appears in the transcript; the value is
unchanged **by construction** because every answerer supplies the ambient
`context.gasleft` word:

- `contextAnswer` (drives `SolI.run`) gains an explicit `resource .gas` arm →
  `wordToU256 context.gasleft` (was a context-ignoring alias of
  `Query.defaultAnswer`, which would have answered `0`); other resource arms
  (`msize`) keep `defaultAnswer`. `contextAnswer` moved above `SolI.runFromContext`.
- `SolI.runFromContext` (drives `foldExpr`, constant-expression evaluation) now
  answers via `contextAnswer context` instead of `Query.defaultAnswer` — so it,
  too, returns `context.gasleft` for `resource .gas`; external shapes are
  bit-identical (`contextAnswer` external = `defaultAnswer`).
- `SolI.runWith` (fail-closed corpus responder) gains an **explicit** `resource`
  arm (previously the catch-all): resource queries are a *different* query arm
  from external call/create requests and are answered **ambiently**, never
  matched against the responder's rows nor treated as an unmatched-external miss.
  This context-free fold carries no ambient gas word, so `gas` takes the
  canonical `0` default — behaviour-preserving because **no corpus fixture emits
  a `gasleft` query** (verified: 0 corpus `gasleft` users), so no corpus value
  changes. A context-bearing fold answers with `context.gasleft`.

`buildCallRequest.requestedGas` keeps its current fill rule (explicit `{gas:}`
else ambient `context.gasleft`). Witness: `SolidCore.Witness.GasleftResource`
drives a real `gasleft()` expression through the evaluator and machine-checks (at
`lake build SolidCore` time, throwing `#eval` guard, no axioms) that the
transcript is exactly `[resource .gas]` and the folded value equals the ambient
`context.gasleft` word.

Gate: `lake build SolidCore` + smoke. ROADMAP registry row A3 → fixed.

## 2026-07-06 — A2 design: intra-frame balance accounting (self balance becomes dynamic)

**Problem.** `msg.value` never credited the callee; `address(this).balance` /
`selfbalance` read the static `context.accountBalances` oracle and value sends
wrote nothing. Real EVM credits value before body execution and debits it on a
successful value-carrying call — Solidity-observable.

**Home for the dynamic value: `State.selfBalance : Word`.** `State` is the
dynamic execution state threaded through a call (storage, transient, events,
external interactions). Self balance is a scalar there (this contract's balance);
**other addresses stay environment facts** — `EnvLookup.accountBalance` for a key
≠ `context.self` still answers from the static `accountBalances` map (the
open-world model: the environment owns the world's balances).

**Credit point — re-base at each external entry (`FunctionDef.evalBodyEntry`).**
Before `Stmt.eval` runs the body, set
`state.selfBalance := addWord (balanceAt context.accountBalances context.self) context.value`
(the environment fact for `self`, then credit `msg.value`). This is the external
message-call / constructor entry (constructor-with-value credits identically —
`constructFrom → FunctionDef.call? → evalBodyEntry`). Internal calls are spliced
in `Stmt.eval` and never reach `evalBodyEntry`, so value is credited exactly once
per external frame. `payable` acceptance already exists
(`FunctionDef.acceptsValue`); credit happens only on the accepted path (a
rejected value send reverts with no body, hence no credit).

**Why re-base (from the oracle each entry) rather than thread a persistent
balance across top-level calls.** The corpus witnesses model "the environment
sent ETH to the contract between two calls" by hand-tuning
`accountBalances[self]` in the *later* call's context to the balance observed at
read time (e.g. weth9 `totalSupply` oracle `12`; payment-splitter `400` then
`300` after a release). Re-basing from that oracle at each external entry keeps
those reads correct, while `msg.value` crediting and value-send debiting become
observable **within** a frame. A persistently-threaded balance would instead
shadow the injected oracle (a constructor crediting `0` would pin `some 0` and
override a later `accountBalances := [(self, 400)]`), breaking splitter/escrow.
Re-basing is also simpler: `selfBalance` need not be `Option`-guarded — the entry
always initializes it before any read.

**Debit point — centralized in `Runtime.recordExternalInteraction`.** Every
value-carrying external effect (low-level `call`, `.send`/`.transfer` — which
lower to `Expr.lowLevelCall` with `kind = call` — and `contractCreate` with
value) records an `ExternalInteraction` carrying the result's `kind`/`value`/
`success`. Folding the debit into `recordExternalInteraction` (a single choke
point covering all four emit sites: two `Expr.lowLevelCall` arms, the
`Stmt.tryExternalCall` arm, and both `Expr.contractCreate` arms) keeps the diff
surgical and **off** the `Stmt.eval` call-splicing regions the sibling
function-boundary worktree is rewriting. Debit amount:
- low-level call: `if success ∧ kind ∈ {call, callcode} then value else 0`
  (staticcall/delegatecall/precompiles transfer nothing → 0);
- create: `if success then value else 0`.
Subtraction is floored at `0` (saturating) — an open-world `success = true`
implies the environment accepted the transfer, but we never fabricate a
wrapped-huge balance on an inconsistent oracle.

**Failed-send behaviour.** The environment answers `success = false` → debit `0`
(EVM refunds value to the caller on callee failure). `.transfer`'s revert-on-
failure rolls back the frame anyway; `.send`/`call` observe the un-debited
balance.

**Reads.** `EnvLookup.accountBalance` at its evaluation site reads
`runtime.state.selfBalance` when the key equals `context.self`, else the static
oracle. `address(this).balance` and `selfbalance` both lower to this node with
key `= context.self`.

**Existing balance-touching corpus (audited, all stay green).** With value-`0`
entries the credit is `+0`, so the read equals the oracle base — unchanged:
- `dapphub-weth9` `totalSupply` (oracle `12`, value `0` → `12`); the deposit/
  receive credits are asserted via `balanceOf` storage, not `address(this).balance`.
- `openzeppelin-vesting-wallet`/`payment-splitter`/`refund-escrow`: entries carry
  value `0`; each reads `address(this).balance` (= oracle) *before* sending, and
  the send's debit lands after the read (or in a separate call whose asserted
  getter reads storage). The multi-stage splitter/escrow oracles (`400`/`300`,
  `125`/`44`) are re-based fresh per entry, so the hand-tuned post-release balance
  is honoured.
- Lean witness `checkedAddressMembersMatch` (`accountInfo`): self `.balance` =
  oracle `1000` at value `0` → unchanged; other-address `.balance` = static `77`.

**The one hand-tuned oracle that must change: `base-constructor-runtime-args`
`BalanceArg`.** It is the sole corpus case that both *receives* value (`10`) and
reads `address(this).balance` in the *same* entry (a constructor storing the
balance to slot 0, asserted `== 10`). Its oracle was hand-tuned to the
**post-credit** balance `accountBalances := [(0xcafe, 10)]`; under A2 that
double-counts (`base 10 + value 10 = 20`). Corrected to the **pre-credit
environment fact** `accountBalances := []` (fresh account, balance `0`), so A2's
credit reconstructs `0 + 10 = 10` — matching Forge ground truth (a fresh deploy
funded with `10` wei reports `address(this).balance == 10` in its constructor).
This is exactly the roadmap's flagged case: the lane previously passed *because*
the balance read returned a hand-tuned oracle constant; A2 makes the credit
explicit and moves the tuning to the pre-call fact.

**Pinning (paired Forge lanes).** A dedicated `balance-accounting` fixture covers
the four required scenarios against Forge ground truth: (1) a payable entry
crediting `msg.value` and reading `address(this).balance`; (2) a `transfer`/`send`
debit observable via a subsequent balance read; (3) a failed send (recipient
reverts) leaving the balance un-debited; (4) constructor-with-value crediting.
Fix + lane land together green (`--only`, the W1–W3 pattern).

Gate: `lake build SolidCore` + smoke (weth9 / vesting / splitter / escrow are the
canaries) + the new lane via `--only`. ROADMAP registry row A2 → fixed.

## 2026-07-06 — A2 consistency with the Yul (`../evm-compiler`) balance model

Checked A2's balance model against how the shared Yul/EVM semantics handle
balance (verified by reading `../evm-compiler`, read-only):

- Yul balance is a per-account `UInt256` in the threaded `OpenWorld.accounts`
  map. `SELFBALANCE` reads `codeOwner`'s account; `BALANCE` reads any account by
  address; `CALLVALUE` reads `executionEnv.weiValue`. An outgoing `CALL` with
  value is **debited from the caller and credited to the callee before the
  callee body runs** (reference EVM `Θ`, `thetaCallTransfer` producing `σ₁`
  before `Ξ`), and on failure the whole account map is rolled back — **no net
  transfer**. Across the boundary balance travels only inside the `OpenWorld`
  snapshot (`Query.external` in) and `CallResponse.postWorld` (out).

- A2 lines up **within a single external frame** (the observable it targets):
  `State.selfBalance` is the self/`codeOwner` account entry, read by
  `address(this).balance` *and* written by the outgoing-call debit through the
  same field (matching that `SELFBALANCE`/`BALANCE(self)` and the call debit hit
  one live entry); `msg.value` is credited at `evalBodyEntry` before `Stmt.eval`
  (credit-before-body); the debit fires only on `success` and nothing on failure
  — observationally equal at the caller boundary to Yul's debit-before-body +
  refund-on-failure, since the callee body is environment-answered and never
  observes our self balance mid-call. Other-address `.balance` stays the static
  oracle (= a read of `accounts.find? addr |>.balance`).

- Two **pre-existing checkpoint-1 simplifications** remain (not A2 regressions):
  (1) responders ignore `postWorld`, so self balance moves only via its own
  credits/debits, not via callee-returned world deltas; (2) balance is not a
  threaded `OpenWorld` — cross-call balance is supplied by the static oracle at
  each entry (the environment owning cross-call world state, per the open-world
  model) rather than carried in `postWorld`. The convergence (the Phase 5
  "OpenWorld-shaped environment carried in the source state" future work) folds
  `selfBalance` into a threaded `OpenWorld` and honours `postWorld`, at which
  point Solidity `BALANCE(self)`/`SELFBALANCE` and the outgoing-call debit become
  the same account-map operations Yul performs. A2 is the intra-frame stepping
  stone and does not contradict that direction.

## 2026-07-07 — Combined integration gate: GREEN (101 cases)

Merged `refactor/function-boundary` (1930a38; internal-function boundary,
recursion closed for value signatures) and `gaps/balance-gasleft` (2536503; A2
dynamic self-balance, A3 gasleft resource query) onto main (which carried the
W1–W3 soundness fixes and the ecdsa fail-closed fix 883fc52). Conflict
resolutions: manifest three-way composed programmatically (zero double-edited
cases; recursion-gap inserted), Interpreter's evalBodyEntry composed BOTH sides
(fnboundary's `table` parameter + A2's selfBalance credit-before-body), DECISIONS
append-append. Combined gate on the merged tree: `lake build SolidCore` green
(1096 jobs — the cross-branch `call?_reverted_rolls_back` theorem composed and
reproved), full replay `forge_interpreter_compare=pass`, `cases=101`,
`paired_cases_passed=yes`, zero failures. The corpus now pins: recursion/deep
call chains (recursion-gap), balance accounting (balance-accounting), packed
narrow-int hashing, shift truncation, signed exponentiation, rational constants,
and the fail-closed ecdsa precompile rows.

## 2026-07-07 — openworld/postworld Stage 0: total, solc-faithful typed storage reads

Per `docs/openworld-postworld-plan.md` §2.6 (orchestrator ruling #2: typed reads
of non-canonical storage words are TOTAL and solc-faithful, never fail-closed).
Ground truth: solc 0.8.35 `--ir` probes (`/tmp/solc-probes/EnumUse.yul`) — the
storage read pipeline `read_from_storage_split → cleanup_from_storage_t_X` never
reverts for any type; validation happens at *use* sites via `cleanup_t_X`.

Fixes landed (`Ty.storageValueFromWord?`, `Interpreter.lean`):

- **bool**: fail-closed reject of w ∉ {0,1} → total `and(w,0xff)` +
  truthiness; canonicalized to {0,1} on read (observationally identical to
  solc's read-mask + use-site `iszero(iszero(·))`; a non-canonical bool is
  unobservable).
- **address**: no mask → `and(w, 2^160-1)` on read.
- **bytesN**: identity → mask to the low 8N bits (our internal convention is
  right-aligned; solc's `shl(256-8N,w)` drops the same bits above the lane).
- **enum**: the big one. New Source-layer `Ty.enumStorage (maxValue)`, produced
  ONLY in storage layouts (`Ty.toCoreStorageLayout?`/`toCoreStorageMemberLayout?`
  lower AST `Ty.enum` to it; ABI params/returns/locals keep the erased
  `uint256` + `AbiCleanup.enum` lowering). Read masks the lane byte and is
  total; an in-range word stays a bare `Value.word` (zero representation change
  on canonical data), an out-of-range word is wrapped
  `Value.abiLazy (AbiCleanup.enumStorage max)` — a *deferred use-site
  validator*. Forcing an `enumStorage` cleanup rejects with **Panic(0x21)**
  (`validator_assert_t_enum`), while the calldata-decode `AbiCleanup.enum`
  keeps the **empty revert** (`validator_revert_t_enum`) — solc has BOTH
  validators and the abi-malformed Forge lane pins the empty calldata one.
  Use-site forcing added at `BinaryOp.apply` (comparisons/arithmetic),
  `uintCast?`/`intCast?`/`uintCleanup?`/`intCleanup?` (conversions),
  `enumFromUIntValue` (enum-to-enum revalidation), and `coerceStorageWordAs`
  (storage writes; solc's `update_storage_value` validates) — returns/getters
  already force through `collectReturnBindings`' deref. A bare load-and-drop
  (`E x = e; x;`) stays silent, exactly like solc's `fun_loadOnly` probe.
- **intN / function-type**: verified already faithful on this tree
  (`intCast?` is total on the packed lane; `externalFunctionValueFromStorageWord`
  already masks the address to 160 bits via `Account.addressWord`). Pinned by
  lanes, no code change.

Known corners (documented, not lane-pinned): an out-of-range storage enum
reaching `abi.encode`/event-data encoding directly (without a variable read or
return in between) rejects through the Option-typed encoders as a generic
revert rather than Panic(0x21); solc timing places the panic at the encode.
Revisit only if a fixture ever observes it.

**Lane**: new paired case `storage-dirty-words` (corpus 101 → 102): Forge
plants non-canonical words via `vm.store` (bool slot=2 truthy / high-bits-only
falsy; enum slot=7 → Panic 0x21 from getter, `==` compare, and `uint256(·)`
conversion; enum `2^200+1` → masked in-range read; address high-bit drop;
bytes4 lane mask; packed uint8/int8 mask + signextend), Lean plants the same
words via `State.storeSlot` on the solc-AST-imported contract — 5 Forge tests
+ 15 paired Lean evals, all green via `--only storage-dirty-words`.

This stage is independent of the postWorld arc but is what makes wholesale
`postWorld` adoption total: any word the environment writes into our storage
now has defined, solc-faithful read semantics.

## 2026-07-07 — openworld/postworld Stage 1: real outgoing `OpenWorld` snapshots

`emitLowLevelCall`/`emitContractCreation` (and the precompile wrapper) now
carry `snapshotWorld context state` in every `Query.external`, replacing the
checkpoint-1 `default` placeholder — the mirror of Yul's `callEval`/`createEval`
→ `ofYulShared`. The snapshot is a pure projection (plan §2.1):

- self account: `State.storage`/`State.transient` verbatim (slot ↦ word into
  `EvmYul.Storage`), A2 `State.selfBalance`, new `State.selfNonce := 0`
  (carried so the adoption round-trip law will hold field-wise; nothing reads
  it), code from `Context.accountCodes`;
- other accounts: one `OpenAccount` per Context-seeded address — balance/code
  from the seed maps, storage/transient empty (we assert nothing), nonce 0;
- substate: `logSeries` = `State.logEntries` projection, `selfDestructSet`
  from `State.selfdestructs`; access sets/refund `default` (declared fidelity
  gap, recorded not hidden);
- `createdAccounts` from `Context.createdInTransactionAccounts`.

Emit helpers gained a `state : State` parameter; the six evaluator call sites
pass the post-argument-evaluation `runtime'.state`. Corpus-neutrality verified
by full replay (matchers key on kind/target/calldata/value/gas only and every
`Query.external` match wildcards the world) — zero fixture edits. New
build-time witness `snapshotWitnessMatches` (Witness/InterpreterExamples.lean)
pins a non-default snapshot: live storage/transient words, balance 77,
nonce 3, code bytes, one log entry, a seeded other-account balance, and a
created-accounts seed all appear in the emitted query; a regression to the
`default` placeholder fails `lake build SolidCore`.

## 2026-07-07 — openworld/postworld Stage 2: wholesale postWorld adoption, echo answers

The arbitrary-changes model is wired end to end (mirror of Yul's
`withWorldAndMachine` → `installYulShared`), behavior-preserving by
construction under the echo convention:

- **Adoption** (`adoptWorld`): on every call/create resume, the answered
  `postWorld`'s self account lands on the existing `State` fields — ordinary
  slot-keyed wholesale replacement of the `WordMap`s (ruling #1: no
  representation change), `selfBalance` (A2's field), `selfNonce`. Self absent
  from the answered accounts ⇒ the empty account (total, like
  `installYulAccounts`). The answered world is retained VERBATIM in
  `State.envWorld?`, which owns the other-account facts, self code, substate
  extras, and `createdAccounts` after adoption; the four Context maps are now
  documented seed-only, and env reads (`.balance` of others, `.code`,
  `.codehash`, extcodesize-style checks, created-accounts set) route through
  `State.env*` accessors (adopted world first, seeds pre-adoption — risk R3's
  single-accessor mitigation).
- **Snapshot after adoption**: `worldMutatedSinceAdoption` (set by every State
  mutator) selects between returning `envWorld?` VERBATIM (nothing mutated) and
  overlaying it with the live self account + canonical log series +
  new selfdestruct records.
- **Logs** (risk R1, split-point variant): canonical series =
  `adoptedLogPrefix ++ (events.drop adoptedEventCount)` projection — `events`
  stays CUMULATIVE, so every existing `state.events` assertion is untouched
  (audited: full replay green with zero fixture edits). Same split-point
  pattern for the selfdestruct set. Callee logs arrive by adoption of the
  answered series — logs are substate, not caller-local (risk R2: a fixture
  asserting "logs survive calls" asserts a property of the responder, not the
  semantics).
- **Echo everywhere**: `ScriptedResponder.answerCall?/answerCreate?` now take
  the sent world and answer `postWorld := sent world` for delta-less rows —
  `Query.defaultAnswer`'s convention (`contextAnswer` already had it). The
  world never participates in row MATCHING (fail-closed rules unchanged).
  A failed create echoes automatically (risk R7). A2's debit stays in
  `recordExternalInteraction` at this stage (pure echo + existing debit =
  today's behavior; the §3.1 debit fold happens at Stage 3 when the
  responder computes post-debit worlds and the record-side debit is deleted —
  the plan's "+ A2-debit fold" is sequenced there to avoid double-counting).

**Round-trip laws (proved, `SolidCore/Solidity/AdoptionLaws.lean`)**:

- `snapshotWorld_adoptWorld : snapshotWorld context (adoptWorld w context s) = w`
  — for EVERY `w`, with plain `=` (the exact mirror of
  `ofYulShared_installYulShared`). Exactness comes from verbatim retention:
  adopt keeps the world, an unmutated snapshot returns it unchanged — the same
  no-surgery design as the Yul side.
- `adoptWorld_idempotent`.
- `adoptWorld_echo_noop`: on the rebuild branches (pre-adoption or mutated),
  adopting the echo of your own snapshot preserves every observable component:
  `loadSlot`/`loadTransientSlot` extensionally (up to `norm`, which every read
  applies; canonical stores are already normalized), balance/nonce up to
  `norm`, and `events`/`externalInteractions`/`immutables`/`selfdestructs`
  exactly. Adopted-clean states are covered exactly by the first two laws.
  Proof infrastructure: `Std.TransCmp`/`Std.LawfulEqCmp` bridge instances for
  the shared `UInt256`'s derived `Ord`, a foldr-based `wordMapToStorage`
  (first-occurrence semantics aligned with `WordMap.lookup?`), and an
  RBMap-`toList`/`find?` correspondence via Batteries' sortedness lemmas.

Gate: `lake build SolidCore` green (laws included), full replay `--jobs 10`
green with ZERO fixture edits (echo adoption is invisible to the corpus, as
the laws predict).

## 2026-07-07 — openworld/postworld Stage 3: PostDelta responder rows, reentrancy lanes, A2-debit fold

The flip: responder rows can now carry real world changes, and the A2 debit
moved into adoption. Behavior-preserving for delta-less rows.

- **`PostDelta`** on responder rows (`OracleRow.callWithPost`/`createWithPost`):
  model-level, ordinary slot-keyed writes into the same maps (ruling #1) —
  `selfStorageWrites`, `selfTransientWrites`, `selfBalance?` (absolute),
  `selfNonce?`, `otherAccounts` (balance/code of others), `appendLogs`,
  `createdAccounts`. `PostDelta.apply self base` layers them onto the echo
  world; `answerCall?`/`answerCreate?` compute
  `postWorld := PostDelta.apply self (debit-folded echo) delta`.
- **A2 debit fold**: the value-transfer debit left `recordExternalInteraction`
  (which now only records the interaction transcript) and became
  `OpenWorld.debitSelf` applied to the echoed world inside the responder,
  gated by the same success/kind table (`ExternalInteraction.selfBalanceDebit`).
  A row's explicit `selfBalance?` REPLACES the debit (no double-count) — this
  is what lets the balance-refunding lane pin that adoption, not the debit, is
  authoritative. Delta-less rows: debit-folded echo == the old
  record-side debit + echo, so the full corpus is unchanged (verified by
  replay: balance witnesses green, zero edits). `answerCreate?` also rejects an
  ill-formed row (failed create + nonempty delta, risk R7) fail-closed.
- **`reentrancy-adoption` lane** (corpus 102 → 103): the ReentrancyAdoption
  Forge fixture runs REAL reentering callees and the deltas are derived from
  its trace (Forge is ground truth):
  1. reentrant-storage-write — attacker reenters `setX(42)`; `pull()` returns
     42 and `x()` reads 42 after (`post.selfStorageWrites := [(0,42)]`).
  2. reentrant-ill-encoded-then-read — the reentering world plants `flag=2`
     (slot 1) / `choice=7` (slot 3); post-call the bool getter reads truthy
     (1) and the enum getter Panics 0x21 — Stage 0 total reads exercised
     THROUGH Stage 3 adoption (the marquee lane).
  3. balance-changing-callee — victim funded 100, spends 40, callee refunds 20;
     `post.selfBalance? := 80` overrides the naive 60 debit; `spend()` reads 80.
  4. transient-storage-mutation — `tk:=1`, callee reenters `bump()`;
     `post.selfTransientWrites := [(0,2)]`; observed `tk == 2`.
  5. create-with-reentry — child constructor reenters `setX(7)`; create row +
     `post.selfStorageWrites := [(0,7)]`; `deploy()` returns 7, `x()` reads 7.
  All five Forge tests green; all five paired Lean evals green; storage layout
  (flag/choice slot packing) and the missing `receive()` were both Forge
  ground-truth corrections, not papered over.

This **supersedes** the Phase 5 fail-closed re-projection policy of
`docs/DECISIONS.md:310-319` and the ROADMAP self-storage "fail-closed
re-projection" resolution: with Stage 0 total reads there is no layout-encoding
inverse and no environment well-formedness hypothesis — the arbitrary-changes
model is exact and the round-trip law is `=`.

Gate: `lake build SolidCore` green, `--only reentrancy-adoption` green, full
replay `--jobs 10` green (103 cases, zero pre-existing fixture edits).
## 2026-07-07 — Tuple-with-hole assignment: importer coverage-audit gap (one line), core already complete

The interpreter core, surface AST, typechecker, and executable elaboration
**already modelled tuple holes end-to-end** before this change: `TupleItem.hole`
threads through every `Interface.lean` pass, `TupleItems.toCoreLValueTargets?`
lowers `.hole` to a `none` slot in the `List (Option CoreLValue)` that
`LValues.writeTuple` consumes, and `VarBindings.toCoreTupleTargets?` maps a
name-less declaration binding to `none`. The prior work (May 2026, archived) had
already pinned holes in binding positions at the checker/executable level.

The **only** remaining break was in the solc-AST importer's *coverage audit*
(`scripts/solc_ast_to_lean_source.py`), not its renderer. `tuple_item_from_node`
and `var_binding_from_node` already render a `null` component as `TupleItem.hole`
/ `{ name := none, … }`. But `iter_scalar_fields` treats a `null` entry inside a
list as a scalar leaf, so a `TupleExpression.components` list containing a hole
surfaced as an *unclassified scalar field* and the audit hard-failed with
`unclassified Solidity AST scalar fields present: TupleExpression.components`.
The declaration-hole path had already been worked around by registering
`('VariableDeclarationStatement', 'declarations')` in `SOURCE_SCALAR_FIELDS`; the
analogous `('TupleExpression', 'components')` entry was simply missing. **Fix:
one entry added to `SOURCE_SCALAR_FIELDS`** — no Lean source changed. (`null`
in a solc AST list is always a structural hole, never scalar data, so
classifying that field as a known source scalar is safe; the frontend audit
stays green: `render_failures=0`, `unknown_source_scalar_value_fields=0`.)

**solc 0.8.35 accept/reject boundary probed** (pinned artifact). Accepts:
leading / middle / trailing holes in both tuple **assignment** LHS (`(a,) = …`,
`(,b) = …`, `(a,,c) = …`) and **declaration** LHS (`(uint a,) = …`, etc.),
nested holes (`((a,),(b,c))`, `((a,b),)`), and the canonical low-level-call idiom
`(bool ok, ) = t.call{value:1}("")` (assignment and leading-hole variants too).
Rejects: a fully-empty tuple target `(,)` — a **parse** error ("Expected primary
expression"), so it never reaches our importer — and hole + arity mismatch
(`(a,) = (1,2,3)` type-mismatch; `(uint a,) = (1,2,3)` "Different number of
components"). We accept exactly the accepted forms and keep rejecting the rest.

**Semantics verified**: a held-out component is not *bound*, but its RHS
computation still runs. Pinned with a storage post-increment in the held-out
slot (`(a,) = (7, pokes++)` etc.): the interpreter bumps `pokes` exactly as solc
does. (An internal-function call in a tuple-literal RHS — `(a,) = (7, poke())` —
is a *separate, pre-existing* executable-lowering gap unrelated to holes; both
the hole and no-hole forms fail it, so the side-effect fixtures use `pokes++`,
which lowers and evaluates cleanly. Left untouched — it is the internal-call
elaboration surface owned elsewhere.)

**Pinned by a new `tuple-holes` corpus lane** (kept `tuple-destructure` intact):
5 Lean evals — importer acceptance, `assignTrailingHole`=71 / `assignLeadingHole`
=91 / `declMiddleHole`=351 (leading/middle/trailing holes with a side-effecting
RHS, all own-call), and the canonical `callTrailingHole` value-carrying idiom
observing the send debit (self balance 10 → 9, returned `bytes` held out, via the
`responderOfResults` + `accountBalances` pattern reused from `balance-accounting`)
— plus 3 `solc_rejects` (`AllHolesAssignment`, `HoleAssignmentArity`,
`HoleDeclArity`). Corpus now 102 cases, 445 lean_evals (+5), 314 solc_rejects
(+3). Gates: `lake build SolidCore` green (no Lean delta), `scripts/smoke_replay.sh`
green (28 cases), `--only tuple-holes` and the nearest neighbours
`--only tuple-destructure --only low-level-call-options` green, frontend audit
green. A full replay was not required for this importer-only scoped fix.

## 2026-07-07 — solc ground-truth research for the boundary-completion arc

Before launching the residue-removal arc (task #9: storage-ref returns,
internal function pointers, calldata-ref callees, tuple-literal-component
hoisting, splice deletion), we probed the pinned solc 0.8.35 via-IR pipeline
directly (`--ir` on four minimal fixtures) so the implementing agent designs to
solc's actual mechanisms. Findings recorded in
`docs/refs-completion-solc-research.md`. Load-bearing facts:

- **Storage-ref returns** are a single slot word returned from the Yul
  function; the caller binds it as a plain local. Confirms stage A is pure
  `Value.storageRef` flow with no new value forms.
- **Internal function pointers** are sequential numeric IDs (0 = invalid /
  uninitialized), called through a per-arity `dispatch_internal_in_m_out_n`
  switch whose `default` is `Panic(0x51)`. They are **storable** (8-byte
  packed storage type; read cleanup = 64-bit mask, validity checked only at
  call time). Consequence for stage C: the interpreter's fn-pointer `Value`
  needs a word encoding (per-contract ID + ID→table-key map), a Panic-0x51
  miss path, and a 64-bit-mask row in the dirty-word storage-read table —
  which also makes postWorld-adopted dirty words in fn-pointer slots behave
  exactly as solc does, with no adoption carve-out.
- **Calldata refs** cross internal boundaries as plain `(offset, length)`
  word pairs (dynamic) or a single offset word (static); slices are adjusted
  pairs. Stage D should flow a descriptor, not exclude.
- **Tuple-literal RHS components** evaluate left-to-right into temps, all
  before any assignment; holes still evaluate their component. Stage B must
  NOT reuse the right-to-left call-argument hoisting order.

Task #9's description was updated to carry these constraints inline.
## 2026-07-07 — Function-boundary refactor, reference-signature extension: memory-ref + storage-ref-parameter callees onto the boundary

Branch `refactor/ref-signatures` (worktree, based at the integrated tip
`11350cd`). Extends the internal-function boundary (`Stmt.internalCall` +
`Contract.table`, landed for value signatures) to **reference-signature
callees**: callees whose parameters are stack values, `memory` references, or
`storage` references, and whose returns are stack values or `memory` references.
Reference-signature recursion / deep nesting through these signatures now
elaborates and runs (previously silently rejected via the retained inline fuel).

### Semantic model (as implemented)
- **Memory refs = pointer pass-through.** A `T memory` argument flows as its
  `Value.memoryRef` pointer; the callee frame binds the pointer (not a copy), so
  callee mutations alias back and a returned memory pointer aliases the caller's
  object. The heap is shared (frames replace `locals` only).
- **Storage refs = flowing runtime values.** A `T storage` argument flows as a
  `Value.storageRef`/`storagePathRef` runtime value (solc's model: a storage
  pointer is a plain argument), bound into the callee frame; the callee's storage
  accesses resolve through it against the shared `state`. No elaboration-time
  alias substitution.

### Interpreter groundwork (`Interpreter.lean`, function-boundary region only —
away from the postWorld snapshot/adoption/emit/read-helper regions)
- `Expr.evalRefArgWithRuntimeOrder` + list form: reference-PRESERVING argument
  evaluation for the `internalCall` arm. A `Expr.var` bound to a storage/memory
  reference yields the pointer VALUE (not the dereferenced load); everything else
  falls through to ordinary eval, so value calls are byte-identical.
- `BindingDecl.bindArgRef?`/`bindArgsRef?` + `InternalFunction.initialFrame?`:
  reference-preserving parameter binding (`Ty.coerceValue?` has no reference
  case, so ordinary binding would reject a pointer). Entry path
  (`FunctionDef.initialFrame?`) untouched.
- `collectReturnBindingsRef`/`coerceReturnBindingsRef`: preserve memory/storage
  pointers on return (memory returns alias; storage-return coercion has no value
  case); non-reference returns dereference-and-coerce exactly as the shared
  collectors, so the entry path (which must abi-value memory returns and never
  returns storage pointers) is untouched.
- `Runtime.assignLocalRefAware?`/`assignNamedValuesRef?` + `internalCallAssign`:
  a returned storage pointer re-points the caller's storage-alias target
  (`assignStorageRef?`), not `coerceLike?` (which has no reference case).
- Witnesses (`SolidCore/Witness/InternalCall.lean`): storage read-through,
  storage-ref return re-pointing, value-argument inertness.

### Elaboration (`Interface.lean`)
- `FunctionDecl.isBoundaryCallee` (was `isValueBoundaryCallee`): now admits
  callees whose params are `isBoundaryLocation` (value / `memory` / `storage`, NOT
  `calldata`, NOT function-typed) and returns are `isBoundaryReturnLocation`
  (value / `memory`, NOT `storage`, NOT `calldata`, NOT function-typed). Used
  identically at the call-site emit and every table-build site.
- `Parameters.boundaryArgDecls?` (was `valueBoundaryArgDecls?`): reuses
  `Parameter.toStorageAwareCoreArgDecl?` to build one reference-preserving temp
  per argument — `storage` → `storageAlias*` (binds the pointer value), `memory`
  → `memoryVarDecl` (aliases a bare memory variable's pointer via
  `memoryRefOrValueWithRuntimeOrder`), value → `varDecl`. Temp name forced to
  `_ic_arg_<i>` (never the parameter name). Node args are the temp reads,
  evaluated reference-preservingly by the arm.
- `FunctionDecl.boundaryCallParts?` (was `valueBoundaryCallParts?`): the return
  decls were already storage-aware (`toStorageAwareDefaultCoreDecls?` +
  `storageRefFlags`); only the arg construction changed. Threads `storageRefEnv`.
- `FunctionDecl.internalTableKey?`: **collision fix.** The ABI canonical
  signature collapses user types (every one-field struct → `(uint256)`, every
  enum → `uint8`, every user type → `address`). Two overloads differing only by
  such a type (`div_(Exp memory,Exp memory)` at 1e18 vs
  `div_(Double memory,Double memory)` at 1e36 — the compound-exponential
  regression) would share a key and misdispatch. The key now appends a structural
  identity of the parameter types (derived `repr`, preserving struct/enum/user
  identity), computed identically at both sites from the same resolved decl.
- `FunctionDecl.toCore?`: registers `storage`-ref RETURNS in `storageRefEnv` and
  runs `rewriteStorageReturnAssignments` (parity with the splice path), so a
  boundary storage-ref-return callee's body treats its return as a storage
  pointer. Inert for value returns and impossible for entry functions — kept as
  forward-groundwork for the deferred storage-ref-return slice below.

### Residues (deliberately deferred — splice path retained; `defaultInternalCallInlineFuel` NOT deleted)
- **Storage-ref RETURNS** (`uint256[] storage`-returning callees:
  `pointer-return-definite`, `function-type-locations`'s storage fn-pointer,
  `override-data-locations` internalStorage). Excluded by
  `isBoundaryReturnLocation`; they stay spliced (green). The interpreter carries
  storage-ref returns correctly (proved by the `InternalCall` witnesses) and the
  callee-body groundwork is in place (above), but the CALLER-side capture wiring
  for a storage-ref-return NODE (aliasing the caller local to the returned
  pointer through the wrapper callers) is not yet complete — the boundary version
  still computed a wrong value where the splice path is correct. Precise residue:
  finish the wrapper-caller (`internal*CallCore?`) storage-ref-return capture,
  then drop the `storage` exclusion from `isBoundaryReturnLocation`.
- **Function-typed callees** (`frontend-frontier` `acceptInternalPure`,
  `function-type-locations` fn-pointer locals). Excluded: there is no
  internal-function-pointer `Value` constructor (only `Value.externalFunction`);
  adding one is broad `Value`-match blast radius and overlaps the sibling
  postWorld agent's `Interpreter.lean` surface — recorded, not attempted here.
- **Calldata-ref callees** excluded (no flowing calldata-reference value yet).
- **Internal call in a tuple-literal RHS component** (e.g. `(a,) = (7, poke())`,
  `(x,y) = (f(), g())`) still fails elaboration — the stage-3 expression-position
  hoisting does not cover the tuple-literal-component position (flagged by the
  tuple-hole agent; adjacent to this surface but a distinct hoisting shape). NOT
  covered by this work; queued as named residue.

### Splice deletion (stage 4): still deferred
The splice path remains the live elaboration for storage-ref-return, calldata,
and function-typed callees, so `defaultInternalCallInlineFuel` + its consumption
sites and `functionExpandModifiersToCoreWithStorageRefsOnly?` cannot be deleted.

### Merge note
Main advanced past this branch's base (`11350cd`): postWorld arc `d52bb82`
(Interpreter.lean snapshot/adoption; State `envWorld?`/`selfNonce`; A2 debit moved
into the responder echo) and tuple-hole `d390609` (importer-only). This branch is
NOT rebased. Interpreter.lean edits here are confined to the function-boundary
call machinery (arm, frame build, return mapping, ref-preserving arg eval) —
expected disjoint from the adoption/emit/responder regions; the merge should
compose in Interpreter.lean with care, and the manifest via the established
programmatic three-way compose.

### Gates
Per-commit: `lake build SolidCore` green; the five reference/pointer/function
sentinels (`reference-internal-memory-boundaries`, `reference-mapping-storage`,
`reference-assignments`, `pointer-return-definite`, `local-pointer-definite`,
`function-type-locations`) green via `--only`; smoke green; a broad Lean-only
replay over the heavy OZ `using`-for storage-ref fixtures (enumerable-set/map,
checkpoints, bitmaps, counters, arrays, timers, double-ended-queue, merkle-proof)
and the memory-struct-heavy compound-exponential lane — all green. Full
`--jobs 10` replay is the closing gate.

## 2026-07-07 — Boundary-completion arc (stages A–E): all reference signatures on the boundary; splice deleted

Branch `refactor/ref-signatures`, continuing from the reference-signature
extension entry above. Designed against direct `--ir` probes of the pinned
solc 0.8.35 (`docs/refs-completion-solc-research.md`, imported at `22597bd`).
One commit per stage; smoke + relevant sentinels per stage; single full
`--jobs 10` replay as the closing gate.

### Stage A — storage-ref RETURNS (research §1)
solc via-IR returns exactly ONE word (the slot) from a `T storage`-returning
internal function; the caller binds it as a plain local. Mirror: the flowing
`Value.storageRef`. The missing piece was the CALLEE-side binding:
`BindingDecl.isStorageRef` (defaulted `false`) makes `defaultBinding` bind a
storage-ref named return to `Value.storageRef uninitializedStorageReturnTarget`
in the callee FRAME — the body's re-points (`storageAliasAssign*`, which assign
through scopes into the frame) and the reference-preserving return collection
then see a storage pointer that survives block scope pops (a declaration-based
prologue was rejected for exactly that scope-pop failure mode, witnessed).
`isBoundaryReturnLocation` stopped excluding `storage`.

### Stage B — tuple-literal RHS components (research §4)
solc evaluates tuple-literal components LEFT-to-right, each into its own temp,
ALL before any assignment; a hole's component still evaluates. New arm for the
assignment form + extension of the list-level varDecl-tuple arm, both reusing
`tupleItemsUseCoreWithInternalCalls?` (the L-to-R temp sequencing already
pinned for `return (f(), g())`); the no-call form keeps today's path (tried
first). NOT the right-to-left yulCompatible call-arg order. Importer: null
tuple components classify as source scalars (same hunk as main's `d390609`).
Lane `tuple-literal-hoist` (assignment/hole/decl forms, storage order-log).

### Stage C — internal function pointers (research §2)
solc via-IR: an internal fn-pointer value is a small sequential dispatch ID
(0 = uninitialized/deleted), assigned 1..n to the functions used as VALUES, in
first-use order; a call through a pointer is a dispatch switch whose default is
`Panic(0x51)`; the storage type is 8 bytes with a 64-bit-mask read cleanup and
NO read-time validity check. Mirrored exactly:
- `Value.internalFunction (id : Word)`, core `Ty.internalFunction`, core
  `Expr.internalFunction` literal; rows for default (0), coercion (identity),
  storage read (64-bit mask — the dirty-word row; adoption-planted words in
  fn-pointer slots behave exactly as solc, no carve-out), storage write
  (8-byte packed slice), no ABI form.
- `InternalFunction.id? : Option Word` (+ `FunctionDef.dispatchId?` →
  `Contract.table`); `Stmt.internalCallPtr` evaluates the pointer expr FIRST,
  then args; table miss (incl. 0) → `RevertData.panic 0x51`; hit → the
  ordinary framed call.
- Elaboration: per-contract numbering (`FunctionDecls.internalFnValueNumbering`
  — value-position identifiers, call-callee slots excluded, first-use order);
  fn-value identifiers rewrite to dispatch-ID number literals AFTER alias
  inlining (statically-resolvable fn-ptr locals keep the alias path);
  `Expr.toCoreAsWithEnv?` turns a number literal in an internal-fn-typed
  context into the pointer literal (typechecker-unreachable otherwise);
  unresolvable call names fall back to `ptrBoundaryCallParts?` (params/returns
  from the function TYPE); nested ptr-call args hoist through the same gates
  as direct calls (`directOrPtrCallArgReturnTy?`).
- **Eval-frame regression + fix**: inlining the ptr arm into `Stmt.eval` grew
  the compiled frame past the stack budget — five corpus lanes segfaulted
  (exit 139). The frame build + result mapping of BOTH call arms moved out of
  the mutual block (`internalCallEnter?`/`internalCallFinish`); the eval frame
  is now smaller than pre-arc. Recorded as a standing constraint: the eval
  block recurses once per statement, so its compiled frame size bounds usable
  program depth — keep its arms thin.
- Lane `internal-fn-pointers`: storage round-trip with data-dependent pointer,
  pointer as internal arg (incl. `f(f(x))`) and return, uninitialized call →
  Panic 0x51 (Forge-paired via low-level call), recursion through a runtime
  pointer. Witnesses additionally pin dirty-word masking end-to-end.

### Stage D — calldata-ref callees (research §3)
solc passes a dynamic calldata ref as two plain words (offset, length) — a
pure READ descriptor (calldata is immutable). This semantics materializes
calldata into immutable `Value`s at the ABI boundary, so passing the value is
observationally identical to passing the descriptor; slices are value slices.
Survey found no incompatibility → exclusion lifted (the research's preferred
outcome), no new machinery. Lane `calldata-ref-internal` (params, slice
returned from an internal fn, recursion over a calldata array).

### Stage E — splice deletion + closure
- `internalTableKey?` made TOTAL over named functions: when `abiSignature?`
  fails (mapping-typed storage params — OZ EnumerableSet/Map), the name + the
  structural repr suffix still key the table.
- Storage-located params with no core type form get a placeholder core Ty and
  `AbiCleanup.none` (the binding is reference-preserving, so the declared core
  Ty of a storage-ref binding is never consulted; ABI cleanups are entry-only
  and mapping params cannot reach an ABI entry).
- DELETED: the α-renaming inline-splice bodies of `internalCallParts?` (both
  branches), `functionExpandModifiersToCoreWithStorageRefsOnly?`, the
  `Stmt.toCoreWithStorageRefsOnly?`/list mutual cluster,
  `Parameters.toStorageAwareCoreArgDeclsWithInternalAliases?`,
  `Parameters.runtimeAliasEnv` (net −315 lines). No callee kind splices.
- KEPT deliberately: (1) `defaultInternalCallInlineFuel` — renamed in ROLE,
  not name: it no longer bounds inline expansion (that path is gone, and with
  it the recursion rejection); it survives only as the nested-call-argument
  hoisting bound (syntactic depth of `f(g(h(...)))` within one expression) and
  as the decreasing Nat of the elaboration cluster's termination measure.
  Deviation from the plan's "delete the constant", recorded honestly: removing
  the parameter threading entirely is a large mechanical follow-up with no
  semantic content. (2) The internal-function ALIAS-inlining machinery
  (`inlineInternalFunctionAliases*`) — statically-resolvable fn-ptr locals are
  still substituted before the ID rewrite; behavior-identical, and deleting it
  would force every static use through the dispatch table for no semantic
  gain. (3) Modifiers stay inlined (unchanged posture).
- Residues (recorded, all pre-existing rejections — no acceptance regressed):
  member-form fn-value uses (`Lib.f` as a value) [**Fixed 2026-07-07**, see
  entry below], fn-pointer VALUES in constructors and modifier bodies
  (fn-pointer CALLS and all other uses work) [**Fixed 2026-07-07**, see entry
  below], and tuple-literal hoisting only for the assignment/declaration
  statement forms.
- Lane `recursion-ref-signatures`: recursive linked-list walk over a mapping
  via `Node storage` (=60), recursion over `uint256[] memory` incl.
  mutation-through-pointer aliasing (=15099) — the residual recursion-gap
  slice, now green against Forge.
- ROADMAP registry row → **Fixed — all signatures**.

Corpus: 105 cases (tuple-literal-hoist, internal-fn-pointers,
calldata-ref-internal, recursion-ref-signatures added; each pins researched
solc behavior with Forge as ground truth). Closing gate: full `--jobs 10`
replay (results in the final gate record below).

### Closing gate (boundary-completion arc)
Full paired replay, `--jobs 10`, all **105/105 cases pass** (103 Forge-paired +
2 Forge-skipped-by-config; `status=0`). Zero failures. The four new pinning
lanes — `tuple-literal-hoist`, `internal-fn-pointers`, `calldata-ref-internal`,
`recursion-ref-signatures` — pass Forge-paired. The full-replay run caught one
truth-value drift (frontend-frontier: a public state variable overriding a
virtual function collided with the fn-pointer numbering candidates — fixed by
excluding `storageNames` from candidates), which is exactly the kind of
frame-isolation/name-resolution edge the arc's R-risks flagged; re-run clean.
The inline-splice machinery is gone and every internal-linkage callee — value,
memory-ref, storage-ref (params + returns), calldata-ref, and function-pointer
— executes as a framed in-monad boundary call.

## 2026-07-07 — perf/storage-map-swap, cause #1: HashMap-backed storage/memory/immutable maps

### Problem
The heaviest storage-read-heavy OZ contracts (openzeppelin-erc20, access-control,
erc1155-pausable-supply, erc721-royalty, erc721-uri-storage) exceeded the 300 s
per-case replay budget (350–700 s single-threaded). Correctness was fine — pure
speed. The dominant driver was O(m·n) storage access:

- `WordMap`/`MemoryMap`/`ImmutableMap` were assoc lists (`List (K × V)`); every
  `lookup?`/`insert` did a linear scan.
- `wordEq lhs rhs := norm lhs == norm rhs` ran **two** bignum `% 2^256` mods per
  comparison, and storage keys are full 256-bit keccak hashes.
- A balance-mapping / EnumerableSet loop doing `m` ops over an `n`-slot store is
  O(m·n) with a bignum constant.

### Change (file:line at commit)
`SolidCore/Solidity/Interpreter.lean`:
- `abbrev StorageMap := Std.HashMap Word Word` (~752) backs `State.storage` /
  `State.transient` (fields ~838–839); `StorageMap.lookup?`/`insertLoop`
  (~754–759) normalize key **and** value at insert and query the HashMap in O(1)
  expected. `State.loadSlot`/`storeSlot`/`loadTransientSlot`/`storeTransientSlot`
  and `State.empty`/`clearTransient` updated to the new type.
- `abbrev MemoryMap := Std.HashMap Nat Value` (~797) backs `Runtime.memory`.
- `abbrev ImmutableMap := Std.HashMap String Value` (~808) backs
  `State.immutables`.
- `Repr` instances for the three (render via `toList`) since `State`/`Runtime`
  derive `Repr`.
- `WordMap` (assoc list) **kept** — it now backs only the small, cold `Context`
  seed maps (`accountBalances`/`accountCodehashes`), which are iterated by key at
  snapshot boundaries and read via `Account.lookupWord?`.
- Bridges `wordMapToStorage`/`storageToWordMap` (~1961) rewritten for the HashMap
  (fold / `toList.foldl`).

`SolidCore/Solidity/AdoptionLaws.lean`: the adoption round-trip meta-theorems
(`lookup?_roundtrip`, `find?_wordMapToStorage`, `lookup?_storageToWordMap`, and
`adoptWorld_echo_noop`) reproved for the HashMap representation. They gained a
`StorageMap.WF` (canonical-keys/values) hypothesis — required because the new
`StorageMap.lookup?` matches keys by exact `norm`-query equality, so the law is
false for a hand-built HashMap with a non-canonical physical key; **every**
interpreter-built `StorageMap` is WF (keys/values normalized at every insert;
`{}` trivially). No `sorry`/axioms.

Lean witness expressions adapted to the new types (not the frozen `.sol` corpus
or Forge tests): `State` literals in `Witness/InterpreterExamples.lean`,
`.transient.isEmpty` in `Witness/Interface.lean` and `Witness/Checked.lean`, and
`state.storage.toList` one-entry matches in `tests/forge-harness/manifest.json`
(a one-entry HashMap's `toList` is `[(k, v)]`, so the exactness check is
preserved).

### Correctness / order audit (the #1 risk of this change)
Keys and values are normalized (`% 2^256`) at **insert** time, so two Nats equal
mod 2^256 collide as one key — exactly what `wordEq`-on-compare guaranteed — and
reads never re-`norm`. HashMap iteration order is nondeterministic, so I audited
every consumer of the three maps for order dependence:

- **storage / transient**: the only iterations are `wordMapToStorage` (folds into
  the key-addressed `EvmYul.Storage`; keys are unique after dedup, so fold order
  is irrelevant) and `storageToWordMap` (rebuilds from the key-addressed store).
  No `.toList`/fold of these maps feeds observable output directly. ✅
- **memory**: keyed by monotonic allocation id; only ever read/written by id
  (`Runtime.loadMemory?`/`allocMemory`/`storeMemory?`), never iterated. ✅
- **immutables**: read by name only (`State.immutable?`), never iterated. ✅
- **Context.accountBalances/accountCodehashes**: iterated by key in
  `snapshotOtherAccounts` — left as assoc lists (`WordMap`), so their order
  behavior is untouched. ✅

Conclusion: no observable result changes.

### Gates
- `lake build SolidCore` — green (1097 jobs), `AdoptionLaws` fully proven, no
  `sorry`/axioms.
- `scripts/smoke_replay.sh` (SOLC pinned to 0.8.35) — 28/28 `lean=ok`,
  `forge_interpreter_compare=pass`.
- Heavy case `openzeppelin-erc20` (`--jobs 1 --skip-forge --timeout 1800`):
  `lean=ok`, `forge_interpreter_compare=pass`.
  - **Before**: ~695 s wall / 437 s user.
  - **After**: 391 s wall / 383 s user.
  - The residual is dominated by fixed Lean elaboration/`#eval` compilation of the
    generated contract, not storage access.

### Follow-ups (not done — deliberately out of scope for this commit)
- **Cause #2**: `FunctionTable.lookup?`/`lookupById?` are O(F) `List.find?` scans
  (string compare / bignum `wordEq`) per internal call. Build name→fn and id→fn
  indexes once at construction. (Prototyped and green in a scratch pass:
  `FunctionTable` becomes a struct `{ entries, byName, byId }` built via a
  first-match `insertIfNew` fold; needs a `Coe (List InternalFunction)
  FunctionTable` for the hand-built witness tables and `[]`→`{}` at empty-table
  call sites in the witness files.)
- **Cause #3**: `Ty.storageValueFromWord?` re-`norm`s an already-canonical loaded
  word and recomputes `2^(8n)` per `fixedBytes` read. Since post-cause-#1 stored
  words are canonical, the redundant second `norm` can be dropped (masking
  semantics unchanged). Lower priority.
## 2026-07-07 — Exec-completeness TRIO (§B4): bare-literal casts, enum conversions, contract-typed locals

The §B4 audit flagged three constructs the typechecker accepts but the *checked
executable translation* (`Expr.toCore?` / `Expr.toCoreAs?` in
`SolidCore/Solidity/Interface.lean`) failed closed on. All three are
over-rejects (our semantics narrower than solc), not unsoundness. Each is now
executed and matches pinned-solc/Forge; corpus lanes pin the accepted behavior.

**1. Bare-literal casts** — e.g. `uint8(uint256(0x1234))`, `int8(uint8(200))`,
`uint8(int8(-1))`, `uint256(int256(-1))`.

- Where it failed: the int/uint fail-closed guard
  `if Ty.isIntOrUint ty && Expr.isNumberLiteralExpression expr then none`
  (three sites: `Expr.toCore?` general cast, `Expr.toCoreAs?`, and the
  typed-env `toCoreAs`-with-env branch). `Expr.isNumberLiteralExpression`
  treats a `Ty(...)` conversion operand as a literal, and `numberLiteralRat?`
  folds nested casts transparently (dropping truncation/sign), so a typed
  conversion whose folded value doesn't fit the target (`int8(-1)` folds to
  raw `-1`, doesn't fit `uint8`) was rejected — even though solc accepts it as
  a reinterpreting cast and constant-folds `uint8(int8(-1)) = 255`.
- Diagnosis: solc rejects an out-of-range *raw* literal cast (`uint8(300)` —
  operand is `int_const 300`) but accepts a cast whose operand is a *typed*
  conversion expression, applying runtime mod/sign semantics. The distinction
  is raw-literal vs typed-operand, not "is it constant".
- Fix: added `Expr.isRawNumberLiteralExpression` (numeric literal / negation /
  arithmetic of raw literals, but NOT a `Ty(...)` conversion) and switched the
  three int/uint guards to it. A typed-conversion operand now falls through to
  the runtime `uintCast`/`intCast`/cleanup path, whose primitives already match
  solc's mod-arithmetic and sign-extension. Raw out-of-range literals
  (`uint8(300)`) still fail closed (verified) and are still typecheck-rejected.
- solc-faithful behavior: `uint8(200)=200`, `uint8(uint256(0x1234))=52`,
  `int8(uint8(200))=-56`, `uint8(int8(-1))=255`, `int16(int8(-1))=-1`,
  `uint256(int256(-1))=2**256-1`.
- Pinning lane: `literal-cast-conversions` (invalid/OutOfRangeLiteralCast.sol
  pins the solc-reject).

**2. Enum conversions** — `MyEnum(x)`, `uint8(myEnumVal)`, including the
out-of-range Panic(0x21).

- Where it failed: an enum-typed *local* declaration (`Color c = Color(x)`).
  The initializer lowers (via `resolveEnums`) to `Expr.enumFromUInt maxValue x`
  with abi-type `uint8`, while the declared local type resolves to `Ty.enum`.
  `Expr.toCoreAs?`/`Expr.coreAsFromTy?` had no `Ty.enum` target case, so it hit
  the fallthrough `Ty.canImplicitlyConvert (uint 8) (enum _) = false → none`,
  failing the whole contract's core translation. (Inline `uint8(Color(x))`
  without a local already worked; free vs contract-nested enum was irrelevant
  once driven through a full `SourceUnit`, which collects free enums.)
- Fix: added a `Ty.enum _ => some coreExpr` target case to both
  `Expr.toCoreAs?` and `Expr.coreAsFromTy?`. Enums are represented as their
  ordinal word in core; the operand is an already-range-checked `enumFromUInt`
  (Panic 0x21 on out-of-range, `Interpreter.lean` `enumFromUIntValue`) or an
  enum of the same type, stored as-is.
- solc-faithful behavior: `Color(2)=2`, `Color(0)=0`, `uint8(Color.Blue)=2`;
  a runtime out-of-range value (`uint8 x = 3; Color(x)`) reverts Panic(0x21);
  the out-of-range *raw literal* `Color(3)` is a compile-time solc reject.
- Pinning lane: `enum-conversions` (invalid/OutOfRangeLiteralEnum.sol pins the
  solc-reject; the Forge test asserts the Panic(0x21) via `catch Panic`).

**3. Contract-typed locals** — `MyContract c = MyContract(addr)`.

- Turned out to be ALREADY closed at HEAD (6e3cdb4): driven through a full
  `SourceUnit` (so the referenced contract is in scope), a contract-typed local
  declares, round-trips, is accepted as an address argument, and its underlying
  address answers `.balance` — all matching solc (contract value = 160-bit
  address). No Interface/Interpreter change was needed. The earlier failure in
  the audit reproduced only when wrapping a bare `ContractDecl` (dropping the
  referenced contract). A pinning lane is added regardless.
- Pinning lane: `contract-typed-locals`.

Corpus additions are new lanes only (new src/*.sol + test/*.t.sol + manifest
entries); no frozen fixture, test, or expected value was modified. All three
lanes run Forge-paired green (solc_rejects=ok forge=ok lean=ok) against pinned
solc 0.8.35; expected values are ground-truth-checked by the Forge/EVM side.
## 2026-07-07 — boundary-completion arc: the two fn-value residues closed

The two FAIL-CLOSED residues the boundary-completion arc recorded (above) are
now Fixed. Both were internal-function-pointer VALUE gaps — not call gaps — and
both are pinned by the new differential lane `refs-residue-fn-values` (Forge
ground truth: `new RefsResidueFnValues(bool)`; member-form dispatches equal the
direct calls, ctor/modifier pointers call through the runtime dispatch ID).
solc accepts all pinned shapes (compiled `--via-ir`); expected values are from
Forge, never invented.

**Residue 1 — member-form fn-value uses (`Lib.f` / `Contract.f` as a VALUE).**
- Failed closed at TWO layers: typecheck rejected the value-position member
  (`TypeCheck.lean` `checkExpr`, the `Expr.member (Expr.typeName ty) member`
  arm: a library type name fails `checkTy` with `unknownType`; a contract type
  name reached the final `unsupported "member <m>"`), and — once typecheck was
  fixed — Interface elaboration rejected it (the value-position numbering /
  rewrite only recognized bare identifiers, so `Lib.f`/`Contract.f` stayed a
  member node and `toCore` failed with `unsupported checked contract …`).
- Fix, typecheck (`SolidCore/Solidity/TypeCheck.lean`): new
  `TypeContext.resolveInternalFunctionValueMember?` resolves a member of a
  library or (current/ancestor) contract to an internally-callable function
  signature; the `Expr.member (Expr.typeName ty) member` arm now tries it
  BEFORE `checkTy` (a library type name is not a value type) and, on success,
  yields the same `FunctionSig.internalFunctionValueTy?` a bare identifier
  would. LIBRARY members are accepted only when the function is declared
  `internal` (public/external library functions are delegatecall entry points —
  solc rejects converting them to a function type: "Special functions cannot be
  converted to function types"); CONTRACT members are gated on
  `isCurrentOrAncestorContract` (an unrelated `Other.f` stays a solc-reject:
  "Member f not found"). Also fixed `resolveInternalFunctionValueByNameLoop` to
  treat same-resolution-target duplicates as non-ambiguous (mirrors the external
  resolver / call-site `resolveLoop`) — this was what made a fn-value in a
  MODIFIER body report `ambiguousFunction` (the modifier-body env unions
  `functionSigsForModifierBodies` with the caller's own `functions`, doubling
  every name).
- Fix, elaboration (`SolidCore/Solidity/Interface.lean`): the value-position
  collector/rewriter (`Expr.collectInternalFnValueIdentsFuel` /
  `…rewriteInternalFnValueIdentsFuel`) now handle `Expr.member (Expr.typeName …)
  member`, keyed by `memberFnValueKeys` — the library-helper mangling
  `libraryHelperName Lib member` (a library helper is elaborated under
  `__library_<Lib>_<f>`, not its bare name) OR the plain member name (contract
  base); the numbering-candidate filter picks whichever actually names an
  elaborated function, so `Lib.f` stamps the library-helper table entry and
  `Contract.f` the contract function's — the same entry a direct call reaches.
  Member-form CALLEES (`Lib.f(..)`) are excluded from value collection (they are
  direct calls). `libraryHelperName` was hoisted above the collector (its only
  new use site) with the later duplicate removed.

**Residue 2 — fn-pointer VALUES created in constructor and modifier bodies.**
- The value-position numbering scanned only ordinary-function bodies, and the
  numbering-to-ID rewrite was applied only to ordinary function bodies — never
  the constructor body or (inlined) modifier bodies. A function used as a value
  ONLY in a ctor/modifier therefore got no dispatch ID and no table stamp, and
  the ctor/modifier body kept a bare fn identifier that failed to elaborate in
  fn-typed position.
- Fix (`SolidCore/Solidity/Interface.lean`): new
  `FunctionDecls.internalFnValueNumberingFull` scans ordinary bodies FIRST
  (identical IDs to before — ordinary-only lanes such as `internal-fn-pointers`
  are byte-for-byte unchanged), then appends modifier- and constructor-body
  value uses. BOTH elaboration entry points — `toCoreFromOrders?` (runtime
  dispatch table) and `constructorFunctionFromOrders?` (constructor) — compute
  this numbering with IDENTICAL arguments, so the ID the constructor writes into
  storage agrees with the table stamp a later pointer call dispatches on. The
  rewrite is now applied to modifier bodies in `FunctionDecl.toCore?` and to the
  constructor body + its modifier bodies in `constructorBodyForDeployment?`
  (threaded a new `internalFnIds` parameter).
- Verified end-to-end via deploy-then-call: `new RefsResidueFnValues(true)`
  → `viaCtorPointer(21)=42`, `(false)` → `viaCtorPointer(4)=12`;
  `viaModifierPointer(10)=11`.

Gates: `lake build SolidCore` green; smoke replay (curated + `internal-fn-
pointers`, `recursion-ref-signatures`, `calldata-ref-internal`,
`library-type-uses`, `base-constructor-runtime-args`, `frontend-frontier`) all
`lean=ok`, `status=0`, `compare=pass`; the new `refs-residue-fn-values` lane is
Forge-paired green (`forge=ok lean=ok`). No solc-reject fixture regressed;
internal-vs-external fn-value classification unchanged (external member fn
values `this.f`/`addr.f` never reach the new typeName-member path, and
`Value.externalFunction` is untouched). Corpus: 109 cases.

Known small limitations (recorded, not blocking; solc rejects or the shape is
absent from the corpus): overloaded library internal functions referenced by
member-form value (only the index-0 helper name is keyed); `C.f` for an
INHERITED (non-direct) function via member-form value (direct declarations of
the named contract only).

## 2026-07-08 — Acceptance soundness: signed/unsigned + contract-hierarchy conversion boundaries (A1–A4)

Four ACCEPTANCE-soundness over-accepts (this repo accepted programs pinned solc
0.8.35 rejects) fixed in `SolidCore/Solidity/TypeCheck.lean`. Each boundary was
read in solc `libsolidity/ast/Types.cpp` and confirmed with pinned-solc probes
of both the now-rejected case and a still-accepted neighbor. New pinning lane:
manifest case `signed-unsigned-contract-conversions` (5 `solc_rejects` fixtures
under `tests/forge-harness/signed-unsigned-contract-conversions/invalid/`, plus
8 Lean `TypeCheck.Examples` evals — a reject + an accepted neighbor per rule).

**A1 — implicit `uintN → intM` (and any signed↔unsigned) is rejected.**
- solc `IntegerType::isImplicitlyConvertibleTo` (Types.cpp:611-614): int→int
  implicit only when `isSigned() == convertTo.isSigned()` AND `convertTo.m_bits
  >= m_bits`. No implicit signed↔unsigned in either direction.
- Over-accept was `Ty.canImplicitlyConvert` arm `uint actualBits → int
  expectedBits => actualBits < expectedBits` (was ~:1060-1061). Deleted that arm.
- Boundary: `uint8 → int16` now REJECTED; `uint8 → uint16` and `int8 → int16`
  (same-sign widening) still accepted; explicit `int16(uint16(a))` still accepted.

**A2 — non-literal mixed-sign binary op (e.g. `uint8 + int16`) is rejected.**
- solc: no common type between a signed and unsigned integer for a binary op
  unless an operand is a number literal that fits the other's type.
- No separate edit needed: the mixed-sign binary path
  (`CheckedExpr.commonOperandTy?` → `Ty.commonImplicit?`, ~:3216-3264) has no
  direct mixed-sign arm and falls to the `canImplicitlyConvert` fallback, which
  A1 now makes false in both directions ⇒ `none` ⇒ rejected. The LITERAL cases
  are handled earlier in `commonArrayElementTy?` (:3270-3279) via
  `implicitLiteralFits` and are UNAFFECTED.
- Boundary: `uint8 a + int16 b` (both vars) REJECTED; `uint8(x) + 2` and
  `1 + int16(x)` (number literal takes the other operand's type) still accepted.

**A3 — explicit signed-int ↔ `bytesN` is rejected; unsigned same-width kept.**
- solc `FixedBytesType::isExplicitlyConvertibleTo` (Types.cpp:1364-1365):
  bytesN→integer only `!integerType->isSigned() && numBits == numBytes*8`;
  `IntegerType::isExplicitlyConvertibleTo` to FixedBytes (Types.cpp:638-639):
  only `!isSigned() && numBits == numBytes*8`. Unsigned, same bit width only.
- Over-accept was `Ty.fixedBytesIntegerSameSize` (~:1138-1141) using
  `integerBits?` (matches BOTH int and uint). Changed to `uintBits?` (unsigned
  only). This predicate feeds both directions of the explicit-conversion match.
- Boundary: `int256(bytes32)` and `bytes32(int256)` now REJECTED;
  `uint256(bytes32)` and `bytes32(uint256)` still accepted (bytesN sizes 1..32 ⇒
  bits are multiples of 8, so `uintBits?`'s `%8` guard never spuriously rejects).

**A4 — explicit contract down-cast (base→derived) is rejected; up-cast kept.**
- solc `ContractType::isExplicitlyConvertibleTo` (Types.cpp:1491-1500) → for a
  contract target falls through to `isImplicitlyConvertibleTo`
  (Types.cpp:1468-1489): allowed only when target is in the source's linearized
  bases (an UP-cast, derived→base). base→derived is a type error.
- Over-accept was the contract↔contract explicit arm (~:1426-1428) using the
  SYMMETRIC `contractsRelated` (ancestor either way). Changed to
  `contractHasAncestorPathFuel types 64 actualPath targetPath` (target must be a
  base/ancestor of source). `contractsRelated` is now unused (kept, harmless).
- Boundary: `Derived(baseInstance)` now REJECTED; `Base(derivedInstance)`
  up-cast and contract↔address conversions still accepted.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` all 28 cases
`lean=ok` / `compare=pass` (no valid corpus program newly rejected); new
`signed-unsigned-contract-conversions` lane `solc_rejects=ok lean=ok`.
## 2026-07-07 — sound/panics: enforce Panic(0x41) allocation bound and Panic(0x22) malformed-storage-bytes header

Two INFERRED missing-Panic gaps from `docs/solc-source-coverage-review.md` (S4,
S5). Each was probe-confirmed against pinned solc 0.8.35 / Foundry-EVM
(ground truth) AND the interpreter BEFORE any code change; both were genuine
divergences.

### S4 — Panic(0x41) oversized memory allocation (CONFIRMED, fixed)

Probe (`new bytes(n)` / `new uint256[](n)` via staticcall, panic payload
decoded): under Forge/EVM `n = type(uint256).max` and `n = 2**64` both revert
**Panic 0x41** for bytes and array; `n = 3` succeeds. Interpreter before the
fix: `Context.checkMemoryAllocation` consulted `memoryAllocationLimit?`, which
is `none` on the production path (only the witness tests set `some 3`), so it
returned `Except.ok` for ANY size — `new bytes(2**256-1)` would try to
materialize an unbounded `List.replicate`, never raising Panic(0x41).

solc trigger (exact): `YulUtilFunctions::arrayAllocationSizeFunction`
(`libsolidity/codegen/YulUtilFunctions.cpp:2370`) opens every memory array
allocation with `if gt(length, 0xffffffffffffffff) { <panic 0x41> }` — checked
on the raw element count, before scaling by the element stride, for both
byte arrays and value-element arrays.

Fix: `SolidCore/Solidity/Interpreter.lean` `Context.checkMemoryAllocation`
(~:1665) now raises `RevertData.memoryAllocationTooLarge` (Panic 0x41)
unconditionally when `size > 0xffffffffffffffff`, then falls through to the
existing optional `memoryAllocationLimit?` test hook. Threshold matches solc
exactly: `2**64-1` is accepted (as solc does; it OOGs later, out of scope),
`2**64` and above panic.

Reconciliation with `docs/bc-soundness-audit.md` §B7 "0x41 PARITY": B7's claim
was about the panic CODE being modeled (the `0x41` catalogue entry at
`Interpreter.lean` ~226-251 and the witness `memoryAllocationLimitedContext`
that fires it with an artificial `some 3` limit). That machinery was real, but
it was NEVER TRIGGERED on the production allocation path, because the real
solc `2**64-1` bound was not enforced there. B7 was code-parity, not
trigger-parity; S4 closes the trigger gap. No contradiction once the two senses
are separated.

Lane: `memory-allocation-overflow` (new) — Forge `MemoryAllocationOverflowForge
Test` pins Panic 0x41 for bytes/array at `max` and `2**64` and success at 3;
Lean drives the same solc-AST-imported contract via `ownCall` and checks
identical Panic(0x41)/return outcomes. Forge-paired green.

### S5 — Panic(0x22) malformed long-form storage byte array (CONFIRMED, fixed)

This CONTRADICTED nothing but was reachable only via a crafted/adopted storage
word (the model this repo already has for storage-dirty-words / reentrancy-
adoption). Probe (plant a slot word with `vm.store`, read via staticcall): a
`bytes`/`string` slot holding the long form (low bit set) with encoded length
16 (`word = 16*2+1 = 33`) reverts **Panic 0x22** on `.length`, the auto getter,
and a full read; encoded length 32 (`word = 65`) is well-formed and reads
length 32. Interpreter before the fix: `storageBytesHeader?` long branch
returned `Except.ok {length := 16, long := true}` — no panic.

solc trigger (exact): `YulUtilFunctions::extractByteArrayLengthFunction`
(`libsolidity/codegen/YulUtilFunctions.cpp:1359`) ends with
`if eq(outOfPlaceEncoding, lt(length, 32)) { <panic 0x22> }`. With the low bit
set (`outOfPlaceEncoding = 1`), an encoded `length < 32` is malformed and
panics with StorageEncodingError (0x22). (The short-form arm of the same
condition — `length >= 32` with low bit clear — was already handled by the
existing `length <= 31` guard in the even branch.)

Fix: `SolidCore/Solidity/Interpreter.lean` `storageBytesHeader?` (~:2851) long
branch now raises `RevertData.invalidStorageByteArray` (Panic 0x22) when the
decoded `length < 32`.

Lane: `storage-bytes-encoding` (new) — Forge `StorageBytesEncodingForgeTest`
plants word 33 with `vm.store` and pins Panic 0x22 on `dataLength()`, the
`data()`/`text()` getters, and `readData()` for both `bytes` and `string`, plus
valid length-32 read of word 65; Lean plants the same words with
`State.storeSlot` on the imported contract and checks identical outcomes.
Forge-paired green.

Gates: `lake build SolidCore` green; `smoke_replay.sh` compare=pass (incl.
`memory-allocation` and `storage-dirty-words` lean=ok); both new lanes
Forge-paired green. Corpus: 114 cases.
## 2026-07-08 — Value fidelity S1: regular string literals lower to UTF-8 bytes

solc stores a regular (non-`unicode`) string literal as its UTF-8 bytes
(`YulUtilFunctions`/`ASTBoogie` string handling; `unicode"..."` and `"..."`
share the same UTF-8 storage — the only difference is which source characters
are accepted). The repo lowered a regular `Literal.string` via
`text.toList.map Char.toNat`, i.e. per-code-point bytes, which is wrong for any
code point > 127. Example: `bytes("café")` — U+00E9 must become the two
UTF-8 bytes `0xC3 0xA9`, so `bytes(...).length == 5` and
`keccak256(bytes(...)) == keccak256(0x636166c3a9) ==
0x9513447e2d376aacd434727887590dd448cda8f2d30c4ace903d31fe209f8ad8`. The buggy
lowering gave `[99,97,102,233]` (length 4, wrong keccak). ASCII was unaffected,
which is why prior tests passed.

Fix (all in the string-literal lowering, `Char.toNat` → `stringUtf8Bytes` /
`text.toUTF8`): `Interface.lean` `Literal.toCoreExpr?` (`byteArray` path,
~:3494), `Literal.toFixedBytesWord?` (bytesN-target path, ~:2988), and
`ABI.lean` `stringBytes` (~:475, the `Error(string)` revert-reason encoder).
The `unicode"..."` path already used `stringUtf8Bytes`; `type(C).name` and
identifier byte arrays stay `Char.toNat` (ASCII identifiers only). Pinned by the
new `utf8-string-literal` lane (length/lead+cont byte/keccak/encodePacked,
Forge-paired-green).

## 2026-07-08 — Value fidelity S2: memory (not calldata) aggregate ABI params validate eagerly

The original S2 framing (calldata array/tuple elements validate eagerly) is
DISPROVEN by the frozen `abi-malformed` lane and a direct pinned-solc probe:
`f(uint8[] calldata a)` reading only `a.length` with a dirty element SUCCEEDS
(solc keeps the calldata reference and validates each element LAZILY on access —
`abiDecodingFunctionCalldataArrayValueType`). The genuine bug is the
`memory`-location counterpart: solc copies a memory reference-type parameter out
of calldata element-by-element through each element's `<validator>`
(`ABIFunctions::abiDecodingFunctionArray` → `abiDecodingFunctionValueType` →
`validatorFunction(_, true)` = `revert(0,0)`), so a dirty narrow-int element
reverts EMPTY at decode even if never read. Probe: `f(uint8[] memory a)` reading
only `a.length` with element `256` REVERTS; the `calldata` twin SUCCEEDS
(`YulUtilFunctions.cpp:4104` — `revert(0,0)`, not a Panic, for the decode
validator).

The repo validated all aggregate params lazily (wrapping elements in
`Value.abiLazy`), correct for calldata but wrong for memory. Fix
(`Interpreter.lean`): new `AbiCleanup.memoryEager` wrapper whose `accepts` is the
recursive element check and which `AbiCleanup.lazyParamValue` resolves through
its eager `accepts`-based fallthrough (returning `none` → empty revert at the
dispatch boundary). `Interface.lean` wraps `memory`-location function params
(~:16928) and constructor params (~:19505; constructor reference params are
always memory — solc forbids `calldata` there) in `memoryEager`; calldata
aggregates keep the lazy `dynamicArray`/`tuple` cleanups unchanged. Pinned by
the new `abi-memory-eager` lane (memory uint8[]/struct dirty-unused element
reverts empty; calldata twin succeeds returning 1 / 7). The frozen `abi-malformed`
calldata-lazy pins remain green.

## 2026-07-08 — Value fidelity S3: encodePacked conditional operand uses the ternary common type width

solc packs `abi.encodePacked(cond ? a : b)` using the conditional's COMMON
(mobile) type, not the then-branch's. The repo's `Expr.abiTy?` returned
`Expr.abiTy? thenExpr` for a ternary, so `cond ? uint8(0x11) : uint16(0x2233)`
packed 1 byte (then = uint8) instead of the common-type 2 bytes (uint16),
yielding `keccak256(0x11)` instead of the correct `keccak256(0x0011) ==
0xd5842eca58c06f1e59ec13dffa2151bec7fef478f0d491c263918c21fb38241e`
(else branch: `keccak256(0x2233) ==
0x0bea8c3dc955818b3f04b78631387a2a53f48726d725c56f6b3e3360c2011195`). Fix
(`Interface.lean` `Expr.abiTy?` ternary case, ~:4844): combine both branch
`abiTy?`s via the existing `Ty.commonImplicit?`, falling back to the then-type
when the else-branch type is not structurally inferable. `abiTy?` cannot resolve
local-variable branch types, so the pinning lane uses explicit casts
(`uint8(0x11)`/`uint16(0x2233)`) which `abiTy?` resolves. Pinned by the new
`packed-ternary-width` lane (both branches, Forge-paired-green).

## 2026-07-08 — Completeness boundaries C1-C5 (solc-source coverage review)

Closing the five completeness/fidelity gaps from `docs/solc-source-coverage-review.md`.
Each boundary confirmed against pinned solc 0.8.35 (accept vs reject / value) plus
a still-valid neighbor; pinned by the new `completeness-boundaries` lane
(solc-reject fixtures + `SolidCore.Solidity.TypeCheck.Examples` witnesses, all
`lake build SolidCore` regression-guarded).

- **C1 (`string.length`) — already correct.** The coverage doc read only the
  `Interface.lean` elaboration path; the acceptance gate is `Ty.hasLengthMember`
  (`TypeCheck.lean:4044`), which lists `bytes`/`bytesN`/`array` but NOT
  `Ty.string`, so `stringVar.length` was already rejected at typecheck (gate
  predates this effort, commit b17f0d2). solc: `ArrayType::nativeMembers` adds
  `length` only when `!isString()`. Probe: `s.length` on `string memory` →
  `Error: Member "length" not found`; neighbors `bytes(s).length` and
  `uint[].length` compile. No code change; added reject fixture
  `C1StringLength.sol` + witnesses `c1StringLengthRejected` /
  `c1LengthNeighborsAccepted`.

- **C2 (`type(C)` member set) — creationCode/runtimeCode already gated;
  interfaceId FIXED for abstract.** solc `Types.cpp:4271-4285`: deployable
  (concrete non-abstract) → `{creationCode, runtimeCode, name}`; non-deployable
  (interface OR abstract) → `{interfaceId, name}`. `TypeCheck.lean:5335-5348`
  already required `kind != interface && !abstract` for creationCode/runtimeCode
  (correct). But the `interfaceId` gate (`:5349`) required `kind == interface`
  only, OVER-REJECTING `type(AbstractContract).interfaceId`, which pinned solc
  ACCEPTS (probe: abstract contract `type(A).interfaceId` compiles). Fix:
  widened the gate to `kind == interface || abstract`
  (`TypeCheck.lean:5349-5357`). Concrete `type(D).interfaceId` still rejected
  (probe: `Error: Member "interfaceId" not found`). Added reject fixture
  `C2ConcreteInterfaceId.sol` + witnesses `c2ConcreteInterfaceIdRejected` /
  `c2NonDeployableInterfaceIdAccepted` (interface AND abstract accepted).

- **C3 (`abi.encodePacked` arrays-of-dynamic) — already correct.** The gate is
  `Ty.isAbiEncodePackedArrayElementShape` (`TypeCheck.lean:4172`), the
  array-ELEMENT shape predicate, which omits `bytes`/`string`/`array`, so
  `bytes[]`/`string[]`/`T[][]` elements were already rejected (the top-level
  `isAbiEncodePackedArgShape` still admits flat `bytes`/`string`/`uint[]`). solc:
  packed mode → `Error: Type not supported in packed mode` for a
  dynamically-sized element. Probe: `encodePacked(bytes[])` and
  `encodePacked(string[])` rejected; `encodePacked(uint[])` compiles. No code
  change; added reject fixtures `C3Packed{Bytes,String}Array.sol` + witnesses
  `c3PackedDynamicArraysRejected` / `c3PackedUintArrayAccepted`.

- **C4 (constant `%` with a negative operand) — FIXED (over-reject).**
  `NumberRat.mod?` (`Interface.lean:2788`) required `exactNat?` of both operands,
  rejecting any negative constant operand. solc folds signed `%` to the truncated
  remainder (sign of the dividend). Probe (pinned solc, all accepted):
  `(-7) % 3 == -1`, `7 % (-3) == 1`, `(-7) % (-3) == -1`. Fix: fold via
  `exactInt?` + `Int.tmod` (Lean `Int.tmod` matches Solidity truncated `%`
  exactly; the `%`/`emod` operator does NOT — `(-7).emod 3 = 2`). Neighbor:
  positive `7 % 3 == 1` still folds and is accepted. Witnesses
  `c4NegativeModFolds` / `c4NegativeModAcceptedInt256` / `c4PositiveModAccepted`.

- **C5 (`bytesN.length` static type `uint256` vs solc `uint8`) — SKIP,
  justified.** solc `FixedBytesType::nativeMembers` types `.length` as `uint8`
  (a compile-time constant = N); the repo tags it `uint 256`
  (`TypeCheck.lean:5425`). The doc found NO observable divergence (both
  ABI-encode to a 32-byte word; the emitted VALUE `Expr.word size` is already
  correct). Narrowing the static type `uint256 → uint8` can only make the
  typechecker REJECT MORE programs (e.g. common-type interactions), never fix a
  divergence — pure over-reject risk on a frozen, solc-validated corpus whose key
  gate is "no valid program newly rejected". Downside-only; skipped for fidelity's
  sake per the doc's own guidance.
## 2026-07-08 — Builtin blind-spot closure: sha256, ripemd160, blockhash, blobhash pinned

`docs/solidity-feature-coverage.md` flagged four builtins as SUPPORTED-UNTESTED
(elaborated in `Interface.lean`, exercised by ZERO corpus lanes): `sha256(bytes)`
(precompile 0x02), `ripemd160(bytes)` (0x03 → `bytes20`), `blockhash(uint)`
(BLOCKHASH), and `blobhash(uint)` (BLOBHASH, EIP-4844). Their result fidelity vs
the pinned solc 0.8.35 / Foundry-EVM had never been differentially checked.

Two new Forge-paired lanes now pin them; both `forge=ok lean=ok`,
`forge_interpreter_compare=pass`. NO interpreter change was needed — every value
matched the EVM on the first differential run.

- `hash-precompile-builtins` — `sha256Of`/`ripemd160Of`/`ripemd160Word` over
  four payloads (empty, `hex"010203"`, one 32-byte word, a 40-byte `>32`
  payload). Ground-truth digests were read from the precompile returns in a
  Foundry `-vvvv` trace, then asserted in `HashPrecompiles.t.sol`. The Lean lane
  imports the same solc AST and, under `responderOfResults` scripted with those
  SAME digests, drives the interpreter: because the open-world responder matches
  a precompile STATICCALL by (kind, target, calldata, value), a green lane proves
  the interpreter forms the precompile calldata as the raw payload (no length
  prefix) and decodes the 32-byte digest word identically. sha256 returns
  `bytes32` (natural); `ripemd160`'s `bytes20` is right-aligned numerically
  inside the interpreter (documented convention, Interpreter.lean ~L469), so the
  value-level witness compares the numeric digest via `ripemd160Word`, while the
  Forge side additionally pins the on-chain left-aligned `bytes20`/`bytes32`
  widening (`0x79f9…d57` → `0x79f9…d57000…000`).

- `block-env-builtins` — `blockHashOf`/`blobHashOf`. `vm.roll` fixes
  `block.number = 1000` so Foundry's blockhash of recent blocks is deterministic
  (verified stable across two runs). Pinned: current (1000)→0, recent
  (999)→`0xf022…3d10`, boundary `number-256` (744)→`0x7468…279c`, too-old
  `number-257` (743)→0, future (1001)→0; `blobhash(0)`/`blobhash(1)`→0 (non-blob
  tx). The Lean lane builds a context whose `blockHashes` map carries the two
  real hashes AND non-zero DECOYS at the three out-of-window slots (1000, 1001,
  743), so a green lane proves the interpreter's availability-window predicate
  (`requested < number && number - requested <= 256`) — not a mere map miss — is
  what forces 0. blobhash reads the empty `txEnv.blobHashes` under the default
  Cancun version → 0, matching EIP-4844's non-blob-tx behavior.

No soundness bug found: all four builtins already matched EVM ground truth.

## 2026-07-08 — G1: user-defined operators dispatch to their bound function, not the builtin

Fixes the wrong-VALUE soundness bug G1 (`docs/solidus-solc-deep-comparison.md`).
Since Solidity 0.8.19, `using {f as +} for T global;` (and unary `using {g as -}`)
binds an operator symbol to a free function; solc resolves `a + b` (a,b : T) to a
CALL of `f(a, b)` that runs with the operator function's OWN checked/unchecked
context. Solidus dropped solc's resolved operator reference on import
(`('BinaryOperation','function')`/`('UnaryOperation','function')` sat in
`ANALYSIS_SCALAR_FIELDS`) and lowered the node to a plain builtin `Expr.binary`/
`Expr.unary`, so the interpreter applied the BUILTIN op on the raw underlying
words. Whenever an operator body differs from the builtin the computed value was
wrong AND wrongly accepted; existing lanes passed only because their bodies equal
the builtin.

solc semantics confirmed against pinned solc 0.8.35 and its
`test/libsolidity/semanticTests/operators/userDefined/`:
- `fixed_point_udvt_with_operators.sol`: `applyInterest(500e18, 0.1e18) -> 550e18`
  (fixed-point `*` = `(a*b)/1e18`). Solidus BEFORE: the builtin int256 `*` (no
  /1e18 rescale) → `500e18 + 500e18*1e17 ≈ 5e37` (wrong). AFTER: `550e18`.
- `checked_operators.sol` / `unchecked_operators.sol`: the operator function runs
  with its own lexical context — a checked body panics 0x11 on overflow even when
  the call site is inside `unchecked {}`; an `unchecked{}` body wraps even from a
  checked call site.

Fix — importer only (the harness frontend that translates solc AST to
`SolidCore.Solidity` source AST); no trusted-Lean change was needed because a
user-defined operator application IS, semantically, an internal call, and the
existing internal-call boundary (`Stmt.internalCall`, `Interpreter.lean:8089`)
already (a) resolves free functions by name and (b) resets `checked := true` for
the callee body regardless of the caller's `unchecked` context:
- `scripts/solc_ast_to_lean_source.py`: new `collect_function_names_by_id`
  (id→name, populated in `render_module`, line ~2020) and
  `user_defined_operator_name` (line ~1832). In `expr_from_node`, a
  `BinaryOperation`/`UnaryOperation` whose solc `function` field is a non-null
  FunctionDefinition id is rendered as `Expr.call (Expr.ident <opFn>) [a, b]`
  (binary, line ~1203) / `[a]` (unary, line ~1100) instead of `Expr.binary`/
  `Expr.unary`. Elaboration + interpreter then run it as an ordinary internal
  call, inheriting correct value, per-body checked/unchecked context, comparison
  `bool` result types, unary/binary `-` disambiguation, and recursion.

New pinning lane `tests/forge-harness/udvt-operator-dispatch` (Forge-paired,
manifest case appended; corpus otherwise untouched): fixed-point mul (550e18),
unary/binary minus disambiguation, `bool` comparison operators, and the
checked/unchecked-context distinction at word width (`checkedOpOverflow(max)`
panics 0x11 from an `unchecked` call site; `uncheckedOpWraps(max) == 0` from a
checked call site). The lane deliberately avoids two ORTHOGONAL, pre-existing
Solidus gaps unrelated to operator dispatch (out of this agent's surface): (1)
signed `int / <numeric-literal>` division reverts typeMismatch — worked around
with a `int256 scale = 1e18;` local; (2) arithmetic on a narrow (`uintN`, N<256)
UDVT `unwrap` result is not width-checked (`Small.unwrap(a)+Small.unwrap(b)` does
not panic on uint8 overflow, though plain `uint8 a + b` does) — hence the
checked/unchecked demonstration uses `uint256`-underlying UDVTs, where word-width
overflow IS detected.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
compare=pass; new lane + existing UDVT-operator lane `frontend-frontier` both
`forge=ok lean=ok` (`forge_interpreter_compare=pass`). Not merged to main.
## 2026-07-08 — Acceptance boundaries G2–G16 (over-accept tightenings + probes)

Fixing the acceptance-boundary gaps `G2`–`G16` from
`docs/solidus-solc-deep-comparison.md`. Ground truth: pinned solc 0.8.35 (READ-ONLY
`/Users/dan/Projects/solidity-src`). Each fixed over-accept adds a solc-REJECT
fixture under `tests/forge-harness/acceptance-boundaries/invalid/` plus a
still-accepted neighbor, wired through the `acceptance-boundaries` manifest lane
(witnesses in `SolidCore/Witness/AcceptanceBoundaries.lean`). Smoke replay stays
all-green (28 cases, no valid corpus program newly rejected).

FIXED over-accepts (Solidus was accepting programs solc rejects):

- **G2 — `msg.value` in a non-payable function.** solc ViewPureChecker.cpp:270-294
  reports payable mutability for `msg.value` and errors 5887 unless the enclosing
  function is payable; internal/private and library functions are exempt
  (`isConstructor() || isPublic()` and `!libraryFunction()`). Added
  `currentVisibility` to `CheckEnv`, set from `fn.visibility`, and gated the
  `msg.value` member arm (`TypeCheck.lean`, `msg` member arm): reject when
  public/external/constructor, not in a library, and not payable. Pure was already
  rejected by `requireStateReadAllowed`. Probe: view/nonpayable/constructor →
  5887; payable and internal → ok. Boundary subtlety: the exemption for
  internal/private functions is load-bearing (the neighbor `g2InternalMsgValueFn`
  pins it). Modifier-body `msg.value` propagation (solc 4006) is NOT modeled — a
  narrower, more obscure over-accept, left documented.

- **G3 — `==`/`!=` on reference types.** solc TypeChecker.cpp:1694-1726 has no
  builtin equality for bytes/string/array/mapping/struct or UDVTs (TypeError 2271);
  value types, addresses, contracts, enums and function pointers compare. Added
  `Ty.isEqualityComparable` and required both operands comparable in the eq/ne arm.
  KEY subtlety found via smoke: enums flow as `Ty.user path` (not `Ty.enum`), so
  the `user` arm allows contract OR enum paths (via `isContractPath`/`isEnumPath`)
  and rejects UDVT paths — this exactly matches the probe (contract/enum/fnptr `==`
  accepted, UDVT `==` rejected). Initial contract-only version over-rejected
  `state() == State.Refunding` in `openzeppelin-refund-escrow`; the enum arm fixed
  it.

- **G4 — compile-time out-of-bounds constant index.** solc rejects `b[k]`/`a[k]`
  when `k` is a compile-time constant `>=` the `bytesN` width / fixed-array length
  (TypeError 1859/3383). The index arms now fold the index via
  `Executable.Expr.numberLiteralNat?` (folds `2+3`) and require `i < size`/`i <
  len`; dynamic arrays and non-constant indices are unaffected.

- **G5 — bare `return;` with a non-empty return list.** Probe corrected the
  writeup: solc rejects `return;` whenever the return list is non-empty, even when
  every return is named (TypeChecker.cpp:1138, TypeError 6777) — not only the
  unnamed case. `checkReturnExprs` now errors on `none, (_ :: _)` unconditionally.

- **G6 — `super.f()` to an abstract base.** solc TypeError 9582; a bodyless base
  declaration is not a valid super target. Added `hasBody` to `FunctionSig`
  (default `true`, set from `fn.body.isSome` in `FunctionDecl.signature?`) and
  filtered `superFunctions` to bodied sigs only. Regular dispatch (`functions`)
  keeps abstract sigs, so this touches only the super chain; the neighbor
  (`super.f()` to an implemented base) still resolves.

- **G7 — qualified `emit X.g()` on a non-event member.** solc TypeError 9292.
  `checkEventEmission` now resolves the member-call form `emit X.name(args)` by
  `name` against `env.events` (inherited events are flattened in), and rejects any
  other emit shape. Probe confirmed the paired risk is real — `emit A.E()` for a
  genuine (possibly inherited) event is legal — so the fix resolves rather than
  blanket-rejects; the neighbor pins both simple `emit E()` and member `emit C.E()`.

- **G9 — inline array literal of a mapping type.** solc rejects (a memory array of
  mappings is invalid, "only valid in storage"). The `Expr.array` arm rejects a
  mapping common-element type.

- **G10 — `msg.data` in `receive()`.** solc TypeError 7139. Added `inReceive` to
  `CheckEnv` (set for `FunctionKind.receive`) and reject `msg.data` when
  `inReceive`; `msg.data` in ordinary/fallback functions is unaffected.

PROBED and SKIPPED (real divergence confirmed, but out-of-scope / unreachable /
needs machinery with over-reject risk beyond the acceptance predicate):

- **G8 — `revert name(args)` shadowed by a callable. FIXED under R3 (2026-07-08
  residue cleanup, below).** A free error `E` masked by a contract-level
  non-error member `E` (function or state var) was an over-accept (Solidus
  resolved `revert E(...)` to the free error in `env.errors`, ignoring the
  shadow). Now rejected, matching solc (TypeError 1885).

- **G11 — `creationCode`/`runtimeCode` cycle. RE-EXAMINED under R3 — Solidus is
  already correct for the SELF cycle, no fix needed.** solc rejects `type(C).
  creationCode`/`runtimeCode` inside `C` (circular reference). Probed Solidus
  (hand-built AST): it REJECTS `type(C).creationCode` inside `C` (verdict matches
  solc — accept/reject aligns; the message differs) while ACCEPTING
  `type(Other).creationCode`. So there is NO over-accept for the single-contract
  self cycle. A CROSS-contract cycle (C↔D) needs a whole-program bytecode-
  dependency pass Solidus does not run, but such a program is solc-rejected and
  therefore never reaches the solc-AST importer — unreachable in the differential
  pipeline. Stays as an intentional whole-program OOS.

- **G12 — `_` as an identifier.** solc DeclarationError 3726 ("The name `_` is
  reserved"). Rejected by solc at name resolution *before* AST import, so it is
  unreachable through the solc-AST importer; the divergence can never be observed
  by Solidus in this pipeline. Skipped per the reachability guidance.

- **G16 — `try` on a library external call. RE-CONFIRMED under R3 — stays as a
  documented over-reject (execution-model bound).** solc ACCEPTS `try L.g()` for
  an `external` library function. Solidus over-rejects it. Accepting it at
  typecheck would admit a shape the interpreter cannot execute (external library
  calls are DELEGATECALL dispatch to a separately-deployed library, which
  Solidus's execution model does not implement) — a wrong-value/crash, strictly
  worse than an over-reject. No corpus program uses it (unreachable on the frozen
  corpus). Stays until external-library delegatecall execution is modeled.

DEFERRED over-rejects (G13–G15): these are *harmless* completeness over-rejects
(Solidus rejects programs solc accepts). Unlike G2–G10 (pure acceptance
predicates in `TypeCheck.lean`), each requires value-computing changes in
`Interface.lean` elaboration and the interpreter, matched exactly to Forge:
G13 nested-tuple-LHS destructuring, G14 storage-array copy with tail
zero-fill/truncation, G15 ternary-of-literals adopting the mobile common type
(observable as a *runtime* panic, not just acceptance). They were deliberately
NOT attempted in this pass to avoid introducing a wrong-value soundness bug
without full-replay validation (the coordinator's merge gate), which is a strictly
worse outcome than a harmless over-reject. Recorded here as the next work item.
## 2026-07-08 — TEST-COVERAGE gaps G17–G22 pinned (or recorded OOS)

Six features from `docs/solidus-solc-deep-comparison.md` were elaborated/handled
by the interpreter but had ZERO differential corpus lane. Each was closed by
adding a Forge-paired lane whose expected values come from ACTUAL pinned-solc
0.8.35 / Foundry-EVM runs (never invented), then confirming Solidus reproduces
them (`forge=ok lean=ok`, `compare=pass`). No interpreter/typechecker change was
required — every gap was a missing test, not a missing/wrong behavior. Corpus
frozen: only NEW lanes were added.

- **G17 `storage-uninit-fn-ptr`** — calling an internal function pointer held in
  a never-assigned STORAGE state variable (and one left unset on an untaken
  constructor branch) reads the zero dispatch value and panics `0x51`. This is
  the storage-default counterpart of the already-laned LOCAL-uninitialized
  pointer call (`internal-fn-pointers callUninitialized`). Forge ground truth:
  both `callStored`/`callCtor` revert with `Panic(0x51)`; Lean via
  `checkedOwnCallPanicMatches`.

- **G18 `try-external-fn-return`** — `try p.getCb() returns (function() external
  view returns (uint256) cb) { return cb(); }` binds an EXTERNAL FUNCTION-typed
  return value; the 24-byte pointer round-trips through the try binding and, when
  invoked, yields the callee's value (42). Forge exercises a concrete `Provider`
  (real EVM ABI encode/decode of the external fn pointer across the try
  boundary). Lean scripts a two-row responder: `getCb()` returns the
  ABI-encoded external fn pointer (`Ty.externalFunction` → `0xbeef.value()`),
  and invoking it returns 42. Confirms the try/catch external-fn return machinery
  (`Interpreter.lean:7174-7236`) is correct.

- **G19 `mutability-relax-override`** — overrides that RELAX (narrow) state
  mutability: base `view` overridden `pure`, base `nonpayable` overridden
  `view`. Pinned solc accepts both (warnings only) and virtual dispatch reaches
  the override bodies. Forge: `runTag(5)=7`, `runBump(5)=25`; Lean via
  `checkedCallWordMatches` (source-unit route, since inheritance base resolution
  needs the whole program). `importedContractAccepted` pins acceptance.

- **G20 `using-for-wildcard`** — `using WildcardLib for *` binds the library's
  functions to ALL receiver types by first parameter; member calls dispatch to
  the matching function across `uint256`/`int256`/`bytes memory`/`bool`
  receivers. Forge: `viaUint(21)=42`, `viaInt(-4)=-12`, `viaBytes(0xaabbcc,10)=13`,
  `viaBool(false)=true`. Lean uses the source-unit route (library binding
  resolution needs the program, like inheritance); the `int256` return is
  matched via an inline `CallResult.returned [Value.int _]` on `signedToWord`.

- **G21 `c99-scope-activation`** — C99 block-scope activation: a local is in
  scope only AFTER its declaration point, not hoisted to the top of its block.
  Two probes whose VALUES distinguish C99 from whole-block hoisting:
  `blockActivation()=1100` (inner `uint y = x` reads the OUTER `x=1`, not a
  hoisted inner `x=0`) and `selfInitFromOuter()=6` (inner `uint x = x + 1`
  initializer reads the OUTER `x=5`). Forge confirms (warnings only); Lean via
  `checkedOwnCallWordMatches`.

- **G22 create2 address prediction — recorded OUT-OF-SCOPE, no lane added.**
  Predicting the deployed `create2` address
  `keccak256(0xff‖deployer‖salt‖keccak256(initCode))` requires the REAL compiled
  creation bytecode as `initCode`. Solidus deliberately models `initCode` as a
  source-canonical name encoding (`creationInitCode`, `Interpreter.lean:2336`:
  32-byte name length ‖ name ‖ ctor args), a recorded gas-like deferred
  limitation (see the earlier "initCode is not compiled bytecode" decision). The
  create2 address in Solidus comes from the fixture oracle/responder, not from
  keccak over real bytecode, so it CANNOT reproduce solc's deployed address.
  Forcing a lane would either assert a non-solc address (forbidden) or require
  modeling compiled initCode (out of scope per the create-initCode decision).
  This is a deliberate OOS non-gap, not an untested-but-modeled path.

No soundness bug found: all five pinned features already matched EVM ground
truth; G22 is a documented out-of-scope limitation.

## 2026-07-08 — G15: ternary-of-literals adopts the mobile common type (over-reject fixed)

**solc semantics (confirmed).** `TypeChecker::visit(Conditional)`
(`libsolidity/analysis/TypeChecker.cpp:1356-1418`) sets a conditional's type to
`Type::commonType(trueExpr->mobileType(), falseExpr->mobileType())`. For two
untyped number literals the `mobileType()` of each is the smallest integer type
that holds it, so `(t ? 63 : 255)` is `uint8` (both mobiles `uint8`, common
`uint8`), `(t ? 300 : 400)` is `uint16`, and a mixed-sign case like
`t ? 1 : 2` typed `uint8` is (correctly) NOT implicitly convertible to `int8`
(solc rejects `int8 r = t ? 1 : 2` — verified with the pin). The concrete type
means the enclosing arithmetic runs at that width: `(t ? 63 : 255) + 1` adds in
`uint8`, so `255 + 1` panics 0x11 in checked mode.

**Wrong → right.** Solidus typed every number literal `uint256`
(`TypeCheck.lean literalTy?`), and `abiTy?`/the typechecker's `Conditional` arm
combined the branch types to `uint256`; the ternary was never recognized as an
untyped-literal shape (`exprIsUntypedNumberLiteralExpression` excludes
`ternary`). So `uint8 a = t ? 63 : 255;` was OVER-REJECTED (`uint256` not
convertible to `uint8`), and `(t ? 63 : 255)` fed to narrow arithmetic mis-typed
to `uint256`. No wrong value was ever emitted — it rejected at typecheck/elab.

**Fix (mobile common type, no new literal-narrowing path).**
- `Interface.lean` (`Executable`): new `smallestUintBits?`/`smallestIntBits?`
  and `Expr.untypedLiteralMobileTy?` — the mobile type of an untyped
  number-literal expression, recursing into a `ternary` via `Ty.commonImplicit?`
  on the branch mobiles (returns `none` for any non-untyped-integer-literal
  shape, so all other exprs keep existing behavior).
- `Interface.lean Expr.abiTy?` ternary arm: return the mobile common type when
  both branches are untyped literals (else the prior `commonImplicit`-of-branch
  fallback, which S3's `packed-ternary-width` relies on). `abiTyWithEnv?` picks
  this up through its `abiTy?` fast path, so `commonOperandTyWithEnv?` sees
  `uint8` and arithmetic elaborates at the ternary width.
- `TypeCheck.lean` `Conditional` arm: `resultTy` is the mobile common type when
  applicable (else the prior implicit-convertibility pick). Deliberately NOT
  marked `requiresExactLiteralFit`: the concrete type flows through the normal
  implicit-conversion path (`uint8 → uint16/uint256` widening OK), matching solc.

**Right value (Forge-verified).** Lane `ternary-literal-mobile-type`:
`narrowAssign(true/false) = 63/255` (was over-rejected), `widenAssign = 63/255`
(uint8→uint256 widen), `widthPanic(true) = 64` and `widthPanic(false)` PANIC
0x11 (uint8 `255+1` overflow — width observable), `uint16Common(true/false) =
300/400`. Forge `TernaryLiteralMobileTypeForgeTest` and the Lean
`checkedOwnCall{Word,Panic}Matches` witnesses agree; `forge=ok lean=ok
compare=pass`.

**Note for the arithmetic-width sibling.** The `widthPanic` observable keeps the
operand width equal to the assignment target (`uint8 r = (…)+1`), so it fires
through the existing narrow-cleanup path. A ternary result WIDENED before its
overflow is observed (`uint16 r = (t?63:255)+1`) did not panic — that was the
pre-existing narrow-arithmetic-widened gap (`uint8+uint8` assigned to `uint16`
yielded 256), in the binary-operand-width machinery. **Now FIXED under the
residue cleanup (2026-07-08, "narrow-arithmetic-widened gap" entry below).**
`untypedLiteralMobileTy?` and `smallest{Uint,Int}Bits?` are shared `Executable`
helpers for literal mobile types.

## 2026-07-08 — G13: nested tuple LHS `((a, b), c) = …` (over-reject fixed)

**solc semantics (confirmed).** solc accepts a nested tuple on the assignment
LHS (`syntaxTests/tupleAssignments/tuple_in_tuple_short.sol`, empty
expectations; verified `((a, b), c) = ((x, x+1), x+2)`, `(a, (b, c)) = …`, and a
nested hole compile with the pin). The RHS tuple is evaluated once,
left-to-right, into temps, then the values are assigned into the (nested)
targets in lockstep with the LHS structure; a hole still evaluates its RHS
component and discards it.

**Wrong → right.** The core `Stmt.assignTuple` LHS was a FLAT
`List (Option LValue)`; elaboration (`TupleItems.toCoreLValueTargets?`) and the
typechecker (`checkTupleAssignmentTargets`) had no recursion into a nested tuple
target, so any `((a, b), c) = …` failed to elaborate / type-check and was
OVER-REJECTED. No wrong value — rejected up front.

**Fix (new nested target, flat path unchanged).**
- `Interpreter.lean`: new `inductive TupleTarget = hole | leaf LValue | nested
  (List TupleTarget)` and `Stmt.assignTupleNested : List TupleTarget -> Expr ->
  Stmt`; a `TupleTargets.writeNested`/`TupleTarget.writeNested` mutual recurses
  a `Value.tuple` against the target tree, left-to-right; the `assignTupleNested`
  interpreter arm evaluates the RHS ONCE to a (possibly nested) `Value.tuple`
  then writes — so `((a,b),c)=((b,c),a)` swaps and holes are pre-evaluated,
  matching solc's temps-then-stores order. The flat `assignTuple` path is
  untouched and still used for non-nested LHSs.
- `Interface.lean`: `TupleItems.hasNestedTuple` gates `tupleAssignmentCore?`;
  when nested, `TupleItem.toCoreTupleTarget?`/`TupleItems.toCoreTupleTargets?`
  build the `TupleTarget` tree and emit `assignTupleNested`; otherwise the
  existing flat elaboration runs.
- `TypeCheck.lean`: the tuple-LHS `Assignment` arm dispatches to
  `checkNestedTupleItems` when `hasNestedTuple`. It walks LHS items against the
  RHS tuple expression in lockstep — recursing on a nested sub-tuple, and for a
  leaf reproducing the flat path's lvalue / writable-location / state-write /
  assignability / mapping-copy / calldata-location checks inline (on syntactic
  subterms, keeping termination structural: measure `sizeOf lhsItems + sizeOf
  rhs`). A hole still type-checks (evaluates) its RHS component.

**Right value (Forge-verified).** Lane `nested-tuple-assignment`:
`nestedLit(3) = 345` (a,b,c = 3,4,5), `nestedRight(3) = 345`, `nestedSwap(3) =
453` (RHS `((b,c),a)` read first → a,b,c = 4,5,3), `nestedHole(3) = 35` (middle
hole discards x+1). Forge `NestedTupleAssignmentForgeTest` and the Lean
`checkedOwnCallWordMatches` witnesses agree; `forge=ok lean=ok compare=pass`.

**Scope note.** A nested-position RHS *internal function call* (`((a,b),c) =
(foo(), bar())` where `foo` returns a 2-tuple) needs the internal-call
tuple-hoisting machinery to run inside the nested elaboration; the lane pins the
expression-RHS forms (literals/params/reads, incl. the swap and hole), which is
where the destructure/order/hole semantics live. Call-in-nested-position was
left as a remaining over-reject here — **now FIXED under R1 (2026-07-08 residue
cleanup, below).**

## 2026-07-08 — G14: storage-array copy with wider/shorter source (over-reject narrowed)

**solc semantics (confirmed).** `ArrayType::isImplicitlyConvertibleTo`
(`libsolidity/ast/Types.cpp:1628-1665`): a copy INTO a non-pointer storage array
is accepted when the base type is implicitly convertible; a DYNAMIC dest accepts
any source length; a FIXED dest `T[N]` requires a fixed source `S[M]` with
`N ≥ M`. The runtime (`YulUtilFunctions` copyArrayToStorage/clearStorageRange)
resizes the dest to the source length, copies elements with per-element
conversion, and zero-fills a longer old tail. Forge ground truth (pin):
`uint16[] = uint8[]` → `[255, 7]`; `uint256[] = uint8[]` (len 3) → `[1,2,3]`;
a dynamic dest shrunk from length 5 to 2 then regrown reads the old slots back
as `0`.

**Wrong → right.** `Ty.canImplicitlyConvert` has no array arm (`_,_ => false`),
so every non-identically-typed array copy was OVER-REJECTED at typecheck.

**Fix (SAFE subset only — verified values, no wrong-value risk).**
`TypeCheck.lean`: new `Ty.storageArrayCopyAssignable?`, consulted in the
`AssignOp.assign` arm ONLY for a genuine storage-variable destination
(`stateLValue && !rebindsStoragePointer`); when it holds, the strict
`expectAssignableToIn` is skipped. It accepts exactly the family whose copied
VALUES the interpreter already reproduces bit-for-bit (the dynamic-dest
deep-clear write resizes and zero-fills; unsigned magnitudes always fit the
wider dest): a DYNAMIC unsigned-integer dest with an unsigned-integer source of
≤ width (`uintM[] = uintN[]`, `N ≤ M`). No interpreter/elaboration change was
needed for this subset.

**Initially NOT accepted (deferred; now FIXED under R2, 2026-07-08 residue
cleanup, below).** The other solc-accepted shapes were left out of the first
`storageArrayCopyAssignable?`:
  * SIGNED element widening (`int8[] → int16[]`);
  * FIXED-length dest `T[N] = S[M]`, `N > M`.
Both are now accepted with Forge-verified values — see the R2 entry.

**Right value (Forge-verified).** Lane `storage-array-copy-convert`:
`widenU8toU16 = (255, 7, len 2)`, `widenU8toU256 = (1, 2, 3, len 3)`,
`shorterClearsTail = (len 2, [2]=0, [4]=0)`. Forge
`StorageArrayCopyConvertForgeTest` and the Lean raw `ownCall` witnesses agree;
`forge=ok lean=ok compare=pass`.
## 2026-07-08 — H1: a negated numeric literal adopts a signed operand's type (gap/arithwidth)

COMPLETENESS gap recorded incidentally in the G1 note (2026-07-08 UDVT-operator
entry). Ground truth: pinned solc 0.8.35 + Forge. Not merged to main.

solc (`Types.cpp` common-type / literal fitting) lets a numeric literal —
including `-2`, `-1e18` — take the other operand's type in a binary arithmetic op
if it fits. Probe: pinned solc ACCEPTS `a / 1e18`, `a / -2`, `a * 3`, `a + 5`,
`a - 5`, `a % 7` for `int256 a`, and Forge confirms signed division truncates
toward zero (`7 / -2 == -3`, `-7 / -2 == 3`), `-8 % 7 == -1`, and
`type(int256).min / -1` Panics 0x11. Scope on our side: a *positive* direct
literal already worked (`a / 1e18` → `intWord`); only a *negated* literal was
broken — and for ALL arithmetic operators, not just `/`. Cause:
`Expr.commonOperandTyWithEnv?` (Interface.lean) used `Expr.isDirectLiteral`,
which matches only `Expr.literal _`, so a negated literal `-2` (whose
`abiTyWithEnv?` reports the *magnitude* type `uint256`) failed
`commonImplicit? int256 uint256`, dropping the op onto the untyped `toCore?`
fallback where `-2` lowered to `-(word 2)` and checked unary `-` on an unsigned
word spuriously Panicked 0x11. Fix: `Expr.adoptsOperandLiteralTy` (Interface.lean)
also accepts a negated raw numeric literal; the `implicitLiteralFits` guard still
rejects out-of-range / wrong-signed literals (e.g. `-2` against a `uintN`
operand), so nothing is accepted beyond solc. The typechecker already types `-2`
as `int256` (its `UnaryOp.neg` case), so this only aligns lowering with the
accepted type. Lane: `signed-literal-arithmetic` (positive+negative literal
divide, INT_MIN/-1 panic neighbor, and `*`/`+`/`-`/`%` neighbors).

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass` (no regression); lane `forge=ok lean=ok`.

## 2026-07-08 — H2: narrow `uintN`/`intN` cast of a checked arithmetic argument (gap/arithwidth)

SOUNDNESS gap (adds a missing Panic 0x11) recorded incidentally in the G1 note
(2026-07-08 UDVT-operator entry). Ground truth: pinned solc 0.8.35 + Forge. Not
merged to main.

Symptom (broader than the UDVT framing in the note): pinned solc/Forge Panic
0x11 for `uint8(a + b)` and `int8(a + b)` on narrow overflow, but Solidus wrapped
(`uint8(200 + 100) == 44`). Because a UDVT `Small.wrap(x)` lowers to `uint8(x)`,
the same defect made a `using`-bound `+` operator whose body is
`Small.wrap(Small.unwrap(a) + Small.unwrap(b))` (the G1 note's exact case) drop
the uint8 overflow Panic. NOTE — the note's plainer probe
`Small.unwrap(a) + Small.unwrap(b)` *as a bare return / statement* was ALREADY
sound here (it lowers via the type-directed `binaryToCoreWithEnvTyped?` →
`uintCleanup 8`); the surviving bug was specifically arithmetic **wrapped in a
narrow int/uint cast**. Cause: a conversion-typed return fell to the env-less
`Stmt.toCore?` cast path (`uintCast N (toCore? arg)`), which lowered the inner
`a + b` with plain 256-bit operands and no result cleanup, then truncated —
silently wrapping.

Fix, two parts in Interface.lean: (1) a narrow-int/uint cast-of-arithmetic case
in `Expr.toCoreAsWithEnv?` (helpers `Ty.narrowIntCastTarget?`,
`BinaryOp.isOverflowArithmetic`, `Expr.peelToOverflowArithmetic?` — the last
peels the redundant same-type cast `annotateAbi` re-wraps around the argument):
it lowers the arithmetic via `binaryToCoreWithEnvTyped?` at the operands' own
width, wraps the result in the checked `Ty.implicitCleanupCore srcTy` (this is
the Panic 0x11 the cast path dropped), then applies the truncating outer cast;
(2) route a conversion-typed `return` through `returnValuesCoreWithReturnTys?`
instead of env-less `Stmt.toCore?`, with the env-less shape kept as the fallback
so no previously-accepted return regresses. Peeling only strips casts wrapping
the *whole* expression, so an explicitly-widened `uint8(uint256(a) + uint256(b))`
keeps its 256-bit (non-panicking) semantics; `unchecked{}` still wraps
(`uintCleanup` honors the checked flag → `uint8(200 + 100) == 44` in an
`unchecked` block); a 256-bit UDVT is unaffected (`Big.unwrap(a)+Big.unwrap(b)`
checks at 256). Verified vs Forge: `addU8(200,100)`, `addI8(100,100)`,
`subI8(-100,100)`, `addU8Operator(200,100)` all Panic 0x11; `addU8(100,55)==155`,
`addI8(-100,50)==-50`, `addU8Unchecked(200,100)==44`, `addBig(5,6)==11`.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass` (no regression — H2 must not start panicking a
currently-passing case, verified); lane `narrow-udvt-arithmetic` `forge=ok
lean=ok`. Full replay is the coordinator's merge gate — not run here.

## 2026-07-08 — R1 (residue cleanup): nested tuple LHS with an INTERNAL-CALL RHS (over-reject fixed)

The G13 scope note left one shape as an over-reject: a NESTED tuple assignment
LHS whose RHS contains internal function calls — `((a, b), c) = (foo(), bar())`
where `foo` returns a 2-tuple (its result destructures into the nested target),
and `((a, b), c) = ((g(), h()), k())` with scalar calls in nested RHS positions.
The maintainer's residue-cleanup pass requires it fixed.

**solc semantics (confirmed with the pin).** Both shapes compile (`solc --bin`).
solc evaluates the RHS tuple components once, LEFT-to-right, each into its own
temp (a multi-return call producing the temps for a nested target), then
destructures against the nested target tree; a hole still evaluates its RHS
component. Forge ground truth (`NestedTupleInternalCallForgeTest`, storage
`order` log packed into the return): `flatMulti() == 10203012` (a,b,c = 10,20,30;
foo before bar → order 12), `nestedCalls() == 102030345` (100,200,300; g,h,k →
order 345), `nestedHole() == 4099967` (a=400 from `p()`, hole discards `q()` but
`q()` still runs → order 67, c=999).

**Wrong → right.** The G13 nested elaboration (`tupleAssignmentCore?`) lowered
the whole RHS with `Expr.toCore?`, which cannot hoist internal calls out of a
tuple, so any nested-LHS assignment with a call RHS failed to elaborate and was
OVER-REJECTED (and the typechecker rejected a nested target whose RHS component
was not itself a tuple literal). No wrong value — rejected up front.

**Fix.**
- `Interface.lean`: `FunctionDecl.nestedTupleRhsHoistItem?` /
  `nestedTupleRhsHoistList?` (in the internal-call mutual block) hoist every RHS
  leaf into a path-unique temp left-to-right (so evaluation order — and thus
  side-effect order — matches solc's temps-then-stores), returning
  (prefix statements, the temp-read expression replacing the component). A
  direct MULTI-return internal call filling a nested target is captured (reusing
  `internalCallParts?` + `captureReturn`) into per-return outer temps and
  replaced by an `Expr.tuple` of their reads; a parenthesized sub-tuple recurses;
  an ordinary leaf (single-return call, pure read) is hoisted like the flat
  `tupleItemsUseCoreWithInternalCalls?`. The `Stmt.toCoreWithInternalCalls?`
  tuple-assignment arm now dispatches to this (building nested targets via
  `TupleItems.toCoreTupleTargets?` and one `Stmt.assignTupleNested`) when the LHS
  `hasNestedTuple` and the flat `Stmt.toCore?` path rejected it. Helper
  `FunctionDecl.internalCalleeReturnTys?` sizes the per-return temps.
- `TypeCheck.lean`: `checkNestedTupleItems` gains a case for a nested LHS target
  aligned with a NON-tuple-literal RHS component whose TYPE is a tuple (a
  multi-return call), checked via the new `checkNestedTupleTargetsAgainstTys`
  (leaf lvalue / writable / state-write / assignability discipline, recursing on
  nested targets); the tuple-literal RHS subcase (scalar calls in nested
  position) already type-checked.

**Right value (Forge-verified).** Lane `nested-tuple-internal-call`:
`flatMulti = 10203012`, `nestedCalls = 102030345`, `nestedHole = 4099967` — Lean
`checkedOwnCallWordMatches` witnesses reproduce all three exactly, including the
left-to-right side-effect order. `forge=ok lean=ok compare=pass`.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass` (no regression); new lane `forge=ok lean=ok`.

## 2026-07-08 — R2 (residue cleanup): storage-array copy — signed widening + fixed-length dest (over-reject fixed)

G14 deferred two storage-array-copy shapes as over-rejects. The maintainer's
residue-cleanup pass requires them fixed. Both now compute Forge-exact values.

**solc semantics (re-confirmed by probing the pin).** `ArrayType::
isImplicitlyConvertibleTo` (`Types.cpp:1628-1665`): base implicitly convertible;
a DYNAMIC dest accepts any source length (dynamic OR fixed source); a FIXED dest
`T[N]` requires a FIXED source `S[M]` with `N ≥ M`. Probed accept/reject matrix
(pin): dyn←fixed ACCEPT, fixed N<M REJECT, fixed N≥M ACCEPT, signed↔unsigned
base REJECT, base narrowing REJECT, fixed←dyn REJECT. The runtime resizes/pads
the dest, sign/zero-extends each element to the dest width (a widening never
overflows → never Panic 0x11), and zero-fills the tail. Forge ground truth
(`StorageArrayCopySignedFixedForgeTest`): `int8[]→int16[]` `[-5,127]`;
`int8[3]→int16[5]` `[-1,100,-128,0,0]`; `uint8[2]→uint16[4]` `[200,255,0,0]`.

**Fix.**
- `TypeCheck.lean`: `Ty.storageArrayCopyAssignable?` rewritten to solc's rule —
  dynamic dest ← any source length, fixed dest N≥M — with an INTEGER base
  restriction (`Ty.integerArrayElemWiden?` = both integers and
  `canImplicitlyConvert`, which already encodes same-signedness widening, so it
  forbids signed↔unsigned and narrowing exactly as solc). Restricting to integer
  bases keeps every accepted shape one whose copied values are Forge-verified.
  Verified accept/reject matrix (9 cases) matches solc bit-for-bit; the
  pointer-dest exclusion stays via the existing `stateLValue &&
  !rebindsStoragePointer` call-site gate.
- `Interpreter.lean`: (a) `loadStorageField` now materialises a whole
  fixed-storage-array READ (was `typeMismatch`) via `loadStorageLayoutAt` — the
  RHS of a fixed-array copy; (b) `Value.padFixedArrayTo` pads a shorter source
  fixed-array to the dest length with the element default (`defaultLike`),
  applied at the non-mutual store entry (`storeStorageField`) and in the
  deep-clear fixed-array arm, so the value handed to the structural-recursive
  `storeStorageLayoutAt` already has the exact length (padding elements inside
  the mutual store would break structural recursion — verified). Signed element
  widening needed NO copy change: the packed storage read (`intCast?` on the
  masked field) already sign-extends, and the write (`coerceStorageWordAs` at the
  normalized `int256` ty) packs the low bits correctly.
- `Interface.lean` (`Expr.toCore?`): a bare negated numeric literal `-5`/`-1e18`
  now folds to a signed constant (`Expr.intWord (signedToWord (-n))`) instead of
  the env-less `-(word 5)`, which Panicked 0x11 under a checked unary `-` on an
  unsigned operand. This surfaced only when POPULATING a signed dynamic array via
  `signedArray.push(-5)` (index-writes and casts already worked); the fold makes
  a bare `int_const` correct in every env-less position (the H1 type-directed
  arithmetic paths are unaffected). A newly-added Witness helper
  `checkedOwnCallIntQuintMatches` matches the 5-int fixed-dest return.

**Right value (Forge-verified).** Lane `storage-array-copy-signed-fixed`:
`signedWiden = (-5, 127, len 2)`, `fixedDestSigned = (-1, 100, -128, 0, 0)`,
`fixedDestUnsigned = (200, 255, 0, 0)`. `forge=ok lean=ok compare=pass`. The
prior `storage-array-copy-convert` (G14 unsigned/dynamic) lane still passes.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass` (no regression); new lane `forge=ok lean=ok`.

## 2026-07-08 — R3 (residue cleanup): re-examined G8, G11, G12, G16

The acceptance agent probed-and-skipped G8/G11 and flagged G12/G16 as likely
non-issues. R3 re-examined each by probing pinned solc 0.8.35 and, where the
solc-AST importer cannot reach the case (solc rejects it, so no AST is emitted),
by hand-building the AST and calling `SourceUnit.check` directly (the technique
the G2–G10 acceptance-boundary witnesses use).

**G8 — free error shadowed by a contract member: FIXED (over-accept).** solc
resolves `revert E(args)` to `E`'s innermost declaration and rejects a revert of
a non-error: a free `error E` masked by a contract `function E` → TypeError
"Expression has to be an error."; masked by a contract `uint E` → "This
expression is not callable." Probed Solidus (hand-built AST): it OVER-ACCEPTED
both (it resolved `E` against `env.errors`, which merges free + contract errors,
ignoring that a contract member shadows the free error). Fix (`TypeCheck.lean`):
a new `CheckEnv.contractNonErrorMemberNames` — the current contract's own +
inherited NON-error member names (built from `visibleFunctionSigs`, NOT the
`functions` field that also carries free functions, plus state vars / modifiers
/ contract events) — and a guard at the top of `checkCustomErrorArgs` rejecting
`revert E(...)` when `E` is a local variable or a contract-level non-error
member. A genuine contract `error E` is not in that set (and never coexists with
a same-name contract member), and free functions are excluded, so the valid
neighbors still revert: probed `revert E()` for a contract error → accepted, for
an unshadowed free error → accepted; the two shadow shapes → rejected. Pinned by
the `acceptance-boundaries` lane (witnesses `g8ErrorShadowRejected` /
`g8ErrorNeighborsAccepted`; solc-reject fixtures `G8ErrorShadowedByFunction.sol`,
`G8ErrorShadowedByStateVar.sol`). solc-validated corpus never contains these
(solc rejects them), so this is a defense-in-depth typechecker tightening; smoke
28/28 confirms no valid revert regressed.

**G11 — `type(C).creationCode`/`runtimeCode` cycle: already correct, no fix.**
Probed Solidus (hand-built AST): `type(C).creationCode` inside `C` is REJECTED,
`type(Other).creationCode` ACCEPTED — the accept/reject verdict matches solc for
the single-contract self cycle, so there is NO over-accept. A cross-contract
cycle (C↔D) needs a whole-program bytecode-dependency pass Solidus does not run,
but such a program is solc-rejected and never reaches the solc-AST importer —
unreachable in the differential pipeline. Documented as intentional whole-program
OOS.

**G12 — `_` reserved: confirmed non-issue.** solc rejects `_` as an identifier
at name resolution, BEFORE emitting an AST, so the divergence is unobservable
through the solc-AST importer (Solidus only ever receives programs solc already
accepted). Unreachable in this pipeline.

**G16 — `try` on a library external call: confirmed over-reject, stays.** solc
ACCEPTS `try L.g()` for an `external` library function; Solidus over-rejects it.
This is an over-REJECT (completeness), not an over-accept. Accepting it would
admit a shape the interpreter cannot execute — external library functions are
DELEGATECALL dispatch to a separately-deployed library, which Solidus's execution
model does not implement — so acceptance would be a wrong-value/crash, strictly
worse than an over-reject. No corpus program uses it. Stays until external-library
delegatecall execution is modeled (recorded here so it is not lost).

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass`; the `acceptance-boundaries` lane (now G2–G10 +
G8) `solc_rejects=ok lean=ok`.

## 2026-07-08 — Sweep: narrow-arithmetic-widened gap (soundness / missing Panic 0x11 fixed)

Sweeping `DECISIONS.md` for residual gaps beyond R1/R2/R3 (per the residue-cleanup
brief) surfaced the narrow-arithmetic-widened gap the G15 note recorded and
deferred to "the binary-operand-width machinery": a narrow integer arithmetic op
whose result is assigned / returned / passed at a WIDER type was computed at the
wider width and did not Panic on operand-width overflow. Probe: `uint16 f(uint8
a, uint8 b) { return a + b; }` with `a=200, b=100` returned 300; pinned solc /
Forge Panic 0x11.

**solc semantics.** A binary arithmetic op is evaluated at the operands' common
type regardless of a wider target; overflow at that width Panics 0x11, and the
(checked) result is only then implicitly widened. So `uint8 + uint8` overflow
panics even when the target is `uint16`/`uint256`.

**Wrong → right (`Interface.lean`, `Expr.toCoreAsWithEnv?` binary arm).**
`binaryToCoreWithEnvTyped?` returns the BARE op (its overflow check lives in the
result cleanup at the operand width `sourceTy`), and `coreAsFromTy?` for a WIDER
target applied only the TARGET-width cleanup — which can never catch the operand
overflow (the un-narrowed sum fits the wider type). The binary arm now wraps the
result in `Ty.implicitCleanupCore sourceTy` (the operand-width Panic 0x11) BEFORE
`coreAsFromTy?`, but only for overflow-arithmetic ops (`+ - * / % **`);
comparisons and bitwise ops never overflow their operand width, and a same-width
target's `coreAsFromTy?` cleanup is then idempotent. An explicitly-256-bit-widened
`uint16(uint256(a) + uint256(b))` keeps its non-panicking 256-bit semantics (the
operand casts move the common type to `uint256`).

**Right value (Forge-verified).** Lane `narrow-arith-widened`:
`addU8toU16(100,55)=155`, `addU8toU16(200,100)` Panic 0x11, `mulU8toU16(20,20)`
Panic 0x11, `addI8toI16(100,20)=120`, `addI8toI16(100,100)` Panic 0x11,
`addWidenedOperands(200,100)=300`. `forge=ok lean=ok compare=pass`.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass`; additionally spot-ran 14 arithmetic/token/math
lanes lean-only (checked-arithmetic, openzeppelin-{safecast,signed-math,erc20,
checkpoints,erc20-snapshot}, solmate-erc20, uniswap-v3-math, packed-ternary-width,
udvt-operator-dispatch, ternary-literal-mobile-type, signed-literal-arithmetic,
narrow-udvt-arithmetic, literal-cast-conversions) — all `lean=ok compare=pass`,
no regression from the added operand-width panics. The full 133-case replay is the
coordinator's merge gate.

## 2026-07-08 — Round-2 acceptance-boundary divergences E1/E2/O1/PT1 fixed; AE1 already-handled; CF2 documented-stays

Fixing the acceptance-boundary divergences in `docs/solc-implementation-divergences-2.md`.
All are accept/reject-boundary only (no wrong runtime value). Each rule was read
in solc source (`/Users/dan/Projects/solidity-src`, v0.8.35 = the pinned binary),
probed against the pinned solc 0.8.35 binary on the exact case AND a neighbor that
must keep its current behavior, fixed minimally in `SolidCore/Solidity/TypeCheck.lean`,
then re-probed. Lane: `tests/forge-harness/acceptance-boundaries-round2/` +
witnesses `SolidCore/Witness/AcceptanceBoundariesRound2.lean`, manifest case
`acceptance-boundaries-round2`.

**E1 — non-rational immutable read in a `pure` function (over-accept → FIXED).**
solc `ViewPureChecker.cpp:194-199`: an immutable read is `Pure` ONLY if the
initializer's type category is `RationalNumber`; every other initializer makes the
read `View` (TypeError 2527). Solidus dropped ANY compile-time-constant-init
immutable from `stateNames` via the broad `exprIsCompileTimeConstant` (true for
`keccak256`, `abi.*`, `concat`, `type().wrap`, a `constant` reference, `bool`/
`string` literals, explicit conversions). Fix: new predicate `exprIsRationalConstant`
(numeric `number`/`unitNumber` literals; unary `-`/`~` over a rational; the
arithmetic/bitwise/shift binary operators over rationals — reusing
`BinaryOp.storageLayoutBaseEvalAllowed`; comparison/logical operators and ternaries
excluded). `StateVarDecl.hasCompileTimeImmutableInit` now uses it, so only a
RationalNumber immutable stays out of the state-read set; every other immutable
joins the existing runtime-immutable class (identical, already-correct `isState`
handling at the ident-read site). Boundary probed against pinned solc: `uint
immutable X=5;`, `2+3`, `1 ether`, `-3`, `~1`, `1<<4` read in `pure` ACCEPT;
`keccak256("x")`, a `constant` ref, `true`, `uint(5)`, `3<5`, `true?1:2` read in
`pure` REJECT (2527); the same reads in a `view` function ACCEPT. Lane fixtures
`E1KeccakImmutableInPure.sol` / `E1ConstantRefImmutableInPure.sol` (solc-reject);
witnesses `e1KeccakImmutableInPureRejected` + `e1NeighborsAccepted`.

**E2 — `this.f.selector` in a `pure`/non-view function (over-reject → FIXED).**
solc `ViewPureChecker.cpp:357-370` special-cases `this.f.selector` — `this` is
never visited, so it contributes NO state read and stays Pure. Solidus recursed
into the inner `this` (ident-`this` runs `requireStateReadAllowed`) and rejected it
in `pure`. Fix: a dedicated match arm for
`Expr.member (Expr.member (Expr.ident "this") member) "selector"` resolves the
current contract's external-callable function value (`env.currentContract` +
`resolveContractExternalFunctionValue`) and returns `bytes4` without a state read;
it also still rejects a private/internal `f` ("member not found"), matching solc.
Only `.selector` is loosened — `this.f()` still routes through the call path and
remains a `pure`/`view` violation. Probed: `this.f.selector` (f public or external)
in `pure`/`view` ACCEPT; `this.f()` in `pure` REJECT; `this.f.selector` for private/
internal `f` REJECT. Witnesses `e2ThisSelectorInPureAccepted` +
`e2ThisCallInPureStillRejected`.

**O1 — duplicate contract in `override(A, A)` (over-accept → FIXED).**
solc `OverrideChecker.cpp:850-879` rejects a duplicate in the override list
(error 4520). Solidus `checkOverrideSpecifier` used `pathSetsEqual`
(membership-both-ways, duplicates ignored). Fix: new `pathListHasDuplicate`, wired
as a `require (!…)` in both `checkOverrideSpecifier` (functions) and
`checkModifierOverrideUse` (modifiers). Probed: `override(A, A)` REJECT (4520);
`override(A, B)` legit diamond and `override(A)` single base ACCEPT. Lane fixture
`O1DuplicateOverride.sol`; witnesses `o1DuplicateOverrideRejected` +
`o1DiamondOverrideAccepted`.

**PT1 — cyclic `constant` dependency (over-accept → FIXED).**
solc `ConstStateVarCircularReferenceChecker` (`PostTypeChecker.cpp:154-245`,
error 6161) rejects a `constant` whose value cyclically depends on itself. Probe
CONFIRMED the over-accept: Solidus returned `Except.ok` for `uint constant A = A;`.
Fix: `collectExprIdents` (a mutual recursion over `Expr`/`Arg`/`TupleItem`/
`CallOption`) + `StateVarDecls.constantsHaveCycle` (build the constant→constant
dependency graph restricted to declared `constant` names, fuel-bounded
`constantReachesSelf`), wired as a `require (!…)` in `ContractDecl.check`
(contract-own `constant`s ∪ file-level `constant`s) and in `SourceUnit.check`
(free `constant`s). Over-collection of idents is harmless — the graph intersects
with declared `constant` names, and a false cycle would need a coincidental name
collision forming a full loop (impossible in valid code; the smoke gate confirms no
corpus regression). Scope limitation (documented): the graph is per-contract +
file-level, so a cycle spanning a contract and an *inherited* base constant is not
detected — that is safe under-detection (never over-rejects a valid program) and
covers the natural single-contract cases (self-cycle, same-contract mutual cycle).
Probed: `uint constant A = A;` and `A=B; B=A;` REJECT (6161); `A=5; B=A+1;` ACCEPT.
Lane fixture `PT1CyclicConstant.sol`; witnesses `pt1SelfCyclicConstantRejected`,
`pt1MutualCyclicConstantRejected`, `pt1NonCyclicConstantAccepted`.

**AE1 — `abi.encodePacked(bytes[]/string[])` (ALREADY-HANDLED, verified).**
solc rejects an array-of-dynamic element in packed mode ("Type not supported in
packed mode"). Solidus's typecheck predicate `Ty.isAbiEncodePackedArrayElementShape`
omits `Ty.bytes`/`Ty.string`, so a `bytes[]`/`string[]` argument is already rejected
at type-check; the interpreter right-pad fall-through the finding worried about is
unreachable for accepted programs. Verified on the Lean side:
`abi.encodePacked(bytes[])` and `(string[])` REJECT while `(uint[])` ACCEPTS
(pinned-solc agrees). No code change. Witnesses `ae1EncodePackedBytesArrayRejected`
+ `ae1EncodePackedUintArrayAccepted`.

**CF2 — no revert-pruning of always-reverting callees (over-reject → DOCUMENTED-STAYS).**
solc runs `ControlFlowRevertPruner` (an interprocedural always-reverts analysis)
before the uninitialized-storage/calldata-pointer-return check (3464), so a pointer
whose only unassigned path terminates in a call to an always-reverting *helper* is
accepted. Solidus prunes only builtin terminals (direct `revert`/`selfdestruct`).
Probe CONFIRMED a real over-reject on a natural single-contract program: a
`returns (uint[] storage p)` whose `else` branch calls an always-reverting internal
helper is REJECTED by Solidus but ACCEPTED by solc; the direct-`revert` form is
already accepted by both, and the genuinely-uninitialized form is rejected by both.
STAYS: a correct fix requires porting solc's interprocedural always-reverts CFG pass
(compute, per internal function, whether it always reverts, then treat calls to such
functions as path terminals in the pointer definite-assignment flow) — a substantial
analysis, not a cheap local change. The divergence is a SOUND over-reject (never
accepts an invalid program), confined to the narrow class of storage/calldata-pointer
returns whose sole unassigned path terminates in an always-reverting helper call, and
the direct-revert form already works. Recorded so it is not lost.

Gates: `lake build SolidCore` green; `scripts/smoke_replay.sh` 28/28 lean=ok,
`forge_interpreter_compare=pass` (no valid corpus program newly rejected); lane
`acceptance-boundaries-round2` `solc_rejects=ok lean=ok`
(`round2AcceptanceBoundariesHold = true`). The full 137-case replay is the
coordinator's merge gate.

## 2026-07-08 — Item #2/#6 REAL-FIXED: `x ** y` is now O(log y) (exponentiation by squaring)

`SolidCore/Solidity/Interpreter.lean` `checkedExp`/`checkedSignedExp`.

**Bug (soundness of termination + denial).** The old `checkedExpLoop`/
`checkedSignedExpLoop` multiplied the accumulator `y` times — O(y). solc/EVM
compute `base ** exp` in O(log y) via `EXP`. A large runtime exponent under
`unchecked` (e.g. `3 ** (2**200)`) made the Lean interpreter loop 2^200 times →
hang/timeout, while pinned solc/Forge return the wrapped value immediately.
Probe: `uncheckedBigExp(3, 2**200)` (Forge) →
`90227379838503308256418949283165379265846182674772648785782829402385907974145`.

**Fix.** `expBySquaring` (O(log e), fuel 257 bounds a 256-bit exponent's
halvings) with two reducers: `natPowMod` (modular, for the two's-complement
wrapped result) and `natPowCapped` (saturating at a cap, for overflow
detection). Because every intermediate power in exponentiation by squaring is
`<= base ** exp`, the capped result is exact below the cap and saturates exactly
when the true power reaches it — so checked exp Panics 0x11 at the SAME point as
the old repeated-multiply loop (item #6: signed narrow-width panic still comes
from the enclosing `intCleanup`; int256 overflow decided from magnitude+sign:
positive overflows at `|r| >= 2^255`, negative at `|r| > 2^255`).

**Verified** against pinned solc/Forge: unsigned wrap `3**(2**200)`, checked
`2**256`→panic / `2**255`→ok; signed `(-2)**9`→wrap 0 (int8), `(-2)**3`→-8,
int256 `2**255`→panic / `2**254`→ok. Existing `checked-arithmetic` lane
(negBaseEven/Odd, negExpOverflow) still green. **Lane:** `exp-by-squaring`.

## 2026-07-08 — Item #1 REAL-FIXED: narrow value-array storage packing no longer straddles slots

`SolidCore/Solidity/Interpreter.lean` `StorageLayout.slotSpan`,
`StorageLayout.cursorStep`, `StorageLayout.arrayElementOffsetAndLayout?`.

**Bug (wrong-slot / wrong-value).** The three functions tight-bit-packed narrow
value-type array elements (`byteOffset := index * widthBytes`; slots =
`ceil(size*widthBytes/32)`), letting a value element straddle a slot boundary.
solc NEVER splits a value element across slots: elements-per-slot =
`floor(32/widthBytes)`, an element that would not fit the slot tail starts a
fresh slot (padding waste). Probe (`--combined-json storage-layout` +
raw-`sload`): `uint72[7]` = 3 slots not 2, element 3 at slot 1 offset 0 not
slot 0 offset 27; `uint96[]` packs 2/slot; `bytes3[]` packs 10/slot;
`uint128[3]` = 2 slots; `bytes3[5]` = 1 slot.

**Fix.** perSlot = `max 1 (wordBytes / widthBytes)`; slotSpan(fixedArray) =
`ceil(size / perSlot)`; element `index` → slot `index / perSlot`, in-slot offset
`(index % perSlot) * widthBytes`. Verified identical to solc for uint72/uint96/
bytes3/uint128 (slot counts and per-element slot+offset). **Lane:**
`storage-array-packing`.

## 2026-07-08 — Bug-batch triage: items #3/#4/#5/#7/#8/#9/#10/#11 ALREADY-FAITHFUL

Investigated with pinned solc 0.8.35 + Forge ground truth and end-to-end Lean
witnesses (importer → checker → interpreter). None diverge; recorded here so the
list is not re-opened.

- **#3 narrow signed div/neg overflow.** Probe: `int8(-128)/int8(-1)` and
  `-int8(-128)` → checked Panic 0x11, unchecked wrap to -128. `checkedSignedDiv`/
  `checkedSignedNeg` only special-case the 256-bit min, but the narrow overflow
  is caught by the enclosing `intCleanup` the importer inserts: for a binary op
  via `implicitCleanupCore` at the operand width (`isOverflowArithmetic` includes
  `div`/`mod`); for unary neg via the return/target-type cleanup. Witness:
  divUnchecked→-128, divChecked→panic, negUnchecked→-128, negChecked→panic. All
  match.
- **#4 modifier placeholder `_` inside nested blocks.** The active lowering
  `Stmt.toCoreReplacingModifierPlaceholder?` (Interface.lean) recurses through
  block/if/while/for/try/unchecked, so a nested `_` is substituted. The
  top-level-only `Stmt.replaceTopLevelModifierPlaceholder` has NO call sites
  (dead code). Probe (modifier with `_` inside `if`): solc and Solidus both
  return 121.
- **#5 abi.encode of narrow uintN/intN.** solc always cleans before encoding;
  Solidus maintains the clean-value invariant (eager cleanup on every
  arithmetic/cast/decode), so `abiEncode` never sees dirty high bits. Probe:
  `uint8 x=200; unchecked{x=x+100;}` (wraps to 44) → both encode 0x2c. Dirt only
  arises via inline assembly, outside importer/corpus scope.
- **#7 transient storage (EIP-1153) clearing granularity.** `clearTransient` is
  applied at the TRANSACTION boundary only: `Contract.callTransaction` clears
  before and maps `CallResult.clearTransient` over the result;
  `ContractCallKind.messageCall` preserves transient across nested calls within a
  tx. Correct tx-scoped semantics (not per-call, not never).
- **#8 `require(cond, CustomError(...))` (0.8.26+).** solc accepts. NOT
  over-rejected: the Python importer emits the two-arg `require`, the Lean matcher
  lowers it to `Stmt.requireCustom`, and the interpreter reverts with
  `RevertData.custom name args` on failure. Witness: `require(a>10, Bad(a))`
  f(15)→returns 15, f(5)→reverted custom "Bad"[5]; `require(c, Plain())`
  false→"Plain"[]. (Independently cross-checked faithful by a sibling agent.)
- **#9 signed `<=`/`>=` derivation.** `applySignedWord` routes `le`→`!sgt`,
  `ge`→`!slt` (i.e. SLE/SGE). Witness: -5<=3 true, -5>=3 false, 3<=-5 false,
  -5<=-5 true. All match solc.
- **#10 intN ABI-decode canonical-form validation.** solc's `validator_revert_t_*`
  reverts (empty data) on a non-canonical intN/uintN in `abi.decode`. Solidus
  wraps decoded narrow values in `Value.abiLazy cleanup`; `AbiCleanup.accepts`
  reconstructs the canonical form and `AbiCleanup.forceValue` reverts
  `RevertData.empty` on mismatch (pinned by the existing abi-malformed lanes).
  Probe: dirty int8 → solc reverts; Solidus reverts empty. Match.
- **#11 fixed-array-of-dynamic head-offset base, nested one level.** Encoder
  bases inner head offsets on the fixed array's own data region. Unit test:
  `abi.encode(uint256[][2])` with `[[0xaa],[0xbb,0xcc]]` → Solidus words
  `[0x20,0x40,0x80,1,0xaa,2,0xbb,0xcc]`, byte-identical to solc/Forge. (A
  separate `uint256[][2] memory` + `new uint256[]` init probe hit an unrelated
  memory-array-allocation limitation — M-series territory, not this ABI item.)

## 2026-07-08 — EC1 fixed: `abi.encodeCall` selector + encoding from DECLARED parameter types

`docs/solc-encodecall-selector-review.md` EC1 (wrong-VALUE family, pinned-solc
0.8.35 confirmed). solc derives the 4-byte selector AND the argument encode
types of `abi.encodeCall(fnPtr, args)` from the callee's DECLARED parameter
types, never from the argument expression types. Two repros bracket the bug:
an argument narrower than the parameter (`i.foo`, `foo(uint256)`, `uint8` arg →
`0x2fbebd38`) and an integer literal against a narrow parameter (`this.foo`,
`foo(uint8)`, literal `3` → `0x11602fb3`). Both verified against the pinned
compiler's `--ir` / `--hashes`.

**Two defects on the same path (both closed).**

- **Lowering wrong-value (the reported bug).** `Expr.functionPointerSelectorCore?`
  built the signature from `argTys`, and the two `abi.encodeCall` lowering sites
  fed both the selector AND the encode `coreTys` from the argument expression
  types. Because the env-free `Expr.toCore?` never sees the callee's parameter
  types, the fix is in the typed pre-pass `Expr.annotateAbiFuel` (which carries a
  `TypeEnv`): for the `encodeCall` branches it resolves the callee's declared
  parameter types via a new `Expr.encodeCallDeclaredParamTys?` (reads the
  `__external_call_kind:<contract>:<fn>(...)` entries already carried in the type
  env) and wraps each argument whose ABI-canonical type differs from its
  parameter in an explicit conversion to the PARAMETER type. Downstream both the
  selector signature (`sourceTys`) and the encode types (`coreTys`) are then
  taken from the parameter types. When the argument's ABI-canonical type already
  matches the parameter (the overwhelmingly common exact-typed case, incl.
  reference-type params) the annotation is byte-for-byte the pre-existing one, so
  there is no regression. `functionPointerSelectorCore?` itself is unchanged —
  other callers keep their behavior.

- **Typecheck over-reject (found during verification, same path).** The reported
  analysis assumed both repros were accepted; in fact the narrower-argument repro
  was OVER-REJECTED (`unknownFunction "foo"`). The `encodeCall` member-pointer
  checker resolved the pointer with the type-EXACT contextual resolver
  (`resolveContractMemberFunctionContextual`), which only matches an exact type
  or an untyped literal — so a `uint8` variable passed where a `uint256` is
  declared found no overload. solc resolves an `encodeCall` pointer by name alone
  (it must be unique) and checks convertibility separately. Fix: new
  `TypeContext.resolveEncodeCallPointerSig` resolves by name + arity (a genuine
  same-arity overload is `ambiguousFunction`, matching solc's "must be unique"),
  and the two member-pointer resolution sites use it. The per-argument
  assignability check (`checkEncodeCallTupleItemsAssignableTo` /
  `checkArgAssignableToParam`) is unchanged, so a truly non-convertible argument
  is still rejected (just downstream, as an assignability error). The general
  contextual resolver used elsewhere is untouched.

**Pinned.** One Forge-paired lane `abi-encodecall-selector`: a harness contract
whose two public functions return the `encodeCall` bytes for both repros; the
Forge test asserts the bytes against solc/EVM (`bytes4(...) ==
IEncodeCallCallee.foo.selector` / `EncodeCallSelectorHarnessTarget.foo.selector`
and full `abi.encodeWithSelector(sel, uint256(3)/uint8(3))`), and the imported
Lean eval checks the Solidus interpreter returns
`encodeSelector(selectorFromSignature "foo(uint256)"/"foo(uint8)") ++
encodeWord 3` for each. Pre-fix the lane fails on both counts (narrow repro
over-rejected at typecheck; literal repro's selector wrong).

Validation: `lake build` green; `scripts/smoke_replay.sh SMOKE_JOBS=6 --only
abi-encodecall-selector` = 29 cases `forge_interpreter_compare=pass`; the new
lane also passes with Forge on (`forge=ok lean=ok`); all four encodeCall-using
lanes (`abi-encodecall-selector`, `abi-malformed`, `function-member-kinds`,
`receive-fallback-dispatch`) re-verified green.
