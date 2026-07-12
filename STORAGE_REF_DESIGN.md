# WS2 — Storage-reference EARLY binding (closes #146 / #177)

## Problem

The model late-binds storage references: a bound storage pointer is
`Value.storagePathRef root indexPath`, and every dereference re-runs
`State.resolveStoragePathSlot` from the root — including the dynamic-array
length check. solc/EVM early-bind: `T storage p = arr[i]` bounds-checks and
computes the concrete slot ONCE at the binding access, then raw-`sload`s with
no recheck (solc `ArrayUtils::accessIndex` emits the check at the access that
binds; the resulting `StorageItem` LValue carries only slot+offset —
`LValue.cpp`). Divergence (#177): `S storage p = arr[i]; arr.pop(); p.a` —
model Panic 0x32, EVM reads the freed (pop-zeroed) slot and returns 0.

## Representation chosen

* `Value.storageRef : String -> Value` — UNCHANGED, kept for WHOLE-variable
  refs (`S storage p = s0;` / `return arr;`). A whole state variable's base
  slot is a compile-time constant, so the name form is already early-bound
  (nothing dynamic is ever re-resolved to reach its base), and keeping it
  preserves the legacy no-layout (`field.ty?` fallback) and `transient`
  handling that is keyed off the field record.
* `Value.storagePathRef : String -> List Value -> Value` — REPLACED by
  `Value.storageSlotRef : Word -> StorageLayout -> Value`: the CAPTURED
  concrete base slot plus the storage layout AT that slot (element type /
  stride / dynamic-ness — everything further indexing or member access
  needs). Resolution to produce it runs ONCE at the binding site (running the
  bounds check there, as solc does).
* `inductive StorageLayout` moves textually above `inductive Value`
  (definition-order only; no change to the type).
* A small plumbing type replaces the `(rootName, indexes)` pairs:

      inductive StorageBase
        | field : String -> StorageBase          -- whole state variable
        | slot  : Word -> StorageLayout -> StorageBase  -- captured pointer

  `Runtime.lookupStorageBase?` maps a local holding `storageRef n` to
  `.field n` and `storageSlotRef s l` to `.slot s l`. All the path
  helpers (`loadStoragePath` / `storeStoragePathWithDeepClear` /
  `deleteStoragePath` / `storagePathSlotValue` / `storageArrayPushPath` /
  `storageArrayPopPath`) are generalized to take a `StorageBase`; the
  name-rooted forms stay as thin wrappers over `.field`.

Rationale vs alternatives: adding a captured-slot FIELD to the existing
`storagePathRef` (keeping the path too) would keep two sources of truth and
invite accidental re-resolution; replacing the constructor is safe because
proof exposure is tiny (see sizing below).

Use-site indexing stays live, as on the EVM: `p[j]` on a bound
`uint[] storage p` resolves ONE step from the captured slot — checking the
CURRENT length stored at that slot — exactly like solc's bounds check at the
access. Early binding fixes the BASE slot only; reads/writes through the
pointer see live slot data.

## Bind sites (all resolve-once now)

| Site | Construct | Mechanism |
| --- | --- | --- |
| `Stmt.storageAlias` | `S storage p = s0;` | unchanged (`Value.storageRef`) |
| `Stmt.storageAliasPath` | `= arr[i]` / `= m[k]` / `= s.f` decl | eval indexes, `bindStorageRef (.field target)` → `storageSlotRef` (Panic 0x32 at bind if OOB) |
| `Stmt.storageAliasFrom` | `= q` (another pointer) | copy source ref value |
| `Stmt.storageAliasFromPath` | `= q[i].f` | resolve extras from source base NOW |
| `Stmt.storageAliasAssign(Path/From/FromPath)` | re-points incl. #188 return-capture rewrites | same resolution, then raw re-point of the ref local |
| `Expr.evalRefArg` | storage-ref ARGUMENT to internal call | passes the (already bound) ref value through |
| internal-call RETURN capture (`assignLocalRefAware?` / `coerceLike?` repoint) | #188 | adopts the already-bound ref value; write-through unchanged |
| ternary storage-pointer init | `= c ? arr[i] : arr[j]` | elaborates to alias stmts per branch (unchanged shape), each resolving at bind |

## Deref/use sites — captured slot, no recheck

`Expr.var`, `Expr.length`, `Expr.index` over ref-rooted bases,
`Expr.storageRefSlot`, `ResolvedLValue` read/write/delete, push/pop through
refs, `materializeForValueUse` all go through
`StorageBase`-rooted helpers: for `.slot s l` they start at `(s, l)` — no
root re-resolution, no length recheck for the already-bound prefix.
`ResolvedLValue` gains `storageSlotPath : Word -> StorageLayout -> List Value`
(captured base + extra indexes accumulated at THIS use, resolved live).

## Proof-churn sizing (Stage A)

`grep storageRef\|storagePathRef` over proof files:

* `FuelMonotonicity.lean` — ZERO hits. Its mutual induction is over the
  STATEMENT cluster only; expression/lvalue evaluation is a fuel-closed
  prefix "shared verbatim by both sides" (its own header). The alias-stmt
  arms (`storageAliasAssign*` etc.) do not recurse into `Stmt.eval`, so
  changing their bodies keeps the per-arm proofs shape-stable. Risk:
  arm-local `simp only` vocabulary may need small adjustments.
* `AdoptionLaws.lean` — zero hits.
* `Interaction.lean` — zero hits (35 lines, alphabet only).
* `Witness/Checked.lean` — one equality function (`checkedCoreValueEq`)
  matches `storagePathRef`; becomes a slot/layout comparison
  (`StorageLayout` gains `BEq`).
* `Interface.lean` / `TypeCheck.lean` — comment-only mentions; the
  elaboration emits alias STATEMENTS whose shapes are unchanged.

Estimated churn: ~40 mechanical sites in `Interpreter.lean`, 1 in
`Witness/Checked.lean`, 0 expected in proof files (verified by full
`lake build` at each stage).

## Stage A baseline (measured)

Real EVM (Forge, pinned solc 0.8.35, lane `storage-ref-early-bind`, 9/9
PASS): t1=0, t2=9, t3 Panic 0x32, t4=33, t5=88, t6=5, t7=42, t8=88, t9=55.

Model at 458f877 (importer probe, same source): t1 **Panic 0x32** (diverges),
t2=9, t3 Panic 0x32 (matches, though raised at deref not bind), t4=33,
t5=88, t6 **Panic 0x32** (diverges — dangling write also over-reverts).

## Behavior deltas (intended, ground-truthed)

* pop-then-deref (`t1`): Panic 0x32 → returns 0 (EVM-verified via Forge lane
  `storage-ref-early-bind`).
* bind-time OOB (`t3`): still Panic 0x32 (unchanged, now raised AT bind —
  same observable for the repro shapes).
* pop-then-push-then-deref (`t2`), live-mutation (`t4`), mapping-value ref
  (`t5`), all #188 write-through shapes: unchanged (controls).

## Results (Stage B+C, commit d8476e7)

* Post-fix importer probe: t1 = 0 (was Panic 0x32), t2 = 9, t3 Panic 0x32,
  t4 = 33, t5 = 88 — all matching the Forge lane.
* `lake build SolidCore` green (1144 jobs) and full `lake build` green —
  FuelMonotonicity, AdoptionLaws and ALL pre-existing witnesses compiled and
  passed with ZERO proof edits (the sizing prediction held: the mutual
  induction is over the statement cluster; expression/lvalue evaluation is a
  fuel-closed prefix, and the reworked alias-stmt arm bodies don't recurse).
* Self-gate, sequential `--only` (pinned solc + forge), all
  `forge=ok lean=ok`: storage-ref-early-bind, storage-ref-path-return,
  storage-value-boundary, aggregate-array-span, storage-array-packing,
  openzeppelin-enumerable-map, openzeppelin-enumerable-set,
  reference-assignments, reference-via-ir-memory-storage,
  eval-order-intrinsic, ternary-storage-pointer, reference-mapping-storage,
  lib-storage-return-use, lib-storage-public-2. ("storage-aggregate" from
  the work order does not exist as a lane name; aggregate-array-span +
  storage-array-packing stood in.)

## Known adjacent residue (NOT in scope, reported)

Write-through-dangling then `push()` (`t6` probe): real EVM `push()` does not
clear the new element slot (relies on the pop-time zeroing invariant), so a
dangling write survives re-growth; the model's `storageArrayPush*` deep-clears
the pushed element and would return 0 where the EVM returns the planted 5.
Pre-existing model behavior (reachable, before WS2, only via adoption-planted
words past the array length); left unchanged here, flagged for a follow-up.
