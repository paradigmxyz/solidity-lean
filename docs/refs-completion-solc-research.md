# solc ground truth for the boundary-completion arc (task #9)

**Date:** 2026-07-07. **Method:** direct `--ir` probes of the pinned compiler
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`), the same via-IR
pipeline our Yul target (`../evm-compiler`) models. Probe sources and full IR
outputs were reproduced from the four fixtures inlined below; every claim in
this document was read directly off the emitted Yul, not from documentation.

This document exists so the implementing agent designs stages A–D of task #9 to
solc's actual model rather than a plausible one. Where our interpreter already
has a matching mechanism, that mapping is stated explicitly.

---

## 1. Storage-ref returns (stage A)

**Probe:**

```solidity
contract P1 {
  uint[] xs;
  function pick() internal returns (uint[] storage) { return xs; }
  function use() public returns (uint) { uint[] storage p = pick(); p.push(7); return p[0]; }
}
```

**Emitted Yul (via-IR):**

```
function fun_pick_13() -> var__8_slot { ... }
...
let expr_24_slot := fun_pick_13()
```

**Facts:**

- An internal function returning `T storage` returns **exactly one word: the
  slot**. There is no byte-offset component in via-IR return values — storage
  pointers to reference types (arrays, structs, mappings, `bytes`/`string`)
  always begin at a slot boundary, so slot alone identifies the referent.
  (Legacy codegen threads `(slot, byteOffset)` pairs; via-IR does not, and we
  target via-IR.)
- The caller binds the returned slot as an ordinary Yul local
  (`let expr_24_slot := ...`) and all subsequent reads/writes go through the
  same storage-access helper functions used for any storage pointer. Nothing
  distinguishes a returned storage pointer from a passed-in one after the call.
- Definite assignment of storage-pointer return variables is enforced by the
  solc **frontend** (a function cannot return an unassigned `T storage`
  named return). Since our corpus is solc-accepted by construction, the
  interpreter never sees an undefined storage-ref return and needs no runtime
  default for one. The `pointer-return-definite` sentinel in Interface.lean
  covers the elaboration side.

**Design guidance:** returning a storage ref through the boundary is *value
return of the existing `Value.storageRef`* — the same flowing-reference model
the refsig arc already landed for arguments. The only missing piece is
mechanical: wire the wrapper-caller capture in `internal*CallCore?` so the
returned `Value.storageRef` lands in the caller's binding, then drop `storage`
from `isBoundaryReturnLocation`. No new value forms, no copy semantics, no
(slot, offset) pair.

---

## 2. Internal function pointers (stage C)

**Probe:**

```solidity
contract P2 {
  function(uint) internal pure returns (uint) fp;          // state variable!
  function dbl(uint x) internal pure returns (uint) { return 2*x; }
  function trip(uint x) internal pure returns (uint) { return 3*x; }
  function set(bool b) public { fp = b ? dbl : trip; }
  function call1(uint x) public returns (uint) { return fp(x); }
  function callLocal(uint x) public pure returns (uint) {
    function(uint) internal pure returns (uint) g;         // uninitialized
    if (x > 10) g = dbl;
    return g(x);
  }
}
```

**Emitted Yul (via-IR), the load-bearing parts:**

```
/// @src "dbl"   let expr_40_functionIdentifier := 1
/// @src "trip"  let expr_41_functionIdentifier := 2

function dispatch_internal_in_1_out_1(fun, in_0) -> out_0 {
    switch fun
    case 1 { out_0 := fun_dbl_21(in_0) }
    case 2 { out_0 := fun_trip_33(in_0) }
    default { panic_error_0x51() }
}

let expr_55 := dispatch_internal_in_1_out_1(expr_53_functionIdentifier, expr_54)

function cleanup_from_storage_t_function_internal_...(value) -> cleaned {
    cleaned := and(value, 0xffffffffffffffff)     // 8-byte storage type
}
function prepare_store_t_function_internal_...(value) -> ret { ret := value }
// stored via update_byte_slice_8_shift_0 (occupies 8 bytes; packs)
```

**Facts:**

1. **Representation:** an internal function pointer value is a **small
   sequential numeric ID** (1, 2, …) assigned per contract, in order, to
   exactly the functions that are *used as values* somewhere (added to the
   "internal dispatch"). A function identifier expression in value position
   (`dbl`) compiles to the literal ID. **ID 0 is reserved** and is the value of
   an uninitialized/`delete`d pointer.
2. **Call-through-pointer:** one dispatch function **per (in-arity,
   out-arity) pair** — `dispatch_internal_in_<m>_out_<n>(fun, args...)` — a
   `switch` over every dispatch-reachable function of that arity, with
   `default { panic_error_0x51() }`. So calling an uninitialized pointer (ID 0)
   or any ID not in the table **panics with `Panic(0x51)`** — it does not
   revert with empty data and is catchable as a panic. Note the switch is
   keyed by arity only, not full type: a dirty ID of matching arity but from a
   different signature would dispatch (solc's type system prevents this for
   honestly-produced values; only adoption-planted dirty words can reach it,
   and then only if the masked ID happens to collide).
3. **Storage:** internal function pointers are **storable state variables**.
   The storage type is **8 bytes** (packs with neighbors, byte-slice update),
   and the storage **read applies `and(value, 0xffffffffffffffff)`** — the
   dirty-word cleanup for this type is a 64-bit mask, nothing more. No
   validity check happens at read time; invalid IDs surface only at call time
   as `Panic(0x51)`.
4. **No operators:** Solidity defines no comparison/arithmetic on internal
   function types, so no equality semantics are needed on the value.
5. Conversion between identical internal function types is the identity
   (`convert_t_function_internal_..._to_...(id) -> id`).

**Design guidance:** our planned `Value` constructor should mirror this
exactly — but note the storage requirement forces a **word encoding**, so a
bare table-key string is not sufficient. Recommended shape: elaborate a
per-contract numbering of dispatch-reachable internal functions (ID 1..n in
declaration-use order, 0 = invalid) alongside the existing `FunctionTable`,
carry `Value.internalFnPtr (id : Nat)` (or the ID plus cached key), and give
the interpreter an ID→table-key map next to the table. Then:

- *fn-identifier in value position* → the literal ID;
- *call through pointer* → look up ID in the map; hit → `Stmt.internalCall`
  through the existing boundary; miss (incl. 0) → `Panic(0x51)` via the
  standard panic-revert path (same machinery as the 0x21 enum panic);
- *storage write* → store the ID word into the 8-byte slice (existing packed
  WordMap write path); *storage read* → mask to 64 bits (add the fn-pointer
  case to the dirty-word read table next to bool/enum/address/bytesN/intN);
  validity is checked **at call time only**, matching solc;
- *default/`delete`* → 0.

This also resolves the postWorld interaction cleanly: an adopted world can
plant any word in a fn-pointer slot; the read masks it; a call either
dispatches to a real same-arity function or panics 0x51 — precisely solc's
behavior, no special adoption carve-out needed.

Recursion through a pointer needs no new fuel story: dispatch → internalCall
is bounded by the same statement fuel → `outOfFuel` as direct internal calls.

---

## 3. Calldata-ref arguments (stage D)

**Probe:**

```solidity
contract P3 {
  function sum(uint[] calldata a, bytes calldata b) internal pure returns (uint s) { ... }
  function go(uint[] calldata a, bytes calldata b) public pure returns (uint) { return sum(a, b); }
}
```

**Emitted Yul:**

```
function fun_sum_34(var_a_4_offset, var_a_4_length, var_b_6_offset, var_b_6_length) -> var_s_9
...
let expr_47 := fun_sum_34(expr_45_offset, expr_45_length, expr_46_offset, expr_46_length)
```

**Facts:**

- A dynamically-sized calldata reference (`T[] calldata`, `bytes calldata`,
  `string calldata`) crosses an internal boundary as **two plain words:
  (offset, length)** — offset is an absolute byte offset into calldata,
  already decoded/validated at the external boundary. Statically-sized
  calldata types (structs, fixed arrays) pass as a **single offset word**.
- Element access inside the callee is pure offset arithmetic +
  `calldataload`; nothing about the callee distinguishes a passed-in calldata
  ref from one the caller made locally. Calldata slices (`a[1:]`) just produce
  an adjusted (offset, length) pair — same value form.
- Calldata is immutable, so this is a pure read descriptor; no aliasing or
  write-back concerns.

**Design guidance:** a calldata ref is a descriptor value into
`Context.calldata` — `(offset, length)` for dynamic types, `offset` for
static — flowing through the boundary as an ordinary argument, exactly like
memory refs flow as pointers. If the interpreter already represents calldata
refs as such a descriptor (or as a materialized slice), pass it through
unchanged; the boundary needs no copy step. This pattern is *common* in
modern 0.8 code (internal helpers over calldata arrays/slices), so prefer
"flow the descriptor" over a principled exclusion unless the survey finds our
calldata value form fundamentally incompatible.

---

## 4. Tuple-literal RHS evaluation order (stage B)

**Probe:**

```solidity
function go() public returns (uint a, uint b) { (a, b) = (f(), g()); }
function goHole() public returns (uint b) { (, b) = (f(), g()); }
```

**Emitted Yul (fun_go, in order):**

```
let expr_46 := fun_f_19()
let expr_49_component_1 := expr_46
let expr_48 := fun_g_35()
let expr_49_component_2 := expr_48
var_b_40 := expr_49_component_2
var_a_38 := expr_49_component_1
```

**Facts:**

- Tuple-literal components evaluate **left-to-right**, each into its own
  temporary, **all before any assignment** to the LHS occurs. (The final
  stores happen right-to-left, but from temps, so it's unobservable.)
- A hole (`(, b) = (f(), g())`) still **evaluates the discarded component**
  (`f()` runs, including its side effects); only the store is dropped.

**Design guidance:** stage B's hoisting for `(x, y) = (f(), g())` must hoist
components **left-to-right** into temps and assign afterward. Note the
contrast with the call-argument hoisting the boundary work already does,
which is right-to-left (`yulCompatible`) — do not reuse that order for tuple
literals. Hole components hoist and evaluate like any other; the existing
tuple-with-hole assignment machinery (task #7) then discards the temp.

---

## 5. Summary table

| Residue | solc via-IR mechanism | Our mirror |
|---|---|---|
| storage-ref return | single slot word returned from Yul fn | return flowing `Value.storageRef`; wire `internal*CallCore?` capture |
| internal fn pointer | sequential numeric ID, 0 = invalid; per-arity dispatch switch, default `Panic(0x51)`; 8-byte storage type, 64-bit mask on read | `Value` with per-contract ID + ID→key map; call = lookup + `internalCall`, miss = Panic 0x51; add 64-bit mask row to dirty-word reads |
| calldata ref arg | (offset, length) word pair (dynamic) / offset word (static), plain args | descriptor value into `Context.calldata`, flows through boundary unchanged |
| tuple-literal components | left-to-right into temps, assign after; holes still evaluate | hoist L-to-R (NOT the R-to-L call-arg order); reuse hole-discard from task #7 |
