import SolarTV.Sem
import EvmYul.SpongeHash.Keccak256

/-!
# solar-verify's spec language: syntax

solar-verify (paradigmxyz/solar, crates/verify) reads specs from NatSpec tags:
`@custom:requires`, `@custom:ensures`, `@custom:succeeds-if`, `@custom:invariant` on a contract
or a struct, `@custom:ghost` declarations and updates, and spec functions, plain or
`@custom:opaque`. Its exporter (`solar-verify --emit-lean`) writes each contract's specs in the
syntax below, and `SolidCore.Spec.Semantics` gives them their meaning over the calls and
observables of SolidCore and EthLib (`SolarTV.Call`, `SolarTV.Observable`).

Spec expressions are Solidity expressions over mathematical integers, as solar-verify encodes them
(`src/vc.rs`, `arith` with `spec` set): one sort, `Int`, with booleans as `0` and `1`. A spec
reads the contract's storage through `Place`s the exporter resolves from the storage layout
(state variables, mapping entries, array elements, struct fields), so its meaning is over the raw
slots the bytecode reads and writes, not over solar-verify's per-variable model of them.

Every form the exporter does not translate is an export error, never a dropped spec.
-/

namespace SolidCore.Spec

/-- The value types a spec reads, binds and returns. -/
inductive Ty where
  /-- `uintN`, `bits` a multiple of 8 up to 256. -/
  | uint (bits : Nat)
  /-- `intN`, two's complement. -/
  | int (bits : Nat)
  | bool
  | address
  /-- `bytesN`, read as the unsigned integer of its `n` bytes. -/
  | fixedBytes (n : Nat)
  /-- An enum with `count` members, read as its index. -/
  | enum (count : Nat)
  /-- A mathematical integer: the type of a `mathint` or `integer` quantifier binder. -/
  | math
  deriving Repr, DecidableEq, Inhabited

/-- Environment values of a call. `time` is solar-verify's `__time`, the latest
`block.timestamp` the contract has seen. -/
inductive EnvVar where
  | sender | value | timestamp | self | time
  deriving Repr, DecidableEq, Inhabited

/-- Unary operators. -/
inductive UnOp where
  | neg | not
  deriving Repr, DecidableEq, Inhabited

/-- Binary operators. The logical operators take and give `0` and `1`. -/
inductive BinOp where
  | add | sub | mul | div | mod | pow
  | band | bor | bxor
  | eq | ne | lt | le | gt | ge
  | and | or | implies
  deriving Repr, DecidableEq, Inhabited

mutual
/-- A spec expression. -/
inductive Term where
  | lit (v : Int)
  /-- The `i`th parameter of the function, as the call passed it. -/
  | arg (i : Nat)
  /-- The `i`th return value (`result` is `ret 0`; named returns are their index). -/
  | ret (i : Nat)
  /-- A variable bound by a quantifier or a spec function's parameter. -/
  | var (name : String)
  | env (v : EnvVar)
  /-- The value of type `ty` stored at `place`, `size` bytes from byte `offset` of its slot
  (counted from the least significant byte; computed for packed array elements). -/
  | load (place : Place) (offset : Term) (size : Nat) (ty : Ty)
  /-- The length of the dynamic storage array at `place`: the word in its slot. -/
  | len (place : Place)
  /-- A ghost variable; `keys` index a ghost mapping. Ghost state starts at zero. -/
  | ghost (name : String) (keys : List Term)
  /-- `old(e)`: `e` in the pre-state (storage, ghost state and `__time` of the call's start). -/
  | old (e : Term)
  | un (op : UnOp) (e : Term)
  | bin (op : BinOp) (a b : Term)
  /-- `e << k` by a literal `k`: wraps modulo `2 ^ 256`, as solar-verify's specs do. -/
  | shl (e : Term) (k : Nat)
  /-- `e >> k` by a literal `k`: the floor of `e / 2 ^ k`. Shifts by a computed amount are export
  errors, since solar-verify encodes them through a table that differs from `2 ^ k` past 255. -/
  | shr (e : Term) (k : Nat)
  /-- `c ? a : b`. -/
  | ite (c a b : Term)
  /-- `forall T x :: body` (one binder; the exporter nests several). -/
  | all (x : String) (ty : Ty) (body : Term)
  /-- `exists T x :: body`. -/
  | ex (x : String) (ty : Ty) (body : Term)
  /-- A call of the spec function `fn`. -/
  | call (fn : String) (args : List Term)
  deriving Repr, Inhabited

/-- A storage location, resolved from the storage layout. -/
inductive Place where
  /-- A slot fixed by the layout. -/
  | slot (n : Nat)
  /-- `k` slots after `base`: a struct field, or an element of a fixed-size array. -/
  | offset (base : Place) (k : Term)
  /-- The entry of the mapping at `base` for the value-typed key `key`:
  `keccak256(key ++ slot(base))`, both as 32-byte words. -/
  | entry (base : Place) (key : Term)
  /-- Element `index` of the dynamic array at `base`, whose elements take `slots` slots each:
  `keccak256(slot(base)) + index * slots`. -/
  | elem (base : Place) (index : Term) (slots : Nat)
  /-- The slot holding packed element `index` of the dynamic array at `base`, `perSlot` elements to
  a slot: `keccak256(slot(base)) + index / perSlot`. Its byte offset is the reader's. -/
  | packedElem (base : Place) (index : Term) (perSlot : Nat)
  deriving Repr, Inhabited
end

/-- A spec function: a single-`return` pure or view function solar-verify unfolds in specs.
An `isOpaque` one is uninterpreted in solar-verify's proofs except where revealed; its meaning
here is its body, and `ret` is the range solar-verify assumes of its result
(`Semantics.OpaqueInRange`). -/
structure SpecFn where
  name : String
  params : List (String × Ty)
  ret : Ty
  body : Term
  isOpaque : Bool
  deriving Repr, Inhabited

/-- One function's spec. -/
structure FnSpec where
  /-- `Contract.name`. -/
  name : String
  /-- The 4-byte ABI selector. -/
  selector : Nat
  params : List Ty
  rets : List Ty
  payable : Bool
  requires : List Term
  ensures : List Term
  succeedsIf : List Term
  deriving Repr, Inhabited

/-- A contract's specs. `invariants` are the contract's `@custom:invariant`s and, expanded
by the exporter over every stored value of the struct, its structs' invariants. -/
structure ContractSpec where
  name : String
  fns : List SpecFn
  invariants : List Term
  ghosts : List String
  specs : List FnSpec
  deriving Repr, Inhabited

/-- What a spec was exported from: the source and its sha256, the compiler that built the
bytecode, its options, and the runtime bytecode's sha256. `solar-verify --emit-lean` writes it;
a theorem about the spec is about these bytes only. -/
structure Manifest where
  source : String
  sourceSha256 : String
  compiler : String
  options : List String
  bytecodeSha256 : String
  deriving Repr, Inhabited, DecidableEq

end SolidCore.Spec
