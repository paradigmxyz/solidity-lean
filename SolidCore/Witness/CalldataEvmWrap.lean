/-
WS3 / #129 CALLDATA-TAIL-WRAP witness.

Pins the EVM-faithful behaviour of the nested calldata tail-pointer accessor
`decodeBytesTailWrap?` (ABI.lean) against real-EVM ground truth captured with the
pinned solc 0.8.35 (Forge lane `tests/forge-harness/calldata-evm-wrap`):

  contract Wrap { function firstElem(bytes[] calldata a) returns (bytes) { return a[0]; } }

Calldata is the post-selector `argData` a `bytes[]` param sees, with a single
element whose tail offset is crafted. `base_ref = arrayPos = 0x80 + 0x20`,
`argData.length = 0xC0` (= EVM calldatasize 0xC4 − 4).

| elem tail offset | EVM               | model (this witness)         |
|------------------|-------------------|------------------------------|
| 2^256−128 (=-128)| returns 0xaabb    | Value.bytes [0xaa,0xbb]       |
| 2^255            | returns 0x (empty)| Value.bytes []                |
| 0x1000 (pos-OOB) | reverts (on access)| deferred marker (abiLazy)    |

The eager (memory-location) malformed-revert matrix (#22/#41/#101/#124/#128) is
UNCHANGED by WS3 — the wrap fires only on the lazy calldata path when the naive
`.drop` decode fails. The truncated-element-head control below re-asserts #128
(EMPTY revert, not Panic 0x41) is preserved.

Decoders are fuel-recursive (`brecOn`) and do not reduce under kernel `rfl`, so
results are pinned with `#guard`, which evaluates via the compiled interpreter
and fails the build if false, adding no axioms.
-/
import SolidCore.Solidity.ABI

namespace SolidCore
namespace Solidity
namespace Source
namespace CalldataEvmWrap

open SolidCore.Solidity.Source.ABI

def w32 (v : Word) : List Byte := ABI.wordToBytesBE 32 v

/-- Post-selector calldata for `firstElem(bytes[])`, single element, with the
    element tail offset `relOffset` planted in the element-head slot. Layout:
    [offset_a=0x80][target len=2][data 0xaabb..][pad][arr len=1][relOffset]. -/
def wrapCalldata (relOffset : Word) : List Byte :=
  w32 0x80
    ++ w32 0x02
    ++ w32 0xaabb000000000000000000000000000000000000000000000000000000000000
    ++ w32 0x00
    ++ w32 0x01
    ++ w32 relOffset

def decodeArr (argData : List Byte) : Except RevertData Value :=
  decodeValueAt? true argData 0 (Ty.dynamicArray Ty.bytesCalldata)

/-- Element 0 decoded to real bytes equal to `expected`. -/
def firstElemBytesEq (result : Except RevertData Value) (expected : List Byte) : Bool :=
  match result with
  | Except.ok (Value.dynamicArray (Value.bytes bs :: _)) => bs == expected
  | _ => false

/-- Element 0 is a DEFERRED marker (`abiLazy`) — reverts empty on access, never
    a boundary revert (a never-accessed pos-OOB element does not revert). -/
def firstElemIsDeferredMarker (result : Except RevertData Value) : Bool :=
  match result with
  | Except.ok (Value.dynamicArray (Value.abiLazy _ _ :: _)) => true
  | _ => false

-- WRAP SUCCESS: high-bit offset -128 wraps mod 2^256 to the in-bounds bytes.
-- EVM returns 0xaabb.
#guard firstElemBytesEq
  (decodeArr (wrapCalldata 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80))
  [0xaa, 0xbb]

-- WRAP FAR: most-negative offset 2^255 wraps far out; calldataload zero-pads to
-- length 0; the signed stride check sees a negative addr and does not revert.
-- EVM returns empty bytes.
#guard firstElemBytesEq
  (decodeArr (wrapCalldata 0x8000000000000000000000000000000000000000000000000000000000000000))
  []

-- POSITIVE OOB (regression armor): a positive offset past calldatasize fails the
-- SIGNED slt check -> deferred marker (EVM reverts on access, no boundary revert).
#guard firstElemIsDeferredMarker (decodeArr (wrapCalldata 0x1000))

-- NORMAL FORWARD control: an ordinary in-bounds forward tail (no wrap) decodes to
-- the same bytes via the naive path (the wrap is never consulted here).
-- Layout: [offset_a=0x20][arr len=1][relOffset=0x20][target len=2][data].
#guard firstElemBytesEq
  (decodeValueAt? true
    (w32 0x20 ++ w32 0x01 ++ w32 0x20 ++ w32 0x02
      ++ w32 0xaabb000000000000000000000000000000000000000000000000000000000000)
    0 (Ty.dynamicArray Ty.bytesCalldata))
  [0xaa, 0xbb]

/-- Preserved eager-path malformed control (#128): a `bytes[] memory` (eager,
    `lazy = false`) with a truncated element-head area reverts EMPTY, not Panic —
    the wrap change never touches the eager path. -/
def isEmptyRevert {α} : Except RevertData α -> Bool
  | Except.error RevertData.empty => true
  | _ => false

#guard isEmptyRevert
  (decodeValueAt? false
    (w32 0x20 ++ w32 3 ++ w32 0x20 ++ w32 (2 ^ 64)) 0
    (Ty.dynamicArray Ty.bytesCalldata))

/-- Eager positive control: a well-formed `uint[] memory` still decodes (no
    over-reject introduced by WS3). -/
def isDecodeOk {α} : Except RevertData α -> Bool
  | Except.ok _ => true
  | _ => false

#guard isDecodeOk
  (decodeValueAt? false (w32 0x20 ++ w32 1 ++ w32 42) 0 (Ty.dynamicArray Ty.uint256))

end CalldataEvmWrap
end Source
end Solidity
end SolidCore
