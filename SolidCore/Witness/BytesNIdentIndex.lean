import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BYTESN-IDENT-INDEX (#175 local/param, #176 state var) — indexing a `bytesN`
value by a BARE IDENTIFIER base.

`a[i]` where `a` is a `bytesN` local, parameter, or state variable must extract
the `i`-th byte (solc returns `bytes1`), and on an out-of-range index (`i >= N`)
must Panic 0x32 (array out-of-bounds). Probed against pinned solc 0.8.35 + anvil:

  bytes32 a = 0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
  a[0] = 0x00, a[3] = 0x33, a[31] = 0xff, a[32] → Panic(0x32)
  bytes4  a = 0xaabbccdd:  a[0] = 0xaa, a[1] = 0xbb, a[4] → Panic(0x32)

The env-free `Expr.toCore?` ident-index arm could not see the identifier's type:
the local/param sub-branch emitted a generic `index` (→ `Value.index?` on a
`Value.word` → `RevertData.typeMismatch` = Panic 0x00) and the state-var
sub-branch emitted `storageIndex` on a scalar-layout slot (→ `typeMismatch` =
Panic 0x00). The fix runs in the type-directed `Expr.resolveStructsFuel` pre-pass
(which carries the full `TypeEnv` of state vars + params + locals): a bytesN
identifier base `name[i]` is rewritten to `bytesN(name)[i]`, so the already-
correct general (non-ident) index arm lowers it to `fixedBytesIndex`, which
returns the byte and Panics 0x32 on `i >= N`.

Real-EVM Forge ground truth: `tests/forge-harness/bytesn-ident-index`.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesNIdentIndex

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def bytes32Val : Nat :=
  0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff

-- bytes4 value 0xaabbccdd. In the model, a `bytesN` value carries its N
-- significant bytes in the LOW N bytes of the word (rendered big-endian by
-- `wordToBytesBE N`), so `bytes4 0xaabbccdd` is the plain word 0xaabbccdd:
-- byte 0 = 0xaa, byte 1 = 0xbb.
private def bytes4Val : Nat :=
  0xaabbccdd

private def ret (e : Expr) : Stmt := Stmt.returnValues (some e)

private def fn (name : String) (params : List Parameter) (rt : Ty)
    (mutb : StateMutability) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some name,
      visibility := some Visibility.external_,
      mutability := mutb,
      params := params,
      returns := [{ name := none, ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def param (name : String) (ty : Ty) : Parameter :=
  { name := some name, ty := ty, location := none }

private def bytes1Ty : Ty := Ty.bytesN 1

-- Contract under test. `b` is a top-level `bytes32` state variable (slot 0).
def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "BytesNIdentIndex", abstract := false,
    bases := [],
    items :=
      [ ContractItem.stateVar { name := "b", ty := Ty.bytesN 32 }
        -- #175 PARAM: bytes32 param indexed by a bare `i`.
      , fn "fParam" [param "a" (Ty.bytesN 32), param "i" (Ty.uint 256)]
          bytes1Ty StateMutability.pure
          [ret (Expr.index (Expr.ident "a") (Expr.ident "i"))]
        -- #175 PARAM: bytes4 param indexed by a bare `i`.
      , fn "fParam4" [param "a" (Ty.bytesN 4), param "i" (Ty.uint 256)]
          bytes1Ty StateMutability.pure
          [ret (Expr.index (Expr.ident "a") (Expr.ident "i"))]
        -- #175 LOCAL: bytes32 local indexed by a bare `i`.
      , fn "fLocal" [param "i" (Ty.uint 256)]
          bytes1Ty StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "a", ty := some (Ty.bytesN 32) }]
              (some (Expr.call (Expr.typeName (Ty.bytesN 32))
                [Arg.positional (Expr.literal
                  (Literal.number
                    "0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"))]))
          , ret (Expr.index (Expr.ident "a") (Expr.ident "i")) ]
        -- #176 STATE VAR: bytes32 state var indexed by a bare `i`.
      , fn "getByte" [param "i" (Ty.uint 256)]
          bytes1Ty StateMutability.view
          [ret (Expr.index (Expr.ident "b") (Expr.ident "i"))] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

-- ACCEPTANCE: the contract type-checks (all four indexing forms are accepted;
-- the bug was runtime-only).
def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- State whose slot 0 holds the bytes32 state variable `b`.
def stateWithB : CoreState :=
  SolidCore.Solidity.Source.State.empty.storeSlot 0 bytes32Val

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- #175 PARAM bytes32: a[0]=0x00, a[3]=0x33, a[31]=0xff.
def fParam_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam" State.empty
    [Value.word bytes32Val, Value.word 0] 0x00
def fParam_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam" State.empty
    [Value.word bytes32Val, Value.word 3] 0x33
def fParam_31 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam" State.empty
    [Value.word bytes32Val, Value.word 31] 0xff

-- #175 PARAM bytes32 OOB: a[32] → Panic 0x32.
def fParam_oob : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "fParam" State.empty
    [Value.word bytes32Val, Value.word 32] 0x32

-- #175 PARAM bytes4: a[0]=0xaa, a[1]=0xbb; a[4] → Panic 0x32.
def fParam4_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam4" State.empty
    [Value.word bytes4Val, Value.word 0] 0xaa
def fParam4_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam4" State.empty
    [Value.word bytes4Val, Value.word 1] 0xbb
def fParam4_oob : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "fParam4" State.empty
    [Value.word bytes4Val, Value.word 4] 0x32

-- #175 LOCAL bytes32: a[3]=0x33; a[32] → Panic 0x32.
def fLocal_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fLocal" State.empty
    [Value.word 3] 0x33
def fLocal_oob : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "fLocal" State.empty
    [Value.word 32] 0x32

-- #176 STATE VAR bytes32: b[0]=0x00, b[3]=0x33, b[31]=0xff; b[32] → Panic 0x32.
def getByte_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "getByte" stateWithB [Value.word 0] 0x00
def getByte_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "getByte" stateWithB [Value.word 3] 0x33
def getByte_31 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "getByte" stateWithB [Value.word 31] 0xff
def getByte_oob : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "getByte" stateWithB [Value.word 32] 0x32

#guard accepted

#guard isOkTrue fParam_0
#guard isOkTrue fParam_3
#guard isOkTrue fParam_31
#guard isOkTrue fParam_oob

#guard isOkTrue fParam4_0
#guard isOkTrue fParam4_1
#guard isOkTrue fParam4_oob

#guard isOkTrue fLocal_3
#guard isOkTrue fLocal_oob

#guard isOkTrue getByte_0
#guard isOkTrue getByte_3
#guard isOkTrue getByte_31
#guard isOkTrue getByte_oob

end BytesNIdentIndex
end Witness
end Solidity
end SolidCore
