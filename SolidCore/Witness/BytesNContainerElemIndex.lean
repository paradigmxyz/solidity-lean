import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BYTESN-CONTAINER-ELEM-INDEX — indexing a `bytesN` value that is ITSELF the
result of a CONTAINER element / struct-member load.

`bytes4[] memory a = new bytes4[](1); a[0] = 0x11223344; return a[0][0];`
must return `0x11` (solc+EVM). solidity-lean reverted `panic:0`: a container
element/member load produces a plain `Value.word` (no width tag), so the
subsequent index consumer dead-ended in `RevertData.typeMismatch` (Panic 0) —
the value-typing gap `VALUE_TYPING_DESIGN.md` describes.

Companion to `BytesNIdentIndex` (bare-ident base). The trigger here is exactly
that the `bytesN` operand of the index is a container element/member load
rather than a bound identifier value.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesNContainerElemIndex

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

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

private def bytes1Ty : Ty := Ty.bytesN 1

private def num (s : String) : Expr := Expr.literal (Literal.number s)

-- memory bytes4[]: a[0] = 0x11223344; return a[0][0]  → 0x11
private def fMemBody : List Stmt :=
  [ Stmt.varDecl
      [{ name := some "a", ty := some (Ty.array (Ty.bytesN 4) none),
         location := some DataLocation.memory }]
      (some (Expr.newExpr (Ty.array (Ty.bytesN 4) none)
        [Arg.positional (num "1")]))
  , Stmt.expr (Expr.assign (Expr.index (Expr.ident "a") (num "0"))
      AssignOp.assign (num "0x11223344"))
  , ret (Expr.index (Expr.index (Expr.ident "a") (num "0")) (num "0")) ]

-- storage struct member: s.b = 0x11223344; return s.b[0]  → 0x11
private def structDecl : ContractItem :=
  ContractItem.structDecl
    { name := "S", fields := [{ name := "b", ty := Ty.bytesN 4 }] }

private def fStructBody : List Stmt :=
  [ Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "b")
      AssignOp.assign (num "0x11223344"))
  , ret (Expr.index (Expr.member (Expr.ident "s") "b") (num "0")) ]

-- storage fixed array bytes4[2]: sfa[0] = 0x11223344; return sfa[0][1]  → 0x22
private def fStorArrBody : List Stmt :=
  [ Stmt.expr (Expr.assign (Expr.index (Expr.ident "sfa") (num "0"))
      AssignOp.assign (num "0x11223344"))
  , ret (Expr.index (Expr.index (Expr.ident "sfa") (num "0")) (num "1")) ]

-- storage mapping(uint256 => bytes4): m[1] = 0x11223344; return m[1][0]  → 0x11
private def fMapBody : List Stmt :=
  [ Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (num "1"))
      AssignOp.assign (num "0x11223344"))
  , ret (Expr.index (Expr.index (Expr.ident "m") (num "1")) (num "0")) ]

-- CONTROL (already agreed): bind to a local first, then index — ident arm.
private def fBoundBody : List Stmt :=
  [ Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "b")
      AssignOp.assign (num "0x11223344"))
  , Stmt.varDecl
      [{ name := some "t", ty := some (Ty.bytesN 4), location := none }]
      (some (Expr.member (Expr.ident "s") "b"))
  , ret (Expr.index (Expr.ident "t") (num "0")) ]

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "BytesNContainerElemIndex",
    abstract := false, bases := [],
    items :=
      [ structDecl
      , ContractItem.stateVar { name := "s", ty := Ty.user { segments := ["S"] } }
      , ContractItem.stateVar { name := "sfa", ty := Ty.array (Ty.bytesN 4) (some 2) }
      , ContractItem.stateVar { name := "m", ty := Ty.mapping (Ty.uint 256) (Ty.bytesN 4) }
      , fn "fMem" [] bytes1Ty StateMutability.pure fMemBody
      , fn "fStruct" [] bytes1Ty StateMutability.nonpayable fStructBody
      , fn "fStorArr" [] bytes1Ty StateMutability.nonpayable fStorArrBody
      , fn "fMap" [] bytes1Ty StateMutability.nonpayable fMapBody
      , fn "fBound" [] bytes1Ty StateMutability.nonpayable fBoundBody ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

def fMem_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fMem" State.empty [] 0x11

def fStruct_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fStruct" State.empty [] 0x11

def fStorArr_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fStorArr" State.empty [] 0x22

def fMap_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fMap" State.empty [] 0x11

def fBound_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fBound" State.empty [] 0x11

#guard accepted
#guard isOkTrue fMem_0
#guard isOkTrue fStruct_0
#guard isOkTrue fStorArr_1
#guard isOkTrue fMap_0
#guard isOkTrue fBound_0

end BytesNContainerElemIndex
end Witness
end Solidity
end SolidCore
