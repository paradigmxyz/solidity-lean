import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-BYTESN-SHL (S, bytesn-left-shift-result-used-directly-as-encoder-argument):
a LEFT shift of a `bytesN` (N < 32) used DIRECTLY as an `abi.encode` argument
reverts Panic(0) where solc+EVM return the left-aligned shifted value.

  bytes4 b = 0x11223344; return abi.encode(b << 8);   // solc+EVM: 0x22334400 (left-aligned)

solidity-lean reverts Panic(0). Binding the shift result to a `bytesN` local first
(`bytes4 r = b << 8; abi.encode(r)`) AGREES, so the defect is in the direct
encoder-argument lowering path.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeBytesNShl

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def bytesMem : Ty := Ty.bytes

private def ret (e : Expr) : Stmt := Stmt.returnValues (some e)

private def fn (name : String) (params : List Parameter) (rt : Ty)
    (loc : Option DataLocation) (mutb : StateMutability) (body : List Stmt) :
    ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some name,
      visibility := some Visibility.external_,
      mutability := mutb,
      params := params,
      returns := [{ name := none, ty := rt, location := loc }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y
private def shr (x y : Expr) : Expr := Expr.binary BinaryOp.shr x y
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def param (nm : String) (ty : Ty) : Parameter :=
  { name := some nm, ty := ty, location := none }

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "C", abstract := false,
    bases := [],
    items :=
      [ -- The exact submission: `abi.encode(b << 8)`, `bytes4 b = 0x11223344`.
        fn "f" [] bytesMem (some DataLocation.memory) StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 4) }]
              (some (lit "0x11223344"))
          , ret (abiEncode [Arg.positional (shl (Expr.ident "b") (lit "8"))]) ]
        -- Control: bind the shift result first, then encode.
      , fn "fBound" [] bytesMem (some DataLocation.memory) StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 4) }]
              (some (lit "0x11223344"))
          , Stmt.varDecl
              [{ name := some "r", ty := some (Ty.bytesN 4) }]
              (some (shl (Expr.ident "b") (lit "8")))
          , ret (abiEncode [Arg.positional (Expr.ident "r")]) ]
        -- Control: RIGHT shift, same operand/position, must agree already.
      , fn "fShr" [] bytesMem (some DataLocation.memory) StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 4) }]
              (some (lit "0x11223344"))
          , ret (abiEncode [Arg.positional (shr (Expr.ident "b") (lit "8"))]) ]
        -- bytes1 left shift: 0x11 << 4 = 0x10 (lane-masked).
      , fn "fB1" [] bytesMem (some DataLocation.memory) StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 1) }]
              (some (lit "0x11"))
          , ret (abiEncode [Arg.positional (shl (Expr.ident "b") (lit "4"))]) ]
        -- Variable shift amount, producer is a PARAMETER: `a << n`.
      , fn "fVar" [param "a" (Ty.bytesN 4), param "n" (Ty.uint 8)]
          bytesMem (some DataLocation.memory) StateMutability.pure
          [ ret (abiEncode [Arg.positional (shl (Expr.ident "a") (Expr.ident "n"))]) ]
        -- Shift BEYOND the width: `b << 32` truncates the 4-byte lane to 0.
      , fn "fBeyond" [] bytesMem (some DataLocation.memory) StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 4) }]
              (some (lit "0x11223344"))
          , ret (abiEncode [Arg.positional (shl (Expr.ident "b") (lit "32"))]) ] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- abi.encode(bytesN) is a single 32-byte word, LEFT-aligned (high bytes).
private def leftAligned (bytes : List Nat) : List Nat :=
  bytes ++ List.replicate (32 - bytes.length) 0

def f_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "f" State.empty []
    (leftAligned [0x22, 0x33, 0x44, 0x00])
def fBound_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "fBound" State.empty []
    (leftAligned [0x22, 0x33, 0x44, 0x00])
def fShr_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "fShr" State.empty []
    (leftAligned [0x00, 0x11, 0x22, 0x33])
def fB1_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "fB1" State.empty []
    (leftAligned [0x10])
def fVar_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "fVar" State.empty
    [Value.fixedBytes 4 0x11223344, Value.word 8]
    (leftAligned [0x22, 0x33, 0x44, 0x00])
def fBeyond_result : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 contract "fBeyond" State.empty []
    (leftAligned [0x00, 0x00, 0x00, 0x00])

#eval accepted
#eval f_result
#eval fBound_result
#eval fShr_result
#eval fB1_result
#eval fVar_result
#eval fBeyond_result

#guard accepted
#guard isOkTrue f_result
#guard isOkTrue fBound_result
#guard isOkTrue fShr_result
#guard isOkTrue fB1_result
#guard isOkTrue fVar_result
#guard isOkTrue fBeyond_result

end AbiEncodeBytesNShl
end Witness
end Solidity
end SolidCore
