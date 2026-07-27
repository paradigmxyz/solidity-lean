import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BYTESN-LENGTH-MEMBER (soundness gap): the `.length` member of a `bytesN` value
must return the constant width `N` (solc folds `bytesN.length` to `N`).

  bytes4 b = 0x11223344; return b.length;   // solc+EVM: 4

solidity-lean reverted Panic(0): the runtime member read routes through
`Expr.length` -> `Value.length?`, and `Value.length?` had no `Value.fixedBytes`
case (VALUE_TYPING_DESIGN left it "explicit no" when the width tag was added),
so a non-constant `bytesN` operand (local / param / ternary result — all carry
their width in the `fixedBytes` tag) dead-ended in `RevertData.typeMismatch`.
The compile-time-constant shapes (`bytes4(0x11223344).length`,
`keccak256("x").length`) already agreed because solc/lean fold them before the
runtime read. Fix: `Value.length?` on `Value.fixedBytes size _` yields `size`.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesNLengthMember

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256

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

private def len (base : Expr) : Expr := Expr.member base "length"

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "BytesNLengthMember", abstract := false,
    bases := [],
    items :=
      [ -- The exact submission: a plain `bytes4` local.
        fn "f" [] u256 StateMutability.pure
          [ Stmt.varDecl
              [{ name := some "b", ty := some (Ty.bytesN 4) }]
              (some (Expr.literal (Literal.number "0x11223344")))
          , ret (len (Expr.ident "b")) ]
        -- A `bytes32` function PARAMETER.
      , fn "f32" [param "a" (Ty.bytesN 32)] u256 StateMutability.pure
          [ret (len (Expr.ident "a"))]
        -- A `bytes4` function PARAMETER.
      , fn "fParam" [param "a" (Ty.bytesN 4)] u256 StateMutability.pure
          [ret (len (Expr.ident "a"))]
        -- A ternary result of two `bytes4` params.
      , fn "fTernary" [param "c" Ty.bool, param "a" (Ty.bytesN 4),
          param "b" (Ty.bytesN 4)] u256 StateMutability.pure
          [ret (len (Expr.ternary (Expr.ident "c") (Expr.ident "a") (Expr.ident "b")))] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- The submission: `bytes4 b = 0x11223344; b.length` == 4.
def f_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "f" State.empty [] 4
def f32_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "f32" State.empty
    [Value.word 0x11223344] 32
def fParam_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fParam" State.empty
    [Value.word 0x11223344] 4
-- Ternary result of two bytes4 operands -> width 4 either way.
def fTernary_true : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fTernary" State.empty
    [Value.word 1, Value.word 0x11223344, Value.word 0] 4
def fTernary_false : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "fTernary" State.empty
    [Value.word 0, Value.word 0x11223344, Value.word 0] 4

#eval accepted
#eval f_len
#eval fTernary_true
#eval fTernary_false

#guard accepted
#guard isOkTrue f_len
#guard isOkTrue f32_len
#guard isOkTrue fParam_len
#guard isOkTrue fTernary_true
#guard isOkTrue fTernary_false

end BytesNLengthMember
end Witness
end Solidity
end SolidCore
