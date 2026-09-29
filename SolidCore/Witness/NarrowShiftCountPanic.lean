import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A shift count keeps its own Solidity type. Therefore `a + b` for `uint8 a,b`
must overflow with Panic(0x11) before `x << (a + b)` is evaluated. This covers
ordinary integer shifts, fixed-bytes shifts, and compound shift assignment.
-/

namespace SolidCore.Solidity.Witness.NarrowShiftCountPanic

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def id (name : String) : Expr := Expr.ident name
private def num (value : String) : Expr := Expr.literal (Literal.number value)
private def cast (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]
private def add (x y : Expr) : Expr := Expr.binary BinaryOp.add x y
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y
private def count : Expr := add (id "a") (id "b")
private def params : List Parameter :=
  [{ name := some "a", ty := Ty.uint 8, location := none },
   { name := some "b", ty := Ty.uint 8, location := none }]

private def fn (name : String) (returnTy : Ty) (body : Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := params
      returns := [{ name := none, ty := returnTy, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some body }

private def wordShift : ContractItem :=
  fn "wordShift" (Ty.uint 256)
    (Stmt.block [Stmt.returnValues (some (shl (cast (Ty.uint 256) (num "1")) count))])

private def bytesShift : ContractItem :=
  fn "bytesShift" (Ty.bytesN 1)
    (Stmt.block [Stmt.returnValues
      (some (shl (cast (Ty.bytesN 1) (num "0xff")) count))])

private def compoundShift : ContractItem :=
  fn "compoundShift" (Ty.uint 256)
    (Stmt.block
      [ Stmt.varDecl [{ name := some "x", ty := some (Ty.uint 256), location := none }]
          (some (num "1"))
      , Stmt.expr (Expr.assign (id "x") AssignOp.shlAssign count)
      , Stmt.returnValues (some (id "x")) ])

-- Explicitly widening each add operand makes the count a uint256 expression;
-- 200 + 100 therefore succeeds, and an EVM shift by 300 yields zero.
private def wideCountExpr : Expr :=
  shl (cast (Ty.uint 256) (num "1"))
    (add (cast (Ty.uint 256) (id "a"))
      (cast (Ty.uint 256) (id "b")))

private def wideCount : ContractItem :=
  fn "wideCount" (Ty.uint 256)
    (Stmt.block [Stmt.returnValues (some wideCountExpr)])

private def typedConstantShift : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "typedConstantShift"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := []
      returns := [{ name := none, ty := Ty.uint 8, location := none }]
      body := some (Stmt.block [Stmt.returnValues (some
        (shl (cast (Ty.uint 8) (num "91"))
          (cast (Ty.uint 8) (num "8"))))]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items := [wordShift, bytesShift, compoundShift, wideCount,
      typedConstantShift] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def overflowArgs : List Value := [Value.word 200, Value.word 100]
private def safeArgs : List Value := [Value.word 2, Value.word 3]

private def word_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "wordShift" State.empty
    overflowArgs 17
private def bytes_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "bytesShift" State.empty
    overflowArgs 17
private def compound_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "compoundShift" State.empty
    overflowArgs 17
private def word_safe_is_32 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "wordShift" State.empty
    safeArgs 32
private def compound_safe_is_32 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "compoundShift" State.empty
    safeArgs 32
private def wide_overflow_count_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "wideCount" State.empty
    overflowArgs 0
private def typed_constant_shift_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "typedConstantShift" State.empty
    [] 0

private def ok : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard ok word_overflow_panics
#guard ok bytes_overflow_panics
#guard ok compound_overflow_panics
#guard ok word_safe_is_32
#guard ok compound_safe_is_32
#guard ok wide_overflow_count_is_0
#guard ok typed_constant_shift_is_0

end SolidCore.Solidity.Witness.NarrowShiftCountPanic
