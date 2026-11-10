import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for constant folding through a narrowing integer conversion.

An explicit integer conversion of a constant keeps the constant only when it
fits the target range. uint8(uint16(0x1234)) truncates at run time to 0x34,
so uint256(uint8(uint16(0x1234))) is 52 and uint8(1) | uint8(uint16(0x1234))
is 0x35. The constant folder used to look straight through every T(x)
conversion, so the outer conversion or the bitwise operator folded the
untruncated 0x1234. Controls: a fitting inner constant still folds, and a
checked narrow overflow of typed constants still panics.
-/

namespace SolidCore.Solidity.Witness.ConstNarrowConversionFold

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the contract below (imported AST):

    contract C {
        function orNarrow() external pure returns (uint256) {
            return uint256(uint8(1) | uint8(uint16(0x1234)));
        }
        function xorNarrow() external pure returns (uint256) {
            return uint256(uint8(1) ^ uint8(uint16(0x1234)));
        }
        function nested() external pure returns (uint256) {
            return uint256(uint8(uint16(0x1234)));
        }
        function nestedSigned() external pure returns (int256) {
            return int256(int8(int16(0x1280)));
        }
        function nestedPlusOne() external pure returns (uint256) {
            return uint256(uint8(uint16(0x1234))) + 1;
        }
        function fitsControl() external pure returns (uint256) {
            return uint256(uint8(1) | uint8(uint16(0x34)));
        }
        function narrowOverflowControl() external pure returns (uint256) {
            return uint256(uint8(200) + uint8(100));
        }
    }
-/
def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "orNarrow",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.bitOr (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))]) (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])]))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "xorNarrow",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.bitXor (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))]) (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])]))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestedSigned",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.int 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional (Expr.call (Expr.typeName (Ty.int 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.int 16)) [Arg.positional (Expr.literal (Literal.number "0x1280"))])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestedPlusOne",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])])]) (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "fitsControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.bitOr (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))]) (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.literal (Literal.number "0x34"))])]))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "narrowOverflowControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.add (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "200"))]) (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "100"))]))]))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- orNarrow
def or_narrow_truncates : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "orNarrow" State.empty []
    0x35

-- xorNarrow
def xor_narrow_truncates : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "xorNarrow" State.empty []
    0x35

-- nested
def nested_truncates : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "nested" State.empty []
    0x34

-- nestedSigned
def nested_signed_truncates : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallIntMatches 1024 contract "nestedSigned" State.empty []
    (SolidCore.Solidity.Shared.signedToWord (-128))

-- nestedPlusOne
def nested_plus_one : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "nestedPlusOne" State.empty []
    0x35

-- fitsControl
def fitting_constant_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "fitsControl" State.empty []
    0x35

-- narrowOverflowControl
def narrow_overflow_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract "narrowOverflowControl" State.empty []
    0x11

#guard accepted
#guard ok or_narrow_truncates
#guard ok xor_narrow_truncates
#guard ok nested_truncates
#guard ok nested_signed_truncates
#guard ok nested_plus_one
#guard ok fitting_constant_control
#guard ok narrow_overflow_control

end SolidCore.Solidity.Witness.ConstNarrowConversionFold
