import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A widening conversion around an assignment-target mapping key keeps the
operand-width cleanup of the narrow expression it wraps. With int8 x =
94, m[int256(x << 4)] = 5 shifts at int8 (1504 wraps to -32) and then
widens, so the store lands on key -32. With uint32 x = 2^32-1,
u[uint256(x << 1)] stores under 0xfffffffe, not 0x1fffffffe; the same
holds for ~x, for the constant type(uint32).max << uint8(1), for a
struct-member target and for a compound assignment, and unchecked uint8
addition wraps to key 44 while checked addition panics 0x11. The store
side used to lower such a wide key env-less, so the shift ran at 256
bits and the store hit the wrong slot. Controls: the same key as an
rvalue, and a uint256 operand that does not wrap.
-/

namespace SolidCore.Solidity.Witness.LValueKeyNarrowShiftWiden

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the contract below (imported AST):

    contract C {
        struct S { uint256 f4; }
        mapping(int256 => uint256) m;
        mapping(uint256 => uint256) u;
        mapping(uint256 => S) ms;
        function signedShl(int8 x) external returns (uint256) {
            m[int256(x << 4)] = 5;
            return m[-32];
        }
        function unsignedShl(uint32 x) external returns (uint256) {
            u[uint256(x << 1)] = 5;
            return u[4294967294];
        }
        function bitNot(uint8 x) external returns (uint256) {
            u[uint256(~x)] = 6;
            return u[254];
        }
        function constShl() external returns (uint256) {
            ms[uint256(type(uint32).max << uint8(1))].f4 = 7;
            return ms[4294967294].f4;
        }
        function nestedShl(uint32 x) external returns (uint256) {
            ms[uint256(x << 1)].f4 = 8;
            return ms[4294967294].f4;
        }
        function compoundShl(uint32 x) external returns (uint256) {
            u[uint256(x << 1)] += 9;
            return u[4294967294];
        }
        function readControl(int8 x) external returns (uint256) {
            m[-32] = 3;
            return m[int256(x << 4)];
        }
        function wideControl(uint256 x) external returns (uint256) {
            u[uint256(x << 1)] = 4;
            return u[8589934590];
        }
        function uncheckedAdd(uint8 x) external returns (uint256) {
            unchecked { u[uint256(x + 100)] = 10; }
            return u[44];
        }
        function checkedAdd(uint8 x) external returns (uint256) {
            u[uint256(x + 100)] = 11;
            return u[300];
        }
    }
-/
def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "f4", ty := Ty.uint 256 }] }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.int 256) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "u",
    ty := Ty.mapping (Ty.uint 256) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "ms",
    ty := Ty.mapping (Ty.uint 256) (Ty.user ({ segments := ["S"] })),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "signedShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.int 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "4")))])) AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "32")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "unsignedShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "1")))])) AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "4294967294"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bitNot",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.ident "x"))])) AssignOp.assign (Expr.literal (Literal.number "6"))), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "254"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "constShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "ms") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.member (Expr.typeName (Ty.uint 32)) "max") (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))]))])) "f4") AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "ms") (Expr.literal (Literal.number "4294967294"))) "f4"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestedShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "ms") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "1")))])) "f4") AssignOp.assign (Expr.literal (Literal.number "8"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "ms") (Expr.literal (Literal.number "4294967294"))) "f4"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "compoundShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "1")))])) AssignOp.addAssign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "4294967294"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "readControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.int 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "32")))) AssignOp.assign (Expr.literal (Literal.number "3"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "4")))])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "wideControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "1")))])) AssignOp.assign (Expr.literal (Literal.number "4"))), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "8589934590"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "uncheckedAdd",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))])) AssignOp.assign (Expr.literal (Literal.number "10")))]), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "44"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "checkedAdd",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "u") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))])) AssignOp.assign (Expr.literal (Literal.number "11"))), Stmt.returnValues (some (Expr.index (Expr.ident "u") (Expr.literal (Literal.number "300"))))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- signedShl
def signed_shl_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "signedShl" State.empty [Value.word 94]
    5

-- unsignedShl
def unsigned_shl_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "unsignedShl" State.empty [Value.word 4294967295]
    5

-- bitNot
def bitnot_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "bitNot" State.empty [Value.word 1]
    6

-- constShl
def const_shl_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "constShl" State.empty []
    7

-- nestedShl
def member_target_shl_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "nestedShl" State.empty [Value.word 4294967295]
    8

-- compoundShl
def compound_shl_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "compoundShl" State.empty [Value.word 4294967295]
    9

-- uncheckedAdd
def unchecked_add_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "uncheckedAdd" State.empty [Value.word 200]
    10

-- checkedAdd
def checked_add_panics : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract "checkedAdd" State.empty [Value.word 200]
    0x11

-- readControl
def read_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "readControl" State.empty [Value.word 94]
    3

-- wideControl
def wide_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "wideControl" State.empty [Value.word 4294967295]
    4

#guard accepted
#guard ok signed_shl_wraps
#guard ok unsigned_shl_wraps
#guard ok bitnot_wraps
#guard ok const_shl_wraps
#guard ok member_target_shl_wraps
#guard ok compound_shl_wraps
#guard ok unchecked_add_wraps
#guard ok checked_add_panics
#guard ok read_control
#guard ok wide_control

end SolidCore.Solidity.Witness.LValueKeyNarrowShiftWiden
