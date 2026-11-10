import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for the type of .length on a fixed-size bytesN value.

solc types x.length of a bytesN value as uint8 (FixedBytesType native
member), so for bytes32 x the expression x.length * 8 is checked uint8
arithmetic: 32 * 8 overflows and reverts with Panic(0x11), and the explicit
conversion int8(bytes3(..).length) is legal and yields 3. The model typed
it as uint256, returning 256 and rejecting the conversion. Controls: a
non-overflowing bytes2 length, an unchecked wrap to 0, uint8 and uint256 locals, a length of an internal call result, and a
dynamic bytes length that stays uint256.
-/

namespace SolidCore.Solidity.Witness.FixedBytesLengthUint8

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the contract below (imported AST):

    contract C {
        function bits(bytes32 x) external pure returns (uint256) {
            return x.length * 8;
        }
        function bitsUnchecked(bytes32 x) external pure returns (uint256) {
            unchecked {
                return x.length * 8;
            }
        }
        function bitsSmall(bytes2 y) external pure returns (uint256) {
            return y.length * 8;
        }
        function lengthLocal(bytes32 x) external pure returns (uint8) {
            uint8 n = x.length;
            return n;
        }
        function lengthWideLocal(bytes32 x) external pure returns (uint256) {
            uint256 n = x.length;
            return n;
        }
        function four() internal pure returns (bytes4) {
            return 0x01020304;
        }
        function callBaseLength() external pure returns (uint256) {
            uint256 n = four().length;
            return n;
        }
        function signedConversion() external pure returns (int8) {
            return int8(bytes3(0x915b42).length);
        }
        function dynamicBytesControl() external pure returns (uint256) {
            bytes memory b = new bytes(32);
            return b.length * 8;
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
    name := some "bits",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "x") "length") (Expr.literal (Literal.number "8"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bitsUnchecked",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "x") "length") (Expr.literal (Literal.number "8"))))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bitsSmall",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "y", ty := Ty.bytesN 2, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "y") "length") (Expr.literal (Literal.number "8"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lengthLocal",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.uint 8, location := none }] (some (Expr.member (Expr.ident "x") "length")), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lengthWideLocal",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.uint 256, location := none }] (some (Expr.member (Expr.ident "x") "length")), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "four",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "0x01020304")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callBaseLength",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.uint 256, location := none }] (some (Expr.member (Expr.call (Expr.ident "four") []) "length")), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "signedConversion",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.int 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.int 8)) [Arg.positional (Expr.member (Expr.call (Expr.typeName (Ty.bytesN 3)) [Arg.positional (Expr.literal (Literal.number "0x915b42"))]) "length")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "dynamicBytesControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "b", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.newExpr (Ty.bytes) [Arg.positional (Expr.literal (Literal.number "32"))])), Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "b") "length") (Expr.literal (Literal.number "8"))))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- bits
def bytes32_length_times_8_panics : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract "bits" State.empty [Value.fixedBytes 32 5]
    0x11

-- bitsUnchecked
def unchecked_wraps : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "bitsUnchecked" State.empty [Value.fixedBytes 32 5]
    0

-- bitsSmall
def bytes2_length_times_8 : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "bitsSmall" State.empty [Value.fixedBytes 2 5]
    16

-- lengthLocal
def uint8_local : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "lengthLocal" State.empty [Value.fixedBytes 32 5]
    32

-- lengthWideLocal
def uint256_local : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "lengthWideLocal" State.empty [Value.fixedBytes 32 5]
    32

-- callBaseLength
def call_base_length : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "callBaseLength" State.empty []
    4

-- signedConversion
def signed_conversion : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallIntMatches 1024 contract "signedConversion" State.empty []
    3

-- dynamicBytesControl
def dynamic_bytes_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "dynamicBytesControl" State.empty []
    256

#guard accepted
#guard ok bytes32_length_times_8_panics
#guard ok unchecked_wraps
#guard ok bytes2_length_times_8
#guard ok uint8_local
#guard ok uint256_local
#guard ok call_base_length
#guard ok signed_conversion
#guard ok dynamic_bytes_control

end SolidCore.Solidity.Witness.FixedBytesLengthUint8
