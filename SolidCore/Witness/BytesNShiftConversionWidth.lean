import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for a conversion of a fixed-bytes shift result to another width.

The shift runs at the operand's own width and the result is converted
afterwards: bytes2(0x1234) >> 4 is the bytes2 value 0x0123, so
bytes32(bytes2(0x1234) >> 4) is 0x0123 followed by zero bytes. The bytesN
shift/bitwise lowering walked the operand at the conversion's target width,
widening the leaves before the shift, so the bits shifted below the 2-byte
lane survived (0x01234000...). Covers widening (bytes32, bytes16 via a
local), narrowing (bytes1), left shift, complement, an ABI-encoded widening, the same-width conversion, and the
already-correct shift through a bytes2 local as a control.
-/

namespace SolidCore.Solidity.Witness.BytesNShiftConversionWidth

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the contract below (imported AST):

    contract C {
        function widenShr(uint256 c) external pure returns (bytes32) {
            return bytes32(bytes2(0x1234) >> c);
        }
        function widenShr7(uint256 c) external pure returns (bytes32) {
            return bytes32(bytes7(0x11223344556677) >> c);
        }
        function widenShrLocal(uint256 c) external pure returns (bytes32) {
            bytes32 r = bytes16(bytes2(0x1234) >> c);
            return r;
        }
        function widenShl(uint256 c) external pure returns (bytes32) {
            return bytes32(bytes2(0x1234) << c);
        }
        function widenNot() external pure returns (bytes32) {
            return bytes32(~bytes2(0x1234));
        }
        function widenShrEncode(uint256 c) external pure returns (bytes memory) {
            return abi.encode(bytes32(bytes2(0x1234) >> c));
        }
        function narrowShr(uint256 c) external pure returns (bytes1) {
            return bytes1(bytes2(0x1234) >> c);
        }
        function sameWidthShr(uint256 c) external pure returns (bytes2) {
            return bytes2(bytes2(0x1234) >> c);
        }
        function viaLocalControl(uint256 c) external pure returns (bytes32) {
            bytes2 t = bytes2(0x1234) >> c;
            return bytes32(t);
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
    name := some "widenShr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenShr7",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 7)) [Arg.positional (Expr.literal (Literal.number "0x11223344556677"))]) (Expr.ident "c"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenShrLocal",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "r", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 16)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))])), Stmt.returnValues (some (Expr.ident "r"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenShl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenNot",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenShrEncode",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "narrowShr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sameWidthShr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 2, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "viaLocalControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "t", ty := Ty.bytesN 2, location := none }] (some (Expr.binary BinaryOp.shr (Expr.call (Expr.typeName (Ty.bytesN 2)) [Arg.positional (Expr.literal (Literal.number "0x1234"))]) (Expr.ident "c"))), Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.ident "t")]))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- widenShr
def widen_shr_discards_low_bits : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "widenShr" State.empty [Value.word 4]
    (0x0123 * 2 ^ 240)

-- widenShr7
def widen_shr7_discards_low_bits : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "widenShr7" State.empty [Value.word 8]
    (0x00112233445566 * 2 ^ 200)

-- widenShrLocal
def widen_shr_bytes16_local : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "widenShrLocal" State.empty [Value.word 4]
    (0x0123 * 2 ^ 240)

-- widenShl
def widen_shl : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "widenShl" State.empty [Value.word 4]
    (0x2340 * 2 ^ 240)

-- widenNot
def widen_bitnot : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "widenNot" State.empty []
    (0xedcb * 2 ^ 240)

-- widenShrEncode
def widen_shr_encode : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 1024 contract "widenShrEncode" State.empty [Value.word 4]
    ([0x01, 0x23] ++ List.replicate 30 0)

-- narrowShr
def narrow_shr : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "narrowShr" State.empty [Value.word 4]
    0x01

-- sameWidthShr
def same_width_shr : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "sameWidthShr" State.empty [Value.word 4]
    0x0123

-- viaLocalControl
def via_local_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "viaLocalControl" State.empty [Value.word 4]
    (0x0123 * 2 ^ 240)

#guard accepted
#guard ok widen_shr_discards_low_bits
#guard ok widen_shr7_discards_low_bits
#guard ok widen_shr_bytes16_local
#guard ok widen_shl
#guard ok widen_bitnot
#guard ok widen_shr_encode
#guard ok narrow_shr
#guard ok same_width_shr
#guard ok via_local_control

end SolidCore.Solidity.Witness.BytesNShiftConversionWidth
