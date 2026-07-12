import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BYTESN-EQ-LITERAL (#180) — `==`/`!=` between a `bytesN` value and a BARE
string/hex literal.

solc 0.8.35 accepts these: the string/hex literal is implicitly converted to the
`bytesN` operand's value type and compared as a value type. The model was
over-rejecting at typecheck because the equality-comparability guard checked the
operands' RAW inferred types — a bare `hex"…"`/`"…"` literal is typed dynamic
`Ty.bytes`/`Ty.string`, neither of which is equality-comparable — instead of the
common (converted) `bytesN` value type. The fix (TypeCheck.lean, `eq`/`ne` arm)
lets the guard pass when one operand is a literal that `implicitLiteralFits` the
OTHER operand's equality-comparable type.

Probed against pinned solc 0.8.35 + anvil (contract C below, deployed):
  a(bytes4 x) = (x == "abcd"):   "abcd" → bytes4 0x61626364
                a(0x61626364) = true,  a(0) = false
  b(bytes4 x) = (x != hex"1234"): hex"1234" → bytes4 0x12340000
                b(0x12340000) = false, b(0) = true
  c(bytes32 x) = (x == hex"00"): hex"00" → bytes32 0x00…00 = 0
                c(0) = true,  c(1) = false

MUST STILL REJECT (no over-accept): `bytes memory x == "abcd"` — dynamic `bytes`
has no builtin `==`; solc AND model reject it. `rejectAccepted` below is `false`.

A `bytesN` value is carried in the LOW N bytes of the model word, so `bytes4
0x61626364` is the plain word 0x61626364; a `bool` return is word 1 (true) / 0
(false).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesNEqLiteral

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def ret (e : Expr) : Stmt := Stmt.returnValues (some e)

private def fn (name : String) (params : List Parameter) (rt : Ty)
    (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some name,
      visibility := some Visibility.external_, mutability := StateMutability.pure,
      params := params, returns := [{ name := none, ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def param (name : String) (ty : Ty) : Parameter :=
  { name := some name, ty := ty, location := none }

private def strLit (s : String) : Expr := Expr.literal (Literal.string s)
private def hexLit (s : String) : Expr := Expr.literal (Literal.hexString s)

-- Contract under test: bytesN operand `==`/`!=`/`<`/`&` a bare string/hex literal.
def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "C", abstract := false, bases := [],
    items :=
    [ -- #180: bytes4 == string literal
      fn "a" [param "x" (Ty.bytesN 4)] Ty.bool
        [ret (Expr.binary BinaryOp.eq (Expr.ident "x") (strLit "abcd"))]
      -- #180: bytes4 != hex literal
    , fn "b" [param "x" (Ty.bytesN 4)] Ty.bool
        [ret (Expr.binary BinaryOp.ne (Expr.ident "x") (hexLit "1234"))]
      -- #180: bytes32 == shorter hex literal
    , fn "c" [param "x" (Ty.bytesN 32)] Ty.bool
        [ret (Expr.binary BinaryOp.eq (Expr.ident "x") (hexLit "00"))]
      -- pre-existing acceptance (ordered comparison) — must stay accepted
    , fn "d" [param "x" (Ty.bytesN 4)] Ty.bool
        [ret (Expr.binary BinaryOp.lt (Expr.ident "x") (hexLit "1234"))]
      -- pre-existing acceptance (bitwise and) — must stay accepted
    , fn "e" [param "x" (Ty.bytesN 4)] (Ty.bytesN 4)
        [ret (Expr.binary BinaryOp.bitAnd (Expr.ident "x") (hexLit "1234"))] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

-- ACCEPTANCE: the whole contract now type-checks (the bug was typecheck-only).
def accepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit sourceUnit)

#guard accepted

-- Runtime values (bool return as word 1 = true / 0 = false).
def a_eq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "a" State.empty [Value.word 0x61626364] 0x01
def a_neq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "a" State.empty [Value.word 0] 0x00
def b_eq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "b" State.empty [Value.word 0x12340000] 0x00
def b_neq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "b" State.empty [Value.word 0] 0x01
def c_eq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "c" State.empty [Value.word 0] 0x01
def c_neq : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "c" State.empty [Value.word 1] 0x00

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard isOkTrue a_eq
#guard isOkTrue a_neq
#guard isOkTrue b_eq
#guard isOkTrue b_neq
#guard isOkTrue c_eq
#guard isOkTrue c_neq

-- NO OVER-ACCEPT REGRESSION: `bytes memory x == "abcd"` must STILL be rejected.
-- Dynamic `bytes` is not equality-comparable; solc (and the model) reject it.
def rejectContract : ContractDecl :=
  { kind := ContractKind.contract, name := "R", abstract := false, bases := [],
    items :=
    [ fn "m" [param "x" Ty.bytes] Ty.bool
        [ret (Expr.binary BinaryOp.eq (Expr.ident "x") (strLit "abcd"))] ] }

def rejectSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract rejectContract] }

def rejectAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit rejectSourceUnit)

#guard rejectAccepted = false

end BytesNEqLiteral
end Witness
end Solidity
end SolidCore
