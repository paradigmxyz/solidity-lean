import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
RIPEMD-BYTES20-TO-BYTES32-RETURN (S, implicit-bytes20-to-bytes32-return, wrong-value):
`ripemd160("")` is `bytes20`; returned directly from a `returns (bytes32)` function
it is IMPLICITLY widened `bytes20 -> bytes32`. Because `bytesN` is left-aligned, solc
inserts `convert_t_bytesM_to_t_bytesN` which moves the 20-byte digest into the HIGH
bytes:

  function f() external pure returns (bytes32) { return ripemd160(""); }
  // solc+EVM: 0x9c1185a5c5e9fc54612808977ee8f548b2258d31000000000000000000000000
  //           (digest left-aligned, i.e. digest << 96)

solidity-lean lowered the target-typed `ripemd160` env-aware WITHOUT the implicit
widening cast, so the digest stayed right-aligned in the returned word
(0x0000..0000 9c11..8d31 = digest) -> wrong value. The fix routes the env-aware
`ripemd160` arm through the same `coreAsFromTy?` widening the generic Direct path
uses, restoring the `fixedBytesCast 32 20` that left-aligns the digest.

`ripemd160(...)` returned at its natural `bytes20` width is a value no-op (no
widening), so `g` below is the identity control.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace RipemdBytes20ToBytes32Return

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def ret (e : Expr) : Stmt := Stmt.returnValues (some e)

private def fn (name : String) (rt : Ty) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some name,
      visibility := some Visibility.external_,
      mutability := StateMutability.pure,
      params := [],
      returns := [{ name := none, ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def ripemdEmpty : Expr :=
  Expr.call (Expr.ident "ripemd160") [Arg.positional (Expr.literal (Literal.bytes []))]

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "T", abstract := false,
    bases := [],
    items :=
      [ -- The exact submission: implicit bytes20 -> bytes32 widening return.
        fn "f" (Ty.bytesN 32) [ ret ripemdEmpty ]
        -- Control: returned at its natural bytes20 width (no widening).
      , fn "g" (Ty.bytesN 20) [ ret ripemdEmpty ] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- RIPEMD-160("") = 0x9c1185a5c5e9fc54612808977ee8f548b2258d31 (20 bytes).
-- As bytes32 (left-aligned) the 20-byte digest sits in the HIGH bytes.
def f_result : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "f" State.empty []
    0x9c1185a5c5e9fc54612808977ee8f548b2258d31000000000000000000000000
-- bytes20 return: the digest at its natural (right-aligned) width, unchanged.
def g_result : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "g" State.empty []
    0x9c1185a5c5e9fc54612808977ee8f548b2258d31

#eval accepted
#eval f_result
#eval g_result

#guard accepted
#guard isOkTrue f_result
#guard isOkTrue g_result

end RipemdBytes20ToBytes32Return
end Witness
end Solidity
end SolidCore
