import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
COMPOUND-ASSIGN-BYTESN-LITERAL (S, bare-literal-rhs-of-compound-bitwise-assign-on-bytesn):
a BARE (uncast) hex/string literal used as the RHS of a COMPOUND BITWISE assignment
(`|=`, `&=`, `^=`) on a `bytesN` LValue must take its `bytesN` type from the LValue.

  bytes4 b = 0x11223344;
  b |= hex"000000ff";     // solc+EVM: 0x112233ff
                          // solidity-lean: revert Panic(0)

The literal is not given the target's `bytesN` type at the compound-assign sink, so
it stays a dynamic byte-string value and the bitwise op has no enumerated case.

CONTROLS (agree with solc): `b |= bytes4(hex"000000ff")` (explicit cast) and
`b = b | hex"000000ff"` (non-compound form).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace CompoundAssignBytesNLiteral

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def b4 : Ty := Ty.bytesN 4
private def numLit (s : String) : Expr := Expr.literal (Literal.number s)
private def hexLit (s : String) : Expr := Expr.literal (Literal.hexString s)
private def id (n : String) : Expr := Expr.ident n
private def conv (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]

private def fn (name : String) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some name,
      visibility := some Visibility.external_,
      mutability := StateMutability.pure,
      params := [], returns := [{ name := none, ty := b4, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def declB : Stmt :=
  Stmt.varDecl [{ name := some "b", ty := some b4 }] (some (numLit "0x11223344"))

-- b |= hex"000000ff"; return b;   solc: 0x112233ff
private def fOr : ContractItem :=
  fn "fOr"
    [ declB
    , Stmt.expr (Expr.assign (id "b") AssignOp.bitOrAssign (hexLit "000000ff"))
    , Stmt.returnValues (some (id "b")) ]

-- b &= hex"00ffff00"; return b;   solc: 0x00223300
private def fAnd : ContractItem :=
  fn "fAnd"
    [ declB
    , Stmt.expr (Expr.assign (id "b") AssignOp.bitAndAssign (hexLit "00ffff00"))
    , Stmt.returnValues (some (id "b")) ]

-- b ^= hex"000000ff"; return b;   solc: 0x112233bb
private def fXor : ContractItem :=
  fn "fXor"
    [ declB
    , Stmt.expr (Expr.assign (id "b") AssignOp.bitXorAssign (hexLit "000000ff"))
    , Stmt.returnValues (some (id "b")) ]

-- CONTROL (agrees): explicit cast b |= bytes4(hex"000000ff").
private def fOrCast : ContractItem :=
  fn "fOrCast"
    [ declB
    , Stmt.expr (Expr.assign (id "b") AssignOp.bitOrAssign (conv b4 (hexLit "000000ff")))
    , Stmt.returnValues (some (id "b")) ]

-- CONTROL (agrees): non-compound form b = b | hex"000000ff".
private def fOrNonCompound : ContractItem :=
  fn "fOrNonCompound"
    [ declB
    , Stmt.expr (Expr.assign (id "b") AssignOp.assign
        (Expr.binary BinaryOp.bitOr (id "b") (hexLit "000000ff")))
    , Stmt.returnValues (some (id "b")) ]

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "C", abstract := false, bases := [],
    items := [ fOr, fAnd, fXor, fOrCast, fOrNonCompound ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

open SolidCore.Solidity.Source in
def rawResult (name : String) : Except TypeError CallResult :=
  CheckedInput.ownCall 4096 contract (CallTarget.name name) State.empty []

open SolidCore.Solidity.Source in
def describe (name : String) : String :=
  match rawResult name with
  | Except.error _ => "typeerror"
  | Except.ok (CallResult.returned _ vs) => s!"{name} returned {repr vs}"
  | Except.ok (CallResult.reverted _ w) => s!"{name} reverted {repr w}"

def wm (name : String) (expected : Word) : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract name State.empty [] expected

#eval accepted
#eval describe "fOr"
#eval describe "fAnd"
#eval describe "fXor"
#eval describe "fOrCast"
#eval describe "fOrNonCompound"

#eval wm "fOr" 0x112233ff
#eval wm "fAnd" 0x00223300
#eval wm "fXor" 0x112233bb
#eval wm "fOrCast" 0x112233ff
#eval wm "fOrNonCompound" 0x112233ff

#guard accepted
#guard isOkTrue (wm "fOr" 0x112233ff)
#guard isOkTrue (wm "fAnd" 0x00223300)
#guard isOkTrue (wm "fXor" 0x112233bb)
#guard isOkTrue (wm "fOrCast" 0x112233ff)
#guard isOkTrue (wm "fOrNonCompound" 0x112233ff)

end CompoundAssignBytesNLiteral
end Witness
end Solidity
end SolidCore
