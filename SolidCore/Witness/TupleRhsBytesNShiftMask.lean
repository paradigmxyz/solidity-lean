import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-RHS-BYTESN-SHIFT-MASK (S, bytesn-width-expanding-op-as-tuple-rhs-component-skips-width-mask):
a width-EXPANDING `bytesN` operation (`b << k` or `~b`) used as a COMPONENT of a
tuple RHS silently skips its per-op width mask and yields a WRONG VALUE.

  bytes4 b = 0x11223344;
  bytes4 x; bytes4 y;
  (x, y) = (b << 8, b);   // solc+EVM: x == 0x22334400
                          // solidity-lean: x == 0x1122334400 (mask skipped)

The single-assignment control (`x = b << 8`) AGREES: it routes through the
env-aware `assignmentCoreWithEnv?` (→ `structCtorTupleCoreAsWithEnv?` →
`toCoreAsWithEnv?`, which inserts the FB1 `fixedBytesCast size size` lane cleanup).
The tuple-RHS component is lowered by the env-LESS `Expr.toCore?` (no target type),
so the mask is never emitted. `>>`/`&` (in-lane) and the SWAP form already agree.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleRhsBytesNShiftMask

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def b4 : Ty := Ty.bytesN 4
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y
private def shr (x y : Expr) : Expr := Expr.binary BinaryOp.shr x y
private def bnot (x : Expr) : Expr := Expr.unary UnaryOp.bitNot x
private def tv (e : Expr) : TupleItem := TupleItem.value e
private def id (n : String) : Expr := Expr.ident n

private def fn (name : String) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some name,
      visibility := some Visibility.external_,
      mutability := StateMutability.pure,
      params := [], returns := [{ name := none, ty := b4, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def declB : Stmt :=
  Stmt.varDecl [{ name := some "b", ty := some b4 }] (some (lit "0x11223344"))
private def declXY : List Stmt :=
  [ Stmt.varDecl [{ name := some "x", ty := some b4 }] none
  , Stmt.varDecl [{ name := some "y", ty := some b4 }] none ]

private def tupleAssign (lhs rhs : List TupleItem) : Stmt :=
  Stmt.expr (Expr.assign (Expr.tuple lhs) AssignOp.assign (Expr.tuple rhs))

-- (x, y) = (b << 8, b); return x;   solc: 0x22334400
private def fShlFirst : ContractItem :=
  fn "fShlFirst"
    (declB :: declXY ++
      [ tupleAssign [tv (id "x"), tv (id "y")] [tv (shl (id "b") (lit "8")), tv (id "b")]
      , Stmt.returnValues (some (id "x")) ])

-- (x, y) = (~b, b); return x;   solc: ~0x11223344 = 0xEEDDCCBB
private def fNotFirst : ContractItem :=
  fn "fNotFirst"
    (declB :: declXY ++
      [ tupleAssign [tv (id "x"), tv (id "y")] [tv (bnot (id "b")), tv (id "b")]
      , Stmt.returnValues (some (id "x")) ])

-- (x, y) = (b, b << 8); return y;   solc: 0x22334400 (second position)
private def fShlSecond : ContractItem :=
  fn "fShlSecond"
    (declB :: declXY ++
      [ tupleAssign [tv (id "x"), tv (id "y")] [tv (id "b"), tv (shl (id "b") (lit "8"))]
      , Stmt.returnValues (some (id "y")) ])

-- DECLARATION form: (bytes4 x2, bytes4 y2) = (b << 8, b); return x2;
private def fDecl : ContractItem :=
  fn "fDecl"
    (declB ::
      [ Stmt.varDecl
          [ { name := some "x2", ty := some b4 }, { name := some "y2", ty := some b4 } ]
          (some (Expr.tuple [tv (shl (id "b") (lit "8")), tv (id "b")]))
      , Stmt.returnValues (some (id "x2")) ])

-- CONTROL (agrees): single assignment x = b << 8.
private def fSingle : ContractItem :=
  fn "fSingle"
    (declB :: declXY ++
      [ Stmt.expr (Expr.assign (id "x") AssignOp.assign (shl (id "b") (lit "8")))
      , Stmt.returnValues (some (id "x")) ])

-- CONTROL (agrees): right shift in tuple RHS (in-lane, no mask needed).
private def fShrTuple : ContractItem :=
  fn "fShrTuple"
    (declB :: declXY ++
      [ tupleAssign [tv (id "x"), tv (id "y")] [tv (shr (id "b") (lit "8")), tv (id "b")]
      , Stmt.returnValues (some (id "x")) ])

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "C", abstract := false, bases := [],
    items := [ fShlFirst, fNotFirst, fShlSecond, fDecl, fSingle, fShrTuple ] }

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
#eval describe "fShlFirst"
#eval describe "fNotFirst"
#eval describe "fShlSecond"
#eval describe "fDecl"
#eval describe "fSingle"
#eval describe "fShrTuple"

#eval wm "fShlFirst" 0x22334400
#eval wm "fNotFirst" 0xEEDDCCBB
#eval wm "fShlSecond" 0x22334400
#eval wm "fDecl" 0x22334400
#eval wm "fSingle" 0x22334400
#eval wm "fShrTuple" 0x00112233

#guard accepted
#guard isOkTrue (wm "fShlFirst" 0x22334400)
#guard isOkTrue (wm "fNotFirst" 0xEEDDCCBB)
#guard isOkTrue (wm "fShlSecond" 0x22334400)
#guard isOkTrue (wm "fDecl" 0x22334400)
#guard isOkTrue (wm "fSingle" 0x22334400)
#guard isOkTrue (wm "fShrTuple" 0x00112233)

end TupleRhsBytesNShiftMask
end Witness
end Solidity
end SolidCore
