/-
#54 (MOD-RET) modifier `return <void expr>` reject witnesses.

Pins a CONFIRMED over-accept fixed on the Lean side:

  * solc 0.8.35 REJECTS a `return` that carries ANY expression inside a
    MODIFIER body — even a void-typed one like `return delete x;` or
    `return require(true);` — with TypeError 7552 "Return arguments not
    allowed" (`TypeChecker::endVisit(Return)`, TypeChecker.cpp:1133-1146: a
    modifier's `functionReturnParameters` is nullptr, so any return argument
    errors). Confirmed against the pinned solc: both modifier forms emit
    "Return arguments not allowed". Pinned by the `*Rejected` witnesses.

  * The precision boundary: this is NOT the same as a zero-return FUNCTION,
    whose empty-BUT-non-null return list still permits a void-typed return
    expression. `function zr() internal { return delete x; }` compiles cleanly
    under the pinned solc and must stay ACCEPTED. Pinned by the `*Accepted`
    witnesses. A bare `return;` in a modifier also stays accepted.

Kept in the built library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Checked

namespace SolidCore
namespace Solidity
namespace Executable
namespace ModifierReturnReject

open Solidity

private def deleteX : Expr := Expr.unary UnaryOp.delete (Expr.ident "x")

private def requireTrue : Expr :=
  Expr.call (Expr.ident "require")
    [Arg.positional (Expr.literal (Literal.bool true))]

-- uint256 x;
private def stateX : ContractItem :=
  ContractItem.stateVar
    { name := "x"
      ty := Ty.uint 256
      visibility := some Visibility.internal_
      mutability := VarMutability.mutable
      override? := none
      init := none }

-- modifier m() { <ret>; _; }
private def modWithReturn (ret : Stmt) : ContractItem :=
  ContractItem.modifierDecl
    { name := "m"
      params := []
      body := some (Stmt.block [ret, Stmt.modifierPlaceholder]) }

-- function f() m { }  (applies the modifier so `_` has a place to expand)
private def userFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "f"
      visibility := some Visibility.public_
      mutability := StateMutability.nonpayable
      params := []
      returns := []
      virtual := false
      override? := none
      modifiers := [{ target := { segments := ["m"] }, args := [] }]
      body := some (Stmt.block []) }

private def unit (items : List ContractItem) : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "C"
            abstract := false
            bases := []
            items := items } ] }

private def accepted? (u : SourceUnit) : Bool :=
  TypeCheck.sourceUnitAccepted? u

-- ===== REJECTS: a modifier `return` carrying an expression. =====

-- modifier m() { return delete x; _; }
def modReturnDeleteRejected : Bool :=
  accepted? (unit
    [stateX, modWithReturn (Stmt.returnValues (some deleteX)), userFn]) == false

-- modifier m() { return require(true); _; }
def modReturnRequireRejected : Bool :=
  accepted? (unit
    [stateX, modWithReturn (Stmt.returnValues (some requireTrue)), userFn]) == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

-- modifier m() { return; _; }  (bare return in a modifier stays allowed)
def modBareReturnAccepted : Bool :=
  accepted? (unit
    [stateX, modWithReturn (Stmt.returnValues none), userFn]) == true

-- function zr() internal { return delete x; }  (zero-return function, NOT a
-- modifier: empty-but-non-null return list still permits a void-typed return)
def zeroReturnFnDeleteAccepted : Bool :=
  accepted? (unit
    [ stateX
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "zr"
          visibility := some Visibility.internal_
          mutability := StateMutability.nonpayable
          params := []
          returns := []
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block [Stmt.returnValues (some deleteX)]) } ])
    == true

end ModifierReturnReject
end Executable
end Solidity
end SolidCore
