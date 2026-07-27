import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NEGATED-NARROW-TYPE-MIN-CAST (coverage gap, over-reject): unary `-` applied to an
explicit narrow signed-int CAST of the literal equal to that type's MINIMUM
(`-int8(-128)`) must type at the OPERAND width (int8), NOT re-fold to a wider
rational:

  function f() external pure returns (int8) {
    unchecked { return -int8(-128); }
  }

solc 0.8.35 + EVM: `int8(-128)` is a typed int8 value; `-` negates it at int8.
The rational fold `128` overflows int8, so it is a RUNTIME int8 negation:
`-128` (wrap) in an `unchecked` block, `Panic(0x11)` in a checked block.

solidity-lean USED TO fail closed at typecheck with
`expectedType (int 8) (int 256)`: the `neg` arm ran `toCoreNumericLiteralAs?
(int 256) expr` on the WHOLE `-int8(-128)`. `numberLiteralRat?` STRIPS explicit
casts, so it folded the expression to the rational `128`, typed the negation as
`int256`, and then the `int256 → int8` return conversion failed closed because
`128` does not fit int8 — over-rejecting the whole contract.

FIX: gate the int256 fold on the operand being an UNTYPED number literal
(`exprIsUntypedNumberLiteralExpression inner`). A TYPED operand (an explicit
narrow cast, a variable, `type(intN).min`) keeps its own type; the NEG-NARROW
lowering path then applies the operand-width checked cleanup at runtime.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NegatedNarrowCastMin

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def i8 : Ty := Ty.int 8
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def neg (e : Expr) : Expr := Expr.unary UnaryOp.neg e
private def conv (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]

-- A pure `returns (int8)` fn whose body is `stmts`.
private def fnWith (nm : String) (stmts : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some nm
      visibility := some Visibility.external_, mutability := StateMutability.pure
      params := [], returns := [{ name := none, ty := i8, location := none }]
      virtual := false, override? := none, modifiers := []
      body := some (Stmt.block stmts) }

-- The submission `f()`: `unchecked { return -int8(-128); }`.
private def fFn : ContractItem :=
  fnWith "f"
    [ Stmt.unchecked
        (Stmt.block [ Stmt.returnValues (some (neg (conv i8 (neg (lit "128"))))) ]) ]

-- CHECKED variant: `return -int8(-128);` — solc+EVM revert Panic(0x11).
private def fCheckedFn : ContractItem :=
  fnWith "fChecked"
    [ Stmt.returnValues (some (neg (conv i8 (neg (lit "128"))))) ]

-- CONTROL: `-int8(-127)` = 127 (fits int8). Same form, not the type minimum.
private def gFn : ContractItem :=
  fnWith "g" [ Stmt.returnValues (some (neg (conv i8 (neg (lit "127"))))) ]

-- CONTROL: `-int8(5)` = -5. Same form, positive operand.
private def hFn : ContractItem :=
  fnWith "h" [ Stmt.returnValues (some (neg (conv i8 (lit "5")))) ]

-- CONTROL: `int8 m = int8(-128); unchecked { return -m; }` = -128. The value
-- bound to a VARIABLE first — already agreed with solc.
private def kFn : ContractItem :=
  fnWith "k"
    [ Stmt.varDecl
        [ { name := some "m", ty := some i8, location := none } ]
        (some (conv i8 (neg (lit "128"))))
    , Stmt.unchecked
        (Stmt.block [ Stmt.returnValues (some (neg (Expr.ident "m"))) ]) ]

def runContractDecl : ContractDecl :=
  { kind := ContractKind.contract, name := "C", abstract := false, bases := []
    items := [fFn, fCheckedFn, gFn, hFn, kFn] }

abbrev C := runContractDecl

def runSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "^0.8.35"
      , SourceItem.contract runContractDecl ] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w128neg : Word := SolidCore.Solidity.Shared.signedToWord (-128)
private def w127 : Word := SolidCore.Solidity.Shared.signedToWord 127
private def w5neg : Word := SolidCore.Solidity.Shared.signedToWord (-5)

-- A single-int8 return: the interpreter returns it as a `Value.int` payload
-- (`checkedOwnCallWordMatches`'s `asWord?` unwraps only `Value.word`), so match
-- both spellings and compare via `wordEq`, exactly as the sibling neg witnesses.
private def returnsWord (nm : String) (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 256 C (CallTarget.name nm) State.empty []
  match result with
  | CallResult.returned _ [Value.int v] => Except.ok (wordEq v expected)
  | CallResult.returned _ [Value.word v] => Except.ok (wordEq v expected)
  | _ => Except.ok false

-- f(): unchecked `-int8(-128)` wraps to int8.min = -128 (0x…ff80).
def f_wraps_min : Except TypeError Bool := returnsWord "f" w128neg
-- fChecked(): checked `-int8(-128)` reverts Panic(0x11) — overflow.
def fChecked_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 C "fChecked" State.empty [] 0x11
-- controls
def g_is_127 : Except TypeError Bool := returnsWord "g" w127
def h_is_neg5 : Except TypeError Bool := returnsWord "h" w5neg
def k_is_min : Except TypeError Bool := returnsWord "k" w128neg

#eval accepted
#eval (f_wraps_min, fChecked_panics, g_is_127, h_is_neg5, k_is_min)

#guard accepted
#guard isOkTrue f_wraps_min
#guard isOkTrue fChecked_panics
#guard isOkTrue g_is_127
#guard isOkTrue h_is_neg5
#guard isOkTrue k_is_min

end NegatedNarrowCastMin
end Witness
end Solidity
end SolidCore
