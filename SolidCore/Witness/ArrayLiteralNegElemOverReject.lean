import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ARRAY-LITERAL-TRAILING-NEGATIVE-ELEMENT (coverage gap, over-reject): an inline
array literal whose type-determining FIRST element is explicitly typed, followed
by a bare NEGATIVE integer literal in a NON-FIRST position, must type as the
first element's type — solc `Type::commonType` folds the accumulated element
type with the literal's `mobileType()` (`commonType(int256, int8) = int256`):

  function f() external pure returns (int256) {
    int256[2] memory a = [int256(2), -1];
    return a[1];
  }

solc 0.8.35 + EVM: types the literal `int256[2]`, `a[1] == -1`
(`0xff…ff`). solidity-lean USED TO fail closed at typecheck with
`expectedType int256[2] int8[2]`: the array-element common-type fold
(`commonArrayElementTyFrom?`) built a probe whose SOURCE was the current
element (`-1`) while its TY was the accumulator (`int256`); the else arm then
re-derived the LEFT operand's type from that source — treating the accumulator
as the untyped literal `-1` and collapsing `int256` to `mobileType(-1) = int8`.
The bug was POSITIONAL (a bare negative literal in the FIRST slot seeds the
accumulator directly, so it never hit the fold) and SIGN-specific (a bare
POSITIVE literal is a DIRECT literal, caught by the fits-accumulator fast path).
Fixed: the fold folds the accumulator TY with each element's own mobile/checked
type, never re-mobilizing the accumulator from the element's source.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace ArrayLiteralNegElemOverReject

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def i256 : Ty := Ty.int 256
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def conv (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]

-- int256[2] memory a = [int256(2), -1];  return a[1];
private def body : List Stmt :=
  [ Stmt.varDecl
      [ { name := some "a", ty := some (Ty.array i256 (some 2)),
          location := some DataLocation.memory } ]
      (some (Expr.array [ conv i256 (lit "2"), Expr.unary UnaryOp.neg (lit "1") ]))
  , Stmt.returnValues (some (Expr.index (Expr.ident "a") (lit "1"))) ]

private def fFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "f"
    visibility := some Visibility.external_, mutability := StateMutability.pure
    params := [], returns := [{ name := none, ty := i256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block body) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "C", abstract := false, bases := []
  items := [ ContractItem.function fFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

open SolidCore.Solidity.Source in
def rawResult : Except TypeError (CallResult) :=
  CheckedInput.ownCall 4096 runContract (CallTarget.name "f") State.empty []

-- signedToWord (-1) = 2^256 - 1 = 0xff…ff, matching the EVM measurement
-- (`0xff…ff…ff`). The returned int256 value carries a `Value.int` payload.
open SolidCore.Solidity.Source in
def run_result : Except TypeError Bool := do
  let result ← rawResult
  match result with
  | CallResult.returned _ [Value.int v] =>
      Except.ok (wordEq v (SolidCore.Solidity.Shared.signedToWord (-1)))
  | CallResult.returned _ [Value.word v] =>
      Except.ok (wordEq v (SolidCore.Solidity.Shared.signedToWord (-1)))
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

open SolidCore.Solidity.Source in
def describe : String :=
  match rawResult with
  | Except.error _ => "typeerror"
  | Except.ok (CallResult.returned _ vs) => s!"returned {repr vs}"
  | Except.ok (CallResult.reverted _ w) => s!"reverted {repr w}"

-- ===========================================================================
-- Controls — the boundary is POSITIONAL and SIGN-specific. A pure `T x = init;`
-- decl SU whose acceptance we can pin at typecheck.
-- ===========================================================================

private def declSU (ty : Ty) (init : Expr) : SourceUnit :=
  { items :=
      [ SourceItem.contract
          { kind := ContractKind.contract, name := "C", abstract := false,
            bases := [],
            items :=
              [ ContractItem.function
                  { kind := FunctionKind.function, name := some "g"
                    visibility := some Visibility.external_
                    mutability := StateMutability.pure
                    params := [], returns := []
                    virtual := false, override? := none, modifiers := []
                    body := some (Stmt.block
                      [ Stmt.varDecl
                          [ { name := some "x", ty := some ty,
                              location := some DataLocation.memory } ]
                          (some init) ]) } ] } ] }

private def okDecl (ty : Ty) (init : Expr) : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit (declSU ty init))

private def neg (e : Expr) : Expr := Expr.unary UnaryOp.neg e

-- `int256[2] x = [-1, int256(2)];` — same bare negative literal, but FIRST
-- (seeds the accumulator directly). solc accepts; must STILL accept.
def accNegFirst : Bool :=
  okDecl (Ty.array i256 (some 2)) (Expr.array [ neg (lit "1"), conv i256 (lit "2") ])

-- `int256[3] x = [-1, int256(-2), -3];` — a bare negative in a NON-FIRST slot
-- (the second over-reject the manifest cites). solc accepts.
def accTriple : Bool :=
  okDecl (Ty.array i256 (some 3))
    (Expr.array [ neg (lit "1"), conv i256 (neg (lit "2")), neg (lit "3") ])

-- `int256[2] x = [int256(1), 2];` — bare literal non-first but POSITIVE. accepts.
def accPosNonFirst : Bool :=
  okDecl (Ty.array i256 (some 2)) (Expr.array [ conv i256 (lit "1"), lit "2" ])

-- `int256[2] x = [int256(-1), int256(-2)];` — all elements cast. accepts.
def accAllCast : Bool :=
  okDecl (Ty.array i256 (some 2))
    (Expr.array [ conv i256 (neg (lit "1")), conv i256 (neg (lit "2")) ])

-- `uint8[2] x = [uint8(2), -1];` — a bare NEGATIVE has no common type with an
-- unsigned accumulator; solc rejects ("Unable to deduce common type"). The fix
-- must NOT over-accept.
def rejNegIntoUnsigned : Bool :=
  TypeCheck.Result.isError
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (declSU (Ty.array (Ty.uint 8) (some 2))
        (Expr.array [ conv (Ty.uint 8) (lit "2"), neg (lit "1") ])))

#eval accepted
#eval run_result
#eval describe
#eval (accNegFirst, accTriple, accPosNonFirst, accAllCast, rejNegIntoUnsigned)

#guard accepted
#guard isOkTrue run_result
#guard accNegFirst
#guard accTriple
#guard accPosNonFirst
#guard accAllCast
#guard rejNegIntoUnsigned

end ArrayLiteralNegElemOverReject
end Witness
end Solidity
end SolidCore
