import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-VARDECL-FROM-EXPR (#171 abi.decode RHS, #172 ternary RHS).

A multi-binding tuple variable DECLARATION `(T1 a, …, Tn z) = rhs` binds each
declared local to the corresponding component of the tuple-typed RHS. solc
accepts these; solidity-lean accepted the contract but the source→core lowering
handled the RHS only in a literal-`Expr.tuple` form (and, on the internal-call
body path, CALL-shaped forms). Any OTHER tuple-typed RHS in DECLARATION position
— an `abi.decode(data, (…))` member call (#171) or a `c ? (…) : (…)` ternary
(#172) — was missed, so replay yielded `TypeError.unsupported` even though
acceptance passed. The tuple-ASSIGNMENT path (`(a, b) = rhs`) already lowered ANY
rhs via `Expr.toCore?` + `assignTuple`; the fix mirrors it in DECLARATION
position generally: declare the fresh locals (anonymous/hole components skipped),
then destructure the lowered RHS through `assignTuple`.

Real-EVM Forge ground truth: `tests/forge-harness/tuple-vardecl-abi-decode`
(addPair(encode(3,4)) = 7, firstOfPair/secondOfPair holes, headAndArray with a
dynamic `uint256[]` component) and `tests/forge-harness/tuple-vardecl-ternary`
(c ? (1,2) : (3,4) => 3 when true, 7 when false). Runtime values pinned below.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleVarDeclAbiDecode

open SolidCore.Solidity.Source

private def uintTy : Ty := Ty.uint 256
private def uintArrTy : Ty := Ty.array (Ty.uint 256) none

private def decodeTypes (items : List TupleItem) : Expr :=
  Expr.tuple items

private def uintTypeItem : TupleItem := TupleItem.value (Expr.typeName uintTy)
private def uintArrTypeItem : TupleItem := TupleItem.value (Expr.typeName uintArrTy)

private def dataParam : Parameter :=
  { name := some "data", ty := Ty.bytes, location := some DataLocation.calldata }

private def uintBinding (n : Name) : VarBinding :=
  { name := some n, ty := some uintTy, location := none }

private def holeBinding : VarBinding :=
  { name := none, ty := none, location := none }

private def uintArrBinding (n : Name) : VarBinding :=
  { name := some n, ty := some uintArrTy, location := some DataLocation.memory }

private def decodeCall (types : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "decode")
    [Arg.positional (Expr.ident "data"), Arg.positional types]

private def pureExtFn (nm : Name) (returns : List Parameter) (body : List Stmt) :
    ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some nm,
      visibility := some Visibility.external_, mutability := StateMutability.pure,
      params := [dataParam], returns := returns,
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

-- addPair: `(uint x, uint y) = abi.decode(data, (uint, uint)); return x + y;`
private def addPairFn : ContractItem :=
  pureExtFn "addPair" [{ name := none, ty := uintTy, location := none }]
    [ Stmt.varDecl [uintBinding "x", uintBinding "y"]
        (some (decodeCall (decodeTypes [uintTypeItem, uintTypeItem])))
    , Stmt.returnValues
        (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.ident "y"))) ]

-- firstOfPair: `(uint x, ) = abi.decode(data, (uint, uint)); return x;`
private def firstOfPairFn : ContractItem :=
  pureExtFn "firstOfPair" [{ name := none, ty := uintTy, location := none }]
    [ Stmt.varDecl [uintBinding "x", holeBinding]
        (some (decodeCall (decodeTypes [uintTypeItem, uintTypeItem])))
    , Stmt.returnValues (some (Expr.ident "x")) ]

-- secondOfPair: `(, uint y) = abi.decode(data, (uint, uint)); return y;`
private def secondOfPairFn : ContractItem :=
  pureExtFn "secondOfPair" [{ name := none, ty := uintTy, location := none }]
    [ Stmt.varDecl [holeBinding, uintBinding "y"]
        (some (decodeCall (decodeTypes [uintTypeItem, uintTypeItem])))
    , Stmt.returnValues (some (Expr.ident "y")) ]

-- headAndArray:
--   `(uint x, uint[] memory a) = abi.decode(data, (uint, uint[]));
--    return (x, a[1]);`
private def headAndArrayFn : ContractItem :=
  pureExtFn "headAndArray"
    [ { name := none, ty := uintTy, location := none }
    , { name := none, ty := uintTy, location := none } ]
    [ Stmt.varDecl [uintBinding "x", uintArrBinding "a"]
        (some (decodeCall (decodeTypes [uintTypeItem, uintArrTypeItem])))
    , Stmt.returnValues
        (some (Expr.tuple
          [ TupleItem.value (Expr.ident "x")
          , TupleItem.value
              (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "1"))) ])) ]

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "TupleVarDeclAbiDecodeTarget",
    abstract := false, bases := [],
    items := [addPairFn, firstOfPairFn, secondOfPairFn, headAndArrayFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleVarDeclAbiDecode
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleVarDeclTernary

open SolidCore.Solidity.Source

private def uintTy : Ty := Ty.uint 256

private def castUint (s : String) : Expr :=
  Expr.call (Expr.typeName uintTy) [Arg.positional (Expr.literal (Literal.number s))]

private def uintBinding (n : Name) : VarBinding :=
  { name := some n, ty := some uintTy, location := none }

-- `bool c = <b>; (uint a, uint b) = c ? (1, 2) : (3, 4); return a + b;`
private def pickFn (nm : Name) (cond : Bool) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some nm,
      visibility := some Visibility.external_, mutability := StateMutability.pure,
      params := [], returns := [{ name := none, ty := uintTy, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.varDecl [{ name := some "c", ty := some Ty.bool, location := none }]
            (some (Expr.literal (Literal.bool cond)))
        , Stmt.varDecl [uintBinding "a", uintBinding "b"]
            (some (Expr.ternary (Expr.ident "c")
              (Expr.tuple [TupleItem.value (castUint "1"), TupleItem.value (castUint "2")])
              (Expr.tuple [TupleItem.value (castUint "3"), TupleItem.value (castUint "4")])))
        , Stmt.returnValues
            (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "TupleVarDeclTernaryTarget",
    abstract := false, bases := [],
    items := [pickFn "whenTrue" true, pickFn "whenFalse" false] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleVarDeclTernary
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleVarDeclAbiDecode

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev DecFam := SolidCore.Solidity.SolcAstImport.TupleVarDeclAbiDecode.importedContract
abbrev TernFam := SolidCore.Solidity.SolcAstImport.TupleVarDeclTernary.importedContract

private def word (n : Word) : List Byte := ABI.encodeWord n

-- abi.encode(3, 4) / abi.encode(9, 4) as calldata bytes.
private def encPair (x y : Word) : CoreValue := Value.bytes (word x ++ word y)

-- abi.encode(9, [11, 22, 33]): head word, offset 0x40, length 3, then elements.
private def encHeadArr : CoreValue :=
  Value.bytes (word 9 ++ word 0x40 ++ word 3 ++ word 11 ++ word 22 ++ word 33)

-- Acceptance: both imported contracts type-check.
def decodeAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TupleVarDeclAbiDecode.importedContractAccepted
def ternaryAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TupleVarDeclTernary.importedContractAccepted

-- #171 abi.decode-RHS runtime values (Forge-confirmed).
def addPair_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 DecFam "addPair" State.empty [encPair 3 4] 7
def firstOfPair_is_9 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 DecFam "firstOfPair" State.empty [encPair 9 4] 9
def secondOfPair_is_4 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 DecFam "secondOfPair" State.empty [encPair 9 4] 4

-- Reference-type component: returns (x, a[1]) = (9, 22).
def headAndArray_is_9_22 : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 256 DecFam (CallTarget.name "headAndArray") State.empty [encHeadArr]
  match result with
  | CallResult.returned _ [Value.word x, Value.word second] =>
      Except.ok (wordEq x 9 && wordEq second 22)
  | _ => Except.ok false

-- #172 ternary-RHS runtime values (Forge-confirmed): true => 1+2 = 3, false => 3+4 = 7.
def ternaryTrue_is_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 TernFam "whenTrue" State.empty [] 3
def ternaryFalse_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 TernFam "whenFalse" State.empty [] 7

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard decodeAccepted
#guard ternaryAccepted
#guard isOkTrue addPair_is_7
#guard isOkTrue firstOfPair_is_9
#guard isOkTrue secondOfPair_is_4
#guard isOkTrue headAndArray_is_9_22
#guard isOkTrue ternaryTrue_is_3
#guard isOkTrue ternaryFalse_is_7

end TupleVarDeclAbiDecode
end Witness
end Solidity
end SolidCore
