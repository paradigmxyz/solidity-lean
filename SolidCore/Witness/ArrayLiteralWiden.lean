/-
Inline-array-literal element-widening boundary witnesses (2026-07-09), task #56
(AL1). solc 0.8.35 types an inline array literal bottom-up (the smallest common
mobile element type, e.g. `[1,2,3] : uint8[3]`) and a fixed→fixed memory-array
conversion requires an IDENTICAL element type (`ArrayType::isImplicitlyConvertibleTo`,
non-copy branch — no implicit element widening). This typechecker previously
ACCEPTED assigning / returning / passing such a literal to a WIDER fixed-array
target; it now rejects exactly what solc rejects, in every position (assignment,
return, internal / external / public argument, struct-constructor field), while
keeping every solc-accepted neighbor.

Each `…Rejected : Bool := Result.isError (SourceUnit.check …)` pins a program
pinned-solc 0.8.35 REJECTS; each `…Accepted : Bool := sourceUnitAccepted? …`
pins a neighbor solc still ACCEPTS (the tightening must not over-reject). The
paired solc-REJECT `.sol` fixtures live under
`tests/forge-harness/array-literal-widen/invalid/`; the accepted controls' RUNTIME
values are pinned by the Forge harness in that lane. Helpers come from
`SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- Local shorthands.
private def alwNum (s : String) : Expr := numberExpr s
private def alwConv (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]
private def alwNeg (e : Expr) : Expr := Expr.unary UnaryOp.neg e
private def alwArr (elemTy : Ty) (k : Nat) : Ty := Ty.array elemTy (some k)
private def alw123 : Expr := Expr.array [alwNum "1", alwNum "2", alwNum "3"]

-- A single pure function declaring `T x = <init>;` (memory-located).
private def alwDeclFn (ty : Ty) (init : Expr) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [ { name := some "x", ty := some ty,
              location := some DataLocation.memory } ]
          (some init) ]) }

-- A single pure function `returns (T memory) { return <init>; }`.
private def alwReturnFn (ty : Ty) (init : Expr) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := none, ty := ty, location := some DataLocation.memory }]
    body := some (Stmt.returnValues (some init)) }

private def alwSU (fn : FunctionDecl) : SourceUnit :=
  { items := [SourceItem.contract
      { name := "C", items := [ContractItem.function fn] }] }

private def alwParam (bits : Nat) : Parameter :=
  { name := some "a"
    ty := alwArr (Ty.uint bits) 3
    location := some DataLocation.memory }

private def alwCalleeFn (bits : Nat) (vis : Visibility) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    visibility := some vis
    returns := []
    params := [alwParam bits]
    body := some (Stmt.block []) }

private def alwCallerFn (call : Expr) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := []
    mutability := StateMutability.nonpayable
    visibility := some Visibility.external_
    body := some (Stmt.expr call) }

private def alwCallSU (callee : FunctionDecl) (caller : FunctionDecl) : SourceUnit :=
  { items := [SourceItem.contract
      { name := "C"
        items := [ContractItem.function callee, ContractItem.function caller] }] }

private def alwStructSU (bits : Nat) : SourceUnit :=
  { items := [SourceItem.contract
      { name := "C"
        items :=
          [ ContractItem.structDecl
              { name := "S"
                fields := [{ name := "a", ty := alwArr (Ty.uint bits) 3 }] }
          , ContractItem.function
              { simpleReturnFunction with
                name := some "f"
                returns := []
                body := some (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "s"
                          ty := some (Ty.user { segments := ["S"] })
                          location := some DataLocation.memory } ]
                      (some (Expr.call (Expr.ident "S")
                        [Arg.positional alw123])) ]) } ] }] }

-- ===========================================================================
-- REJECTED — a widened fixed-array target (solc types the literal narrower)
-- ===========================================================================

-- `uint256[3] memory x = [1,2,3];`  (solc: uint8[3] ↛ uint256[3])
def alwAssignWiden256Rejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (Ty.uint 256) 3) alw123)))

-- `uint16[3] memory x = [1,2,3];`   (solc: uint8[3] ↛ uint16[3])
def alwAssignWiden16Rejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (Ty.uint 16) 3) alw123)))

-- `uint256[2][2] memory x = [[1,2],[3,4]];`  (solc: uint8[2][2] ↛ uint256[2][2])
def alwAssignWidenMultidimRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (alwArr (Ty.uint 256) 2) 2)
      (Expr.array
        [ Expr.array [alwNum "1", alwNum "2"]
        , Expr.array [alwNum "3", alwNum "4"] ]))))

-- `function f() returns (uint256[3] memory){ return [1,2,3]; }`
def alwReturnWiden256Rejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwReturnFn (alwArr (Ty.uint 256) 3) alw123)))

-- internal `g(uint256[3])` called `g([1,2,3])`
def alwArgInternalWidenRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwCallSU (alwCalleeFn 256 Visibility.internal_)
      (alwCallerFn (Expr.call (Expr.ident "g") [Arg.positional alw123]))))

-- external `this.g([1,2,3])` with `g(uint256[3]) external`
def alwArgExternalWidenRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwCallSU (alwCalleeFn 256 Visibility.external_)
      (alwCallerFn (Expr.call
        (Expr.member (Expr.ident "this") "g") [Arg.positional alw123]))))

-- struct constructor `S([1,2,3])` where `S { uint256[3] a; }`
def alwStructFieldWidenRejected : Bool :=
  Result.isError (SourceUnit.check (alwStructSU 256))

-- `bytes1[2] memory x = [0x11,0x22];`  (solc: uint8[2] ↛ bytes1[2])
def alwBytesArrRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (Ty.bytesN 1) 2)
      (Expr.array [alwNum "0x11", alwNum "0x22"]))))

def alwAllRejected : Bool :=
  alwAssignWiden256Rejected && alwAssignWiden16Rejected &&
    alwAssignWidenMultidimRejected && alwReturnWiden256Rejected &&
    alwArgInternalWidenRejected && alwArgExternalWidenRejected &&
    alwStructFieldWidenRejected && alwBytesArrRejected

-- ===========================================================================
-- ACCEPTED — the element type matches solc's bottom-up literal type
-- ===========================================================================

-- `uint8[3] memory x = [1,2,3];`  (common mobile type uint8 == target)
def alwAssignUint8Accepted : Bool :=
  sourceUnitAccepted? (alwSU (alwDeclFn (alwArr (Ty.uint 8) 3) alw123))

-- `uint256[3] memory x = [uint256(1),2,3];`  (explicit element forces uint256)
def alwAssignExplicit256Accepted : Bool :=
  sourceUnitAccepted? (alwSU (alwDeclFn (alwArr (Ty.uint 256) 3)
    (Expr.array [alwConv (Ty.uint 256) (alwNum "1"), alwNum "2", alwNum "3"])))

-- `int8[2] memory x = [int8(-1),2];`  (common type int8; order-sensitive)
def alwAssignInt8Accepted : Bool :=
  sourceUnitAccepted? (alwSU (alwDeclFn (alwArr (Ty.int 8) 2)
    (Expr.array [alwConv (Ty.int 8) (alwNeg (alwNum "1")), alwNum "2"])))

-- `uint8[2][2] memory x = [[1,2],[3,4]];`  (nested common type uint8)
def alwAssignMultidim8Accepted : Bool :=
  sourceUnitAccepted? (alwSU (alwDeclFn (alwArr (alwArr (Ty.uint 8) 2) 2)
    (Expr.array
      [ Expr.array [alwNum "1", alwNum "2"]
      , Expr.array [alwNum "3", alwNum "4"] ])))

-- `bytes1[2] memory x = [bytes1(0x11),bytes1(0x22)];`
def alwBytesTypedAccepted : Bool :=
  sourceUnitAccepted? (alwSU (alwDeclFn (alwArr (Ty.bytesN 1) 2)
    (Expr.array
      [ alwConv (Ty.bytesN 1) (alwNum "0x11")
      , alwConv (Ty.bytesN 1) (alwNum "0x22") ])))

-- internal `g(uint8[3])` called `g([1,2,3])` — accepted
def alwArgUint8Accepted : Bool :=
  sourceUnitAccepted?
    (alwCallSU (alwCalleeFn 8 Visibility.internal_)
      (alwCallerFn (Expr.call (Expr.ident "g") [Arg.positional alw123])))

def alwAllAccepted : Bool :=
  alwAssignUint8Accepted && alwAssignExplicit256Accepted &&
    alwAssignInt8Accepted && alwAssignMultidim8Accepted &&
    alwBytesTypedAccepted && alwArgUint8Accepted

-- ===========================================================================
-- Already-correct neighbors that must STAY rejected (empty/ragged/dynamic/overflow)
-- ===========================================================================

def alwEmptyStillRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (Ty.uint 8) 0) (Expr.array []))))

def alwRaggedStillRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (alwArr (Ty.uint 8) 2) 2)
      (Expr.array
        [ Expr.array [alwNum "1"]
        , Expr.array [alwNum "2", alwNum "3"] ]))))

def alwFixedToDynamicStillRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (Ty.array (Ty.uint 256) none) alw123)))

def alwElementOverflowStillRejected : Bool :=
  Result.isError (SourceUnit.check
    (alwSU (alwDeclFn (alwArr (Ty.uint 8) 2)
      (Expr.array [alwNum "1", alwNum "256"]))))

def alwNeighborsStillRejected : Bool :=
  alwEmptyStillRejected && alwRaggedStillRejected &&
    alwFixedToDynamicStillRejected && alwElementOverflowStillRejected

end Examples
end TypeCheck
end Solidity
end SolidCore
