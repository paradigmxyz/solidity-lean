/-
Acceptance-boundary witnesses (2026-07-08) for the over-accept tightenings
G2–G10 from `docs/solidus-solc-deep-comparison.md`.

Each item pins BOTH sides of the boundary on the Lean side:
  * a program pinned-solc 0.8.35 REJECTS is now rejected by this typechecker
    (`...Rejected : Bool := Result.isError (SourceUnit.check …)`), and
  * a neighbor solc still ACCEPTS stays accepted (`…Accepted`,
    `sourceUnitAccepted? …`) — the tightening must not over-reject.

The paired solc-REJECT `.sol` fixtures live under
`tests/forge-harness/acceptance-boundaries/invalid/` and are compiled by the
differential harness to confirm pinned solc rejects them. Helpers
(`su_singleContract`, `simpleReturnFunction`, `su_uint256`, `numberExpr`,
`SourceUnit.check`, `Result.isError`, `sourceUnitAccepted?`) come from
`SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- Local shorthands.
private def msgValueExpr : Expr := Expr.member (Expr.ident "msg") "value"
private def msgDataExpr : Expr := Expr.member (Expr.ident "msg") "data"

-- ===========================================================================
-- G2 — `msg.value` in a non-payable public/external function is REJECTED
-- (solc TypeError 5887, ViewPureChecker.cpp:270-294). Internal/private and
-- library functions are exempt; a payable function is fine.
-- ===========================================================================

def g2ViewMsgValueFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    mutability := StateMutability.view
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.returnValues (some msgValueExpr)) }

def g2MsgValueInViewRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G2View" g2ViewMsgValueFn))

def g2PayableMsgValueFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    mutability := StateMutability.payable
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.returnValues (some msgValueExpr)) }

def g2InternalMsgValueFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.returnValues (some msgValueExpr)) }

def g2MsgValueNeighborsAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "G2Payable" g2PayableMsgValueFn) &&
    sourceUnitAccepted? (su_singleContract "G2Internal" g2InternalMsgValueFn)

-- ===========================================================================
-- G3 — `==`/`!=` on reference types is REJECTED (solc TypeError 2271); value
-- types, addresses, contracts, enums and function pointers still compare.
-- ===========================================================================

def g3EqBytesFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "a", ty := Ty.bytes, location := some DataLocation.memory }
      , { name := some "b", ty := Ty.bytes
          location := some DataLocation.memory } ]
    returns := [{ name := none, ty := Ty.bool, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.binary BinaryOp.eq (Expr.ident "a") (Expr.ident "b")))) }

def g3EqOnBytesRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G3Bytes" g3EqBytesFn))

def g3EqAddressFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "a", ty := Ty.address false, location := none }
      , { name := some "b", ty := Ty.address false, location := none } ]
    returns := [{ name := none, ty := Ty.bool, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.binary BinaryOp.eq (Expr.ident "a") (Expr.ident "b")))) }

def g3EqUintFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    params :=
      [ { name := some "a", ty := su_uint256, location := none }
      , { name := some "b", ty := su_uint256, location := none } ]
    returns := [{ name := none, ty := Ty.bool, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.binary BinaryOp.eq (Expr.ident "a") (Expr.ident "b")))) }

def g3EqNeighborsAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "G3Addr" g3EqAddressFn) &&
    sourceUnitAccepted? (su_singleContract "G3Uint" g3EqUintFn)

-- ===========================================================================
-- G4 — a compile-time out-of-bounds constant index on a `bytesN`/fixed-size
-- array is REJECTED (solc TypeError 1859/3383). In-bounds constant and dynamic
-- indices still accept.
-- ===========================================================================

def g4BytesIndexFn (idx : String) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "b", ty := Ty.bytesN 4, location := none }]
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.index (Expr.ident "b") (numberExpr idx)))) }

def g4ArrayIndexFn (idx : String) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    params :=
      [ { name := some "a", ty := Ty.array su_uint256 (some 3)
          location := some DataLocation.memory } ]
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.index (Expr.ident "a") (numberExpr idx)))) }

def g4ConstOobRejected : Bool :=
  Result.isError
      (SourceUnit.check (su_singleContract "G4Bytes" (g4BytesIndexFn "4"))) &&
    Result.isError
      (SourceUnit.check (su_singleContract "G4Array" (g4ArrayIndexFn "3")))

def g4InBoundsAccepted : Bool :=
  sourceUnitAccepted?
      (su_singleContract "G4BytesOk" (g4BytesIndexFn "3")) &&
    sourceUnitAccepted?
      (su_singleContract "G4ArrayOk" (g4ArrayIndexFn "2"))

-- ===========================================================================
-- G5 — a bare `return;` with a non-empty return list is REJECTED, even when
-- every return is named (solc TypeError 6777, TypeChecker.cpp:1138). A
-- value-carrying return and an implicit fall-through still accept.
-- ===========================================================================

def g5BareReturnFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := some "a", ty := su_uint256, location := none }]
    body := some (Stmt.block [Stmt.returnValues none]) }

def g5BareReturnNamedRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G5" g5BareReturnFn))

def g5ValueReturnFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := some "a", ty := su_uint256, location := none }]
    body := some (Stmt.block [Stmt.returnValues (some (numberExpr "5"))]) }

def g5ImplicitReturnFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    returns := [{ name := some "a", ty := su_uint256, location := none }]
    body := some (Stmt.block []) }

def g5ReturnNeighborsAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "G5Value" g5ValueReturnFn) &&
    sourceUnitAccepted? (su_singleContract "G5Implicit" g5ImplicitReturnFn)

-- ===========================================================================
-- G6 — `super.f()` resolving to an abstract (unimplemented) base function is
-- REJECTED (solc TypeError 9582); an implemented super target still resolves.
-- ===========================================================================

def g6AbstractBase : ContractDecl :=
  { name := "G6Base"
    abstract := true
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            returns := [{ name := none, ty := su_uint256, location := none }]
            visibility := some Visibility.public_
            mutability := StateMutability.view
            virtual := true
            body := none } ] }

def g6DerivedSuperCall (baseName : Name) : ContractDecl :=
  { name := "G6Derived"
    bases := [{ base := userPath baseName }]
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            returns := [{ name := none, ty := su_uint256, location := none }]
            visibility := some Visibility.public_
            mutability := StateMutability.view
            virtual := true
            override? := some {}
            body :=
              some (Stmt.returnValues
                (some (Expr.call
                  (Expr.member (Expr.ident "super") "f") []))) } ] }

def g6SuperToAbstractRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items :=
          [ SourceItem.contract g6AbstractBase
          , SourceItem.contract (g6DerivedSuperCall "G6Base") ] })

-- Neighbor: the same super call resolves when the base function is implemented.
def g6ConcreteBase : ContractDecl :=
  { name := "G6BaseImpl"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            returns := [{ name := none, ty := su_uint256, location := none }]
            visibility := some Visibility.public_
            mutability := StateMutability.view
            virtual := true
            body := some (Stmt.returnValues (some (numberExpr "1"))) } ] }

def g6SuperToConcreteAccepted : Bool :=
  sourceUnitAccepted?
    { items :=
        [ SourceItem.contract g6ConcreteBase
        , SourceItem.contract (g6DerivedSuperCall "G6BaseImpl") ] }

-- ===========================================================================
-- G7 — a qualified `emit X.g()` whose member callee is not an event is
-- REJECTED (solc TypeError 9292). A simple-name and a member-form emit that
-- both resolve to a real event still accept.
-- ===========================================================================

def g7Event : ContractItem :=
  ContractItem.eventDecl { name := "E", params := [] }

def g7NonEventMemberContract : ContractDecl :=
  { name := "G7Bad"
    items :=
      [ g7Event
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "g"
            visibility := some Visibility.internal_
            mutability := StateMutability.pure
            body := some Stmt.empty }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "h"
            visibility := some Visibility.public_
            mutability := StateMutability.nonpayable
            body :=
              some (Stmt.emitEvent
                (Expr.call
                  (Expr.member (Expr.ident "G7Bad") "g") [])) } ] }

def g7EmitNonEventMemberRejected : Bool :=
  Result.isError
    (SourceUnit.check { items := [SourceItem.contract g7NonEventMemberContract] })

def g7EventMemberContract : ContractDecl :=
  { name := "G7Ok"
    items :=
      [ g7Event
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "h"
            visibility := some Visibility.public_
            mutability := StateMutability.nonpayable
            body :=
              some (Stmt.block
                [ Stmt.emitEvent (Expr.call (Expr.ident "E") [])
                , Stmt.emitEvent
                    (Expr.call (Expr.member (Expr.ident "G7Ok") "E") []) ]) } ] }

def g7EmitEventNeighborsAccepted : Bool :=
  sourceUnitAccepted? { items := [SourceItem.contract g7EventMemberContract] }

-- ===========================================================================
-- G9 — an inline array literal with a mapping element type is REJECTED (a
-- memory array of mappings is invalid; solc "only valid in storage"). An
-- inline array of a value type still accepts.
-- ===========================================================================

def g9MappingArrayContract : ContractDecl :=
  { name := "G9Bad"
    items :=
      [ ContractItem.stateVar
          { name := "m", ty := Ty.mapping su_uint256 su_uint256 }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            visibility := some Visibility.public_
            mutability := StateMutability.view
            body := some (Stmt.expr (Expr.array [Expr.ident "m"])) } ] }

def g9InlineArrayMappingRejected : Bool :=
  Result.isError
    (SourceUnit.check { items := [SourceItem.contract g9MappingArrayContract] })

def g9ValueArrayContract : ContractDecl :=
  { name := "G9Ok"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            body :=
              some (Stmt.expr
                (Expr.array [numberExpr "1", numberExpr "2"])) } ] }

def g9InlineArrayValueAccepted : Bool :=
  sourceUnitAccepted? { items := [SourceItem.contract g9ValueArrayContract] }

-- ===========================================================================
-- G10 — `msg.data` inside a `receive` function is REJECTED (solc TypeError
-- 7139). The same read in an ordinary function / fallback still accepts.
-- ===========================================================================

def g10ReceiveMsgDataContract : ContractDecl :=
  { name := "G10Bad"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.receive
            name := none
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            body := some (Stmt.expr msgDataExpr) } ] }

def g10MsgDataInReceiveRejected : Bool :=
  Result.isError
    (SourceUnit.check { items := [SourceItem.contract g10ReceiveMsgDataContract] })

def g10FallbackMsgDataContract : ContractDecl :=
  { name := "G10Ok"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.fallback
            name := none
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            body := some (Stmt.expr msgDataExpr) } ] }

def g10MsgDataInFallbackAccepted : Bool :=
  sourceUnitAccepted? { items := [SourceItem.contract g10FallbackMsgDataContract] }

end Examples
end TypeCheck
end Solidity
end SolidCore
