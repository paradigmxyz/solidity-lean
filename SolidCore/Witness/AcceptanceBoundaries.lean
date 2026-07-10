/-
Acceptance-boundary witnesses (2026-07-08) for the over-accept tightenings
G2–G10 from `docs/solidity-lean-solc-deep-comparison.md`.

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

-- ===========================================================================
-- G8 — `revert E(...)` where a contract-level NON-error member (function or
-- state var) shadows a free error `E` is REJECTED (solc: "Expression has to be
-- an error." / "This expression is not callable."). solc resolves `E` to its
-- innermost declaration and rejects a revert of a non-error. Neighbors that
-- stay ACCEPTED: a genuine contract error `E`, and a bare free error `E` with
-- no shadowing member.
-- ===========================================================================

private def g8RevertE : Stmt :=
  Stmt.revertCall (Expr.call (Expr.ident "E") [Arg.positional (numberExpr "1")])

private def g8FreeErrorE : SourceItem :=
  SourceItem.freeError
    { name := "E", params := [{ name := none, ty := uint256, location := none }] }

-- free error E shadowed by a contract FUNCTION E.
def g8ErrorShadowedByFunctionSource : SourceUnit :=
  { items :=
      [ g8FreeErrorE
      , SourceItem.contract
          { name := "G8Fn"
            items :=
              [ ContractItem.function
                  { simpleReturnFunction with
                    name := some "E"
                    params := [{ name := some "x", ty := uint256, location := none }]
                    returns := [{ name := none, ty := uint256, location := none }]
                    body := some (Stmt.returnValues (some (Expr.ident "x"))) }
              , ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body := some g8RevertE } ] } ] }

-- free error E shadowed by a contract STATE VAR E.
def g8ErrorShadowedByStateVarSource : SourceUnit :=
  { items :=
      [ g8FreeErrorE
      , SourceItem.contract
          { name := "G8State"
            items :=
              [ ContractItem.stateVar { name := "E", ty := uint256 }
              , ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    mutability := StateMutability.nonpayable
                    body := some g8RevertE } ] } ] }

def g8ErrorShadowRejected : Bool :=
  Result.isError (SourceUnit.check g8ErrorShadowedByFunctionSource) &&
    Result.isError (SourceUnit.check g8ErrorShadowedByStateVarSource)

-- Neighbors that stay ACCEPTED: a genuine contract error, and a free error not
-- shadowed by any contract member.
def g8ContractErrorSource : SourceUnit :=
  { items :=
      [ SourceItem.contract
          { name := "G8OkContract"
            items :=
              [ ContractItem.errorDecl
                  { name := "E"
                    params := [{ name := none, ty := uint256, location := none }] }
              , ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body := some g8RevertE } ] } ] }

def g8FreeErrorSource : SourceUnit :=
  { items :=
      [ g8FreeErrorE
      , SourceItem.contract
          { name := "G8OkFree"
            items :=
              [ ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body := some g8RevertE } ] } ] }

def g8ErrorNeighborsAccepted : Bool :=
  sourceUnitAccepted? g8ContractErrorSource &&
    sourceUnitAccepted? g8FreeErrorSource

-- ===========================================================================
-- G11 — an `internal` or `private` contract-member function declared `payable`
-- is REJECTED (solc: `"internal" and "private" functions cannot be payable`,
-- TypeChecker::visitFunction). Only `external`/`public` members may carry the
-- `payable` mutability. Free/library functions are handled by their own
-- (already-existing) payable rejections and are not exercised here.
-- ===========================================================================

def g11PayableFn (vis : Visibility) : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "f"
    visibility := some vis
    mutability := StateMutability.payable
    body := some (Stmt.block []) }

def badInternalPayableRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "G11Internal" (g11PayableFn Visibility.internal_)))

def badPrivatePayableRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "G11Private" (g11PayableFn Visibility.private_)))

-- Neighbors that stay ACCEPTED: `external payable` and `public payable`.
def g11PayableNeighborsAccepted : Bool :=
  sourceUnitAccepted?
      (su_singleContract "G11External" (g11PayableFn Visibility.external_)) &&
    sourceUnitAccepted?
      (su_singleContract "G11Public" (g11PayableFn Visibility.public_))

-- ===========================================================================
-- G12 — regression pins for two shapes solc REJECTS that this typechecker
-- already rejected (verified 2026-07-09; these were investigated as suspected
-- over-accepts but the model was already correct). Pinned so a future loosening
-- cannot silently re-open them.
--   * implicit `string memory` → `bytes memory` assignment
--     (solc: "Type string memory is not implicitly convertible to expected type
--     bytes memory"), while the EXPLICIT `bytes(s)` cast stays accepted;
--   * `==` on two `string` operands (solc: "Built-in binary operator == cannot
--     be applied to types string memory and string memory") — covered for
--     `bytes` by g3EqOnBytesRejected; this adds the `string` operand case.
-- ===========================================================================

def g12StringToBytesAssignFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    mutability := StateMutability.pure
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "s", ty := some Ty.string
             location := some DataLocation.memory }]
          (some (Expr.literal (Literal.string "hi")))
      , Stmt.varDecl
          [{ name := some "b", ty := some Ty.bytes
             location := some DataLocation.memory }]
          (some (Expr.ident "s"))
      , Stmt.returnValues (some (Expr.member (Expr.ident "b") "length")) ]) }

def badStringToBytesAssignRejected : Bool :=
  Result.isError
    (SourceUnit.check (su_singleContract "G12Assign" g12StringToBytesAssignFn))

-- Neighbor: the EXPLICIT `bytes(s)` cast stays accepted.
def g12ExplicitBytesCastFn : FunctionDecl :=
  { g12StringToBytesAssignFn with
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "s", ty := some Ty.string
             location := some DataLocation.memory }]
          (some (Expr.literal (Literal.string "hi")))
      , Stmt.varDecl
          [{ name := some "b", ty := some Ty.bytes
             location := some DataLocation.memory }]
          (some (Expr.call (Expr.typeName Ty.bytes)
            [Arg.positional (Expr.ident "s")]))
      , Stmt.returnValues (some (Expr.member (Expr.ident "b") "length")) ]) }

def explicitBytesCastAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "G12Cast" g12ExplicitBytesCastFn)

def g12EqStringFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "a", ty := Ty.string, location := some DataLocation.memory }
      , { name := some "b", ty := Ty.string
          location := some DataLocation.memory } ]
    returns := [{ name := none, ty := Ty.bool, location := none }]
    body :=
      some (Stmt.returnValues
        (some (Expr.binary BinaryOp.eq (Expr.ident "a") (Expr.ident "b")))) }

def badStringEqualityRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G12Eq" g12EqStringFn))

-- ===========================================================================
-- G13 — a HEX number literal combined with a unit denomination is REJECTED
-- (solc TypeChecker.cpp:3969-3975, error 5145: "Hexadecimal numbers cannot be
-- used with unit denominations. You can use an expression of the form
-- \"0x1234 * 1 days\" instead."). Confirmed with pinned solc 0.8.35:
-- `0x10 ether`, `0x2 wei`, `0x1 seconds`, `0x3 minutes` → all reject.
-- The guard lives in `parseUnitNumberRat?` (Interface.lean): a `0x`/`0X`-prefixed
-- literal text carrying a denomination folds to `none`. Neighbors that stay
-- ACCEPTED: any DECIMAL denomination (`1 ether`, `0.5 ether`, `2 days`), a plain
-- hex literal with NO denomination (`0x10`), and a hex literal inside an
-- EXPRESSION with a unit (`0x1234 * 1 days`, a binary op — not a single
-- denominated literal, so it never reaches the guard).
-- ===========================================================================

private def denomLiteralFn (text : String) (unit : UnitDenomination) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    body := some (Stmt.returnValues
      (some (Expr.literal (Literal.unitNumber text unit)))) }

private def plainNumberFn (text : String) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    body := some (Stmt.returnValues
      (some (Expr.literal (Literal.number text)))) }

-- `0x1234 * 1 days`: a binary op, NOT a hex-literal-with-denomination.
private def hexTimesDaysFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    body := some (Stmt.returnValues
      (some (Expr.binary BinaryOp.mul
        (Expr.literal (Literal.number "0x1234"))
        (Expr.literal (Literal.unitNumber "1" UnitDenomination.days))))) }

def badHexEtherLiteralRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "G13HexEther" (denomLiteralFn "0x10" UnitDenomination.ether)))

def badHexWeiLiteralRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "G13HexWei" (denomLiteralFn "0x2" UnitDenomination.wei)))

def badHexSecondsLiteralRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "G13HexSeconds" (denomLiteralFn "0x1" UnitDenomination.seconds)))

def hexDenomNeighborsAccepted : Bool :=
  -- Decimal denominations, plain hex, and hex-in-an-expression stay accepted.
  sourceUnitAccepted? (su_singleContract "G13OneEther"
      (denomLiteralFn "1" UnitDenomination.ether)) &&
    sourceUnitAccepted? (su_singleContract "G13HalfEther"
      (denomLiteralFn "0.5" UnitDenomination.ether)) &&
    sourceUnitAccepted? (su_singleContract "G13TwoDays"
      (denomLiteralFn "2" UnitDenomination.days)) &&
    sourceUnitAccepted? (su_singleContract "G13PlainHex"
      (plainNumberFn "0x10")) &&
    sourceUnitAccepted? (su_singleContract "G13HexTimesDays" hexTimesDaysFn)

-- ===========================================================================
-- G14 — a constant `/` or `%` whose operands are BOTH number literals and whose
-- divisor folds to ZERO is REJECTED at compile time (solc TypeChecker.cpp:
-- 1709-1712, Error 2271: "Built-in binary operator / cannot be applied to types
-- int_const 1 and int_const 0"; folding `RationalNumberType` division/modulo by
-- zero returns null). Confirmed with pinned solc 0.8.35: `1/0`, `5%0` → reject.
-- The guard lives in the div/mod arm of `checkExpr` (TypeCheck.lean): when both
-- operands fold via `numberLiteralRat?` and the divisor is zero, reject.
-- Neighbors that stay ACCEPTED: a constant `/`/`%` by a NON-zero divisor
-- (`4/2 = 2`, `5%3 = 2`), and a RUNTIME divide-by-zero `a/0` (a non-constant
-- dividend → fold `none` → still a runtime Panic 0x12, NOT a compile reject).
-- ===========================================================================

private def constBinOpReturnFn (op : BinaryOp) (a b : String) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    body := some (Stmt.returnValues
      (some (Expr.binary op (numberExpr a) (numberExpr b)))) }

private def runtimeDivByZeroFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := su_uint256, location := none }]
    body := some (Stmt.returnValues
      (some (Expr.binary BinaryOp.div (Expr.ident "a") (numberExpr "0")))) }

def badConstDivByZeroRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "G14Div" (constBinOpReturnFn BinaryOp.div "1" "0")))

def badConstModByZeroRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "G14Mod" (constBinOpReturnFn BinaryOp.mod "5" "0")))

def constDivModNeighborsAccepted : Bool :=
  -- Non-zero constant divisor folds; a runtime divide-by-zero stays accepted.
  sourceUnitAccepted? (su_singleContract "G14Div42"
      (constBinOpReturnFn BinaryOp.div "4" "2")) &&
    sourceUnitAccepted? (su_singleContract "G14Mod53"
      (constBinOpReturnFn BinaryOp.mod "5" "3")) &&
    sourceUnitAccepted? (su_singleContract "G14RuntimeDiv" runtimeDivByZeroFn)

-- ===========================================================================
-- G15 — a bare variable-declaration statement may NOT be the single-statement
-- body of an `if`/`else` branch, a `while`/`do-while` body, or a `for` body
-- (solc SyntaxChecker.cpp:217-249, Error 9079: "Variable declarations can only
-- be used inside blocks."). Confirmed with pinned solc 0.8.35 for all five
-- positions. The guard lives in the `ifElse`/`whileLoop`/`doWhile`/`forLoop`
-- arms of `checkStmt` via `Stmt.isBareVarDecl`. Neighbors that stay ACCEPTED:
-- a BRACED body `if (true) { uint x = 1; }` (a `Stmt.block`, not a bare
-- `Stmt.varDecl`), and a variable declaration in the `for` INIT position
-- (`for (uint i = 0; …)`), which solc explicitly allows.
-- ===========================================================================

private def uintXDecl : Stmt :=
  Stmt.varDecl [{ name := some "x", ty := some su_uint256, location := none }]
    (some (numberExpr "1"))

private def cfVoidFn (body : Stmt) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := []
    body := some (Stmt.block [body]) }

def badIfVarDeclBodyRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G15If"
    (cfVoidFn (Stmt.ifElse (boolExpr true) uintXDecl none))))

def badElseVarDeclBodyRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G15Else"
    (cfVoidFn (Stmt.ifElse (boolExpr true) (Stmt.block []) (some uintXDecl)))))

def badWhileVarDeclBodyRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G15While"
    (cfVoidFn (Stmt.whileLoop (boolExpr true) uintXDecl))))

def badDoWhileVarDeclBodyRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G15DoWhile"
    (cfVoidFn (Stmt.doWhile uintXDecl (boolExpr true)))))

def badForVarDeclBodyRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "G15For"
    (cfVoidFn (Stmt.forLoop none (some (boolExpr true)) none uintXDecl))))

private def forInitVarDeclFn : FunctionDecl :=
  -- `for (uint i = 0; false; ) { }` — vardecl in the INIT, block body: accepts.
  cfVoidFn (Stmt.forLoop
    (some (Stmt.varDecl
      [{ name := some "i", ty := some su_uint256, location := none }]
      (some (numberExpr "0"))))
    (some (boolExpr false)) none (Stmt.block []))

def varDeclBodyNeighborsAccepted : Bool :=
  -- A braced vardecl body and a for-init vardecl stay accepted.
  sourceUnitAccepted? (su_singleContract "G15Braced"
      (cfVoidFn (Stmt.ifElse (boolExpr true) (Stmt.block [uintXDecl]) none))) &&
    sourceUnitAccepted? (su_singleContract "G15ForInit" forInitVarDeclFn)
-- #109 COMMON-TYPE-LITERAL-MOBILE — the common type of a narrow typed operand
-- and an untyped number LITERAL that does NOT fit it is
-- `commonType(narrow, literal->mobileType())` (`Types.cpp:286`), i.e. the
-- literal's SMALLEST-fitting `uintN`/`intN` (300 ↦ uint16) — NOT uint256. So
-- `uint8 a + 300` really is `uint16` and solc ACCEPTS returning it as uint16
-- (the model formerly typed it uint256 and over-rejected the return). The
-- widening applies ONLY on the binary-operator common-type path: a plain
-- assignment `uint8 x = 300` is a fit check that still REJECTS.
-- ===========================================================================

-- `function f(uint8 a) public pure returns (uint16) { return a + 300; }`
private def commonTypeLiteralAddFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := Solidity.Ty.uint 8 }]
    returns := [{ name := none, ty := Solidity.Ty.uint 16 }]
    body := some (Stmt.returnValues
      (some (Expr.binary BinaryOp.add
        (Expr.ident "a") (numberExpr "300")))) }

-- `function f(uint8 a) public pure { uint8 x = 300; }` — a non-fitting literal
-- assigned to a narrow variable is a fit check (`isImplicitlyConvertibleTo`),
-- NOT the mobile-type common-type widening; solc REJECTS it and so must we.
private def commonTypeLiteralAssignFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := Solidity.Ty.uint 8 }]
    returns := []
    body := some (Stmt.varDecl
      [{ name := some "x", ty := some (Solidity.Ty.uint 8) }]
      (some (numberExpr "300"))) }

def commonTypeLiteralAddReturnsU16Accepted : Bool :=
  sourceUnitAccepted? (su_singleContract "CTL109Add" commonTypeLiteralAddFn)

def commonTypeLiteralNarrowAssignRejected : Bool :=
  Result.isError (SourceUnit.check
    (su_singleContract "CTL109Assign" commonTypeLiteralAssignFn))

-- #111 NEG-LITERAL-COMMON-TYPE — the NEGATIVE-literal sibling of #109. A negative
-- untyped number literal's `mobileType` is the smallest-fitting SIGNED intN
-- (`-300 ↦ int16`, `-1 ↦ int8`; `RationalNumberType::mobileType`,
-- `Types.cpp:1210`). `Type::commonType` (`Types.cpp:286`) is
-- `commonType(typed, literal->mobileType())`, and
-- `IntegerType::isImplicitlyConvertibleTo` (`Types.cpp:611-614`) forbids ALL
-- implicit signed↔unsigned conversions. So an UNSIGNED operand with a negative
-- literal has NO common type and solc REJECTS `uint8 a * -300`
-- ("Built-in binary operator * cannot be applied to types uint8 and
-- int_const -300"), while a SIGNED operand shares the common type and solc
-- ACCEPTS `int16 a * -300` (typed int16). The model already matches: the A1
-- rule (`Ty.canImplicitlyConvert` rejects signed↔unsigned) composed with the
-- #109 mobile-type widening (`untypedLiteralMobileTy?` sees through unary neg to
-- `int16`) makes `commonImplicit? uint8 int16 = none` → arithmetic type error.
-- ===========================================================================

-- `function f(uint8 a) pure returns (int256) { return a <op> <negLit>; }`
private def negLitCommonTypeUnsignedFn
    (op : BinaryOp) (litOnLeft : Bool := false) (paramTy : Solidity.Ty)
    (lit : String := "300") : FunctionDecl :=
  let a := Expr.ident "a"
  let l := Expr.unary UnaryOp.neg (numberExpr lit)
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := paramTy }]
    returns := [{ name := none, ty := Solidity.Ty.int 256 }]
    body := some (Stmt.returnValues (some
      (if litOnLeft then Expr.binary op l a else Expr.binary op a l))) }

-- (a) crux: uint8 operand × negative literal → REJECT (no common type).
def negLitCommonTypeUnsignedMulRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "NL111UMul"
    (negLitCommonTypeUnsignedFn BinaryOp.mul (paramTy := Solidity.Ty.uint 8))))

-- Siblings that all REJECT for the same reason (unsigned + negative literal):
--   uint16 × -300, -300 × uint8 (literal on left), uint8 + -300, uint8 × -1.
def negLitCommonTypeUnsignedSiblingsRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "NL111U16Mul"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (paramTy := Solidity.Ty.uint 16)))) &&
    Result.isError (SourceUnit.check (su_singleContract "NL111ULeft"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (litOnLeft := true)
        (paramTy := Solidity.Ty.uint 8)))) &&
    Result.isError (SourceUnit.check (su_singleContract "NL111UAdd"
      (negLitCommonTypeUnsignedFn BinaryOp.add (paramTy := Solidity.Ty.uint 8)))) &&
    Result.isError (SourceUnit.check (su_singleContract "NL111UNeg1"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (paramTy := Solidity.Ty.uint 8)
        (lit := "1"))))

-- Neighbors that MUST stay ACCEPTED (signed operand shares the common type):
--   int16 × -300 (int16), int8 × -1 (int8), -300 × int16 (int16).
def negLitCommonTypeSignedNeighborsAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "NL111I16Mul"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (paramTy := Solidity.Ty.int 16))) &&
    sourceUnitAccepted? (su_singleContract "NL111I8Neg1"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (paramTy := Solidity.Ty.int 8)
        (lit := "1"))) &&
    sourceUnitAccepted? (su_singleContract "NL111ILeft"
      (negLitCommonTypeUnsignedFn BinaryOp.mul (litOnLeft := true)
        (paramTy := Solidity.Ty.int 16)))

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard badConstDivByZeroRejected
#guard badConstModByZeroRejected
#guard constDivModNeighborsAccepted
#guard badIfVarDeclBodyRejected
#guard badElseVarDeclBodyRejected
#guard badWhileVarDeclBodyRejected
#guard badDoWhileVarDeclBodyRejected
#guard badForVarDeclBodyRejected
#guard varDeclBodyNeighborsAccepted

-- DUP-EVENT-SIBLING — two SIBLING base contracts that each declare an event
-- with the SAME name and SAME ABI parameter types clash even when the derived
-- contract declares no event of its own. solc
-- `ContractLevelChecker::checkDuplicateEvents` (error 5883, "Event with same
-- name and parameter types defined twice") collects events from the WHOLE
-- linearized base list into a name-keyed multimap and flags any two whose
-- external-callable parameters are equal. Indexed-ness is NOT part of the
-- comparison (`event E(uint indexed)` vs `event E(uint)` still clash), and the
-- comparison is over ABI TYPES only. Confirmed against pinned solc 0.8.35:
--   contract A{event E(uint);} contract B{event E(uint);} contract C is A,B{}
--     → REJECT 5883; the indexed variant → REJECT 5883 too.
-- The tightening runs `EventSigs.ensureNoDuplicateAbiSignatures` over
-- `inheritedEventSigs` (drawn from `drop 1 dispatchOrder`, the C3 linearization
-- with each base appearing exactly once). Neighbors that stay ACCEPTED:
--   * DIAMOND — a single event reached via two paths
--     (`contract Z{event E(uint);} A is Z; B is Z; C is A,B`) appears once in
--     the linearization, so it does NOT self-clash (solc accepts); and
--   * two sibling events sharing a name but with DIFFERENT ABI types
--     (`event E(uint)` vs `event E(bool)`) — no clash (solc accepts).
-- (The analogous sibling clash for ERRORS / state vars / structs / enums is a
-- SEPARATE, broader mechanism — solc's name-resolution "Identifier already
-- declared" — not this event ABI-signature check; it remains a distinct gap.)
-- ===========================================================================

private def dupEventItem (ty : Solidity.Ty) (indexed : Bool := false) :
    Solidity.ContractItem :=
  Solidity.ContractItem.eventDecl
    { name := "E", params := [{ name := none, ty := ty, indexed := indexed }] }

private def dupEventBase (name : Name) (item : Solidity.ContractItem)
    (bases : List Name := []) : Solidity.ContractDecl :=
  { name := name
    bases := bases.map (fun b => { base := userPath b })
    items := [item] }

private def dupEventEmpty (name : Name) (bases : List Name) :
    Solidity.ContractDecl :=
  { name := name, bases := bases.map (fun b => { base := userPath b }) }

private def dupEventSU (cs : List Solidity.ContractDecl) : Solidity.SourceUnit :=
  { items := cs.map SourceItem.contract }

-- (a) sibling bases each `event E(uint)`, derived declares nothing → REJECT.
def dupEventSiblingRejected : Bool :=
  Result.isError (SourceUnit.check (dupEventSU
    [ dupEventBase "DupEvA" (dupEventItem su_uint256)
    , dupEventBase "DupEvB" (dupEventItem su_uint256)
    , dupEventEmpty "DupEvC" ["DupEvA", "DupEvB"] ]))

-- (c) indexed vs non-indexed, same ABI type → still REJECT (indexed ignored).
def dupEventSiblingIndexedRejected : Bool :=
  Result.isError (SourceUnit.check (dupEventSU
    [ dupEventBase "DupEvIxA" (dupEventItem su_uint256 (indexed := true))
    , dupEventBase "DupEvIxB" (dupEventItem su_uint256)
    , dupEventEmpty "DupEvIxC" ["DupEvIxA", "DupEvIxB"] ]))

-- Neighbors that MUST stay accepted:
--   (b) diamond: one event reached via two paths — no self-clash;
--   (d) same name but different ABI parameter types — no clash.
def dupEventSiblingNeighborsAccepted : Bool :=
  sourceUnitAccepted? (dupEventSU
      [ dupEventBase "DupEvDZ" (dupEventItem su_uint256)
      , dupEventEmpty "DupEvDA" ["DupEvDZ"]
      , dupEventEmpty "DupEvDB" ["DupEvDZ"]
      , dupEventEmpty "DupEvDC" ["DupEvDA", "DupEvDB"] ]) &&
    sourceUnitAccepted? (dupEventSU
      [ dupEventBase "DupEvTA" (dupEventItem su_uint256)
      , dupEventBase "DupEvTB" (dupEventItem Solidity.Ty.bool)
      , dupEventEmpty "DupEvTC" ["DupEvTA", "DupEvTB"] ])

-- ===========================================================================
-- INHERITED-IDENTIFIER-CLASH — a contract inheriting from two (or more) SIBLING
-- bases that each declare a NON-OVERLOADABLE identifier of the SAME NAME is
-- REJECTED, even when the derived contract declares nothing of its own. Unlike
-- the event case above (ABI-signature-based, error 5883), this is solc's general
-- NAME-based name-resolution clash (error 9097 "Identifier already declared",
-- `DeclarationContainer::conflictingDeclaration`, DeclarationContainer.cpp:35).
-- It is name-based, NOT signature-based: `error E(uint)` in A and
-- `error E(address)` in B still clash. Confirmed against pinned solc 0.8.35:
--   contract A{error E(uint);}  contract B{error E(address);} contract C is A,B{}  → 9097
--   contract A{uint x;}         contract B{bool x;}           contract C is A,B{}  → 9097
--   contract A{struct S{uint a;}} contract B{struct S{bool b;}} contract C is A,B{} → 9097
--   contract A{enum E{X}}       contract B{enum E{Y}}         contract C is A,B{}  → 9097
--   contract A{error Foo();}    contract B{uint Foo;}         contract C is A,B{}  → 9097 (cross-kind)
--   contract A{event Foo();}    contract B{error Foo();}      contract C is A,B{}  → 9097 (cross-kind)
--   contract A{function f()public{}} contract B{uint f;}      contract C is A,B{}  → 9097 (cross-kind)
--   contract A{function f()public{}} contract B{event f();}   contract C is A,B{}  → 9097 (func-vs-event)
-- The overloadable exception: two FUNCTIONS or two EVENTS may share a name across
-- bases (function overloading; duplicate-signature events are the separate 5883
-- check). PRIVATE base members are not inherited into the derived scope, so they
-- do not participate (verified: private func/state-var foo vs sibling error foo
-- both ACCEPT). Neighbors that MUST stay accepted:
--   * DIAMOND — a single declaration reached via two paths
--     (`Z{error E;} A is Z; B is Z; C is A,B`) appears once in the C3
--     linearization, so it does NOT self-clash (verified ACCEPT for error / state
--     var / struct / enum); and
--   * legal function/event overloading across bases; and
--   * distinct names across bases.
-- The tightening runs `checkNoInheritedSiblingIdentifierClashes` (name-based)
-- over the inherited non-overloadable / function / event name lists gathered from
-- `ancestorPaths` / `inheritedContracts` (each base once).
-- ===========================================================================

private def icErr (n : Name) (ty : Solidity.Ty) : Solidity.ContractItem :=
  Solidity.ContractItem.errorDecl
    { name := n, params := [{ name := none, ty := ty, location := none }] }
private def icSv (n : Name) (ty : Solidity.Ty) : Solidity.ContractItem :=
  Solidity.ContractItem.stateVar { name := n, ty := ty }
private def icStruct (n : Name) (fn : Name) (ty : Solidity.Ty) :
    Solidity.ContractItem :=
  Solidity.ContractItem.structDecl { name := n, fields := [{ name := fn, ty := ty }] }
private def icEnum (n : Name) (c : Name) : Solidity.ContractItem :=
  Solidity.ContractItem.enumDecl { name := n, cases := [c] }
private def icEvent (n : Name) (ty : Solidity.Ty) : Solidity.ContractItem :=
  Solidity.ContractItem.eventDecl { name := n, params := [{ name := none, ty := ty }] }
private def icFunc (n : Name) : Solidity.ContractItem :=
  Solidity.ContractItem.function
    { name := some n, visibility := some Solidity.Visibility.public_,
      body := some (Solidity.Stmt.block []) }

private def icBase (name : Name) (items : List Solidity.ContractItem)
    (bases : List Name := []) : Solidity.ContractDecl :=
  { name := name, bases := bases.map (fun b => { base := userPath b }), items := items }
private def icSU (cs : List Solidity.ContractDecl) : Solidity.SourceUnit :=
  { items := cs.map SourceItem.contract }

-- (a) Non-overloadable sibling clashes, each kind → REJECT. Parameter/field
-- types deliberately DIFFER between the two bases to pin name-based (not
-- signature-based) collision.
def icErrorSiblingRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcErrA" [icErr "E" su_uint256]
    , icBase "IcErrB" [icErr "E" (Solidity.Ty.address false)]
    , icBase "IcErrC" [] ["IcErrA", "IcErrB"] ]))

def icStateVarSiblingRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcSvA" [icSv "x" su_uint256]
    , icBase "IcSvB" [icSv "x" Solidity.Ty.bool]
    , icBase "IcSvC" [] ["IcSvA", "IcSvB"] ]))

def icStructSiblingRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcStA" [icStruct "S" "a" su_uint256]
    , icBase "IcStB" [icStruct "S" "b" Solidity.Ty.bool]
    , icBase "IcStC" [] ["IcStA", "IcStB"] ]))

def icEnumSiblingRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcEnA" [icEnum "E" "X"]
    , icBase "IcEnB" [icEnum "E" "Y"]
    , icBase "IcEnC" [] ["IcEnA", "IcEnB"] ]))

-- (b) Cross-kind sibling clashes → REJECT.
def icErrorVsStateVarRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcXA" [icErr "Foo" su_uint256]
    , icBase "IcXB" [icSv "Foo" su_uint256]
    , icBase "IcXC" [] ["IcXA", "IcXB"] ]))

def icEventVsErrorRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcYA" [icEvent "Foo" su_uint256]
    , icBase "IcYB" [icErr "Foo" su_uint256]
    , icBase "IcYC" [] ["IcYA", "IcYB"] ]))

def icFuncVsStateVarRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcZA" [icFunc "Foo"]
    , icBase "IcZB" [icSv "Foo" su_uint256]
    , icBase "IcZC" [] ["IcZA", "IcZB"] ]))

def icFuncVsEventRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcWA" [icFunc "f"]
    , icBase "IcWB" [icEvent "f" su_uint256]
    , icBase "IcWC" [] ["IcWA", "IcWB"] ]))

-- (c) Transitive: a function inherited from a GRANDPARENT clashes with a
-- sibling's equally-named error → REJECT (scope is the whole linearization).
def icGrandparentFuncVsSiblingErrorRejected : Bool :=
  Result.isError (SourceUnit.check (icSU
    [ icBase "IcGZ" [icFunc "f"]
    , icBase "IcGA" [] ["IcGZ"]
    , icBase "IcGB" [icErr "f" su_uint256]
    , icBase "IcGC" [] ["IcGA", "IcGB"] ]))

-- Neighbors that MUST stay accepted.
--   (d) diamond single-declaration reached via two paths — error / state var /
--       struct / enum — no self-clash.
def icDiamondNeighborsAccepted : Bool :=
  sourceUnitAccepted? (icSU
      [ icBase "IcDErrZ" [icErr "E" su_uint256]
      , icBase "IcDErrA" [] ["IcDErrZ"]
      , icBase "IcDErrB" [] ["IcDErrZ"]
      , icBase "IcDErrC" [] ["IcDErrA", "IcDErrB"] ]) &&
    sourceUnitAccepted? (icSU
      [ icBase "IcDSvZ" [icSv "x" su_uint256]
      , icBase "IcDSvA" [] ["IcDSvZ"]
      , icBase "IcDSvB" [] ["IcDSvZ"]
      , icBase "IcDSvC" [] ["IcDSvA", "IcDSvB"] ]) &&
    sourceUnitAccepted? (icSU
      [ icBase "IcDStZ" [icStruct "S" "a" su_uint256]
      , icBase "IcDStA" [] ["IcDStZ"]
      , icBase "IcDStB" [] ["IcDStZ"]
      , icBase "IcDStC" [] ["IcDStA", "IcDStB"] ]) &&
    sourceUnitAccepted? (icSU
      [ icBase "IcDEnZ" [icEnum "E" "X"]
      , icBase "IcDEnA" [] ["IcDEnZ"]
      , icBase "IcDEnB" [] ["IcDEnZ"]
      , icBase "IcDEnC" [] ["IcDEnA", "IcDEnB"] ])

--   (e) legal overloading across bases (functions with distinct names, events
--       with different signatures) and distinct sibling names — no clash.
def icOverloadNeighborsAccepted : Bool :=
  sourceUnitAccepted? (icSU
      [ icBase "IcOfA" [icFunc "f"]
      , icBase "IcOfB" [icFunc "g"]
      , icBase "IcOfC" [] ["IcOfA", "IcOfB"] ]) &&
    sourceUnitAccepted? (icSU
      [ icBase "IcOeA" [icEvent "E" su_uint256]
      , icBase "IcOeB" [icEvent "E" Solidity.Ty.bool]
      , icBase "IcOeC" [] ["IcOeA", "IcOeB"] ]) &&
    sourceUnitAccepted? (icSU
      [ icBase "IcOdA" [icErr "E1" su_uint256]
      , icBase "IcOdB" [icErr "E2" su_uint256]
      , icBase "IcOdC" [] ["IcOdA", "IcOdB"] ])

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard icErrorSiblingRejected
#guard icStateVarSiblingRejected
#guard icStructSiblingRejected
#guard icEnumSiblingRejected
#guard icErrorVsStateVarRejected
#guard icEventVsErrorRejected
#guard icFuncVsStateVarRejected
#guard icFuncVsEventRejected
#guard icGrandparentFuncVsSiblingErrorRejected
#guard icDiamondNeighborsAccepted
#guard icOverloadNeighborsAccepted
#guard dupEventSiblingRejected
#guard dupEventSiblingIndexedRejected
#guard dupEventSiblingNeighborsAccepted
-- #107 TRY-RETURNS-EXACT-TYPE — in `try C.g() returns (T x, ...) { } catch { }`
-- each returns-clause parameter type must EXACTLY EQUAL the corresponding
-- declared return type of the called function (solc TypeChecker.cpp:1011-1024,
-- endVisit(TryStatement), error 6509: "Invalid type, expected <ret> but got
-- <clause>"; solc compares AST `Type` objects with `*type != *returnType`, i.e.
-- exact inequality — NOT implicit convertibility). Confirmed with pinned solc
-- 0.8.35:
--   * g returns uint8, clause `uint256 x`  -> REJECT 6509 (widening)
--   * g returns uint256, clause `uint8 x`  -> REJECT 6509 (narrowing)
--   * g returns uint8, clause `uint8 x`    -> ACCEPT (exact)
--   * g returns uint256, clause `uint x`   -> ACCEPT (`uint` == `uint256`, same
--     `Ty.uint 256`; the AST normalises both, so exact equality holds)
--   * g returns `uint[] memory`, clause `uint[] memory a` -> ACCEPT (a `calldata`
--     clause is rejected earlier by a data-location check, error path unrelated)
--   * multi-return exact match (uint8, address) -> ACCEPT
-- The model previously used implicit convertibility (`expectAssignableToTys`),
-- accepting the widening/narrowing cases; the fix
-- (`CheckedExpr.expectExactlyEqualToTys`) tightens the per-element comparison to
-- exact `Ty` equality while keeping the arity check (solc error 2800) untouched.
-- ===========================================================================

private def t107GFn (gReturns : List Parameter) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    visibility := some Visibility.external_
    mutability := StateMutability.view
    returns := gReturns
    body := some (Stmt.block []) }

private def t107FFn (clause : List Parameter) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    visibility := some Visibility.public_
    mutability := StateMutability.nonpayable
    returns := []
    body := some (Stmt.block
      [ Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "this") "g") [])
          clause
          (Stmt.block [])
          [CatchClause.clause none [] (Stmt.block [])] ]) }

private def t107Contract (gReturns clause : List Parameter) : SourceUnit :=
  { items := [ SourceItem.contract
      { name := "C"
        items := [ ContractItem.function (t107FFn clause)
                 , ContractItem.function (t107GFn gReturns) ] } ] }

-- Parameter builders (return params are unnamed; clause params bind a name).
private def t107Ret (ty : Ty) (loc : Option DataLocation := none) : Parameter :=
  { name := none, ty := ty, location := loc }
private def t107Clause (nm : Name) (ty : Ty) (loc : Option DataLocation := none) :
    Parameter :=
  { name := some nm, ty := ty, location := loc }

private def t107U8 : Ty := Ty.uint 8
private def t107U256 : Ty := Ty.uint 256
private def t107Addr : Ty := Ty.address false
private def t107UArr : Ty := Ty.array (Ty.uint 256) none

-- Widening clause (uint8 return, uint256 clause) is REJECTED.
def try107WideningRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (t107Contract [t107Ret t107U8] [t107Clause "x" t107U256]))

-- Narrowing clause (uint256 return, uint8 clause) is REJECTED.
def try107NarrowingRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (t107Contract [t107Ret t107U256] [t107Clause "x" t107U8]))

-- Exact matches ACCEPT: uint8/uint8; uint256/uint256 (= `uint`); address/address;
-- `uint[] memory`/`uint[] memory`; and a multi-return (uint8, address) exact match.
def try107ExactMatchesAccepted : Bool :=
  sourceUnitAccepted?
      (t107Contract [t107Ret t107U8] [t107Clause "x" t107U8]) &&
    sourceUnitAccepted?
      (t107Contract [t107Ret t107U256] [t107Clause "x" t107U256]) &&
    sourceUnitAccepted?
      (t107Contract [t107Ret t107Addr] [t107Clause "x" t107Addr]) &&
    sourceUnitAccepted?
      (t107Contract
        [t107Ret t107UArr (some DataLocation.memory)]
        [t107Clause "a" t107UArr (some DataLocation.memory)]) &&
    sourceUnitAccepted?
      (t107Contract
        [t107Ret t107U8, t107Ret t107Addr]
        [t107Clause "x" t107U8, t107Clause "y" t107Addr])

-- A multi-return with ONE widening element must still REJECT (per-element exact).
def try107MultiWideningRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (t107Contract
        [t107Ret t107U8, t107Ret t107Addr]
        [t107Clause "x" t107U256, t107Clause "y" t107Addr]))

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard try107WideningRejected
#guard try107NarrowingRejected
#guard try107ExactMatchesAccepted
#guard try107MultiWideningRejected
-- ABI-DECODE — the second argument must be a TUPLE of types, and every
-- top-level decoded `address` component is coerced to `address payable`.
--
--   * Bare (non-parenthesized) single type `abi.decode(data, uint)` is REJECTED
--     (solc TypeError 6444, `TypeChecker.cpp:127-136`: "The second argument to
--     \"abi.decode\" has to be a tuple of types."). `(uint)` — a one-element
--     tuple — and `(uint, bool)` are ACCEPTED. (The importer preserves the
--     tuple wrapper for this argument, so `Expr.typeName` here can only mean the
--     rejected bare form.)
--   * Each top-level decoded `address` is forced to `address payable`
--     (`TypeChecker.cpp:150-152`), so it is assignable to an `address payable`
--     variable. Probed against pinned solc 0.8.35:
--       `address payable p = abi.decode(data, (address));`  compiles.
-- ===========================================================================

private def abiDecodeDataParam : Parameter :=
  { name := some "data", ty := Ty.bytes, location := some DataLocation.memory }

private def abiDecodeExpr (typesExpr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "decode")
    [Arg.positional (Expr.ident "data"), Arg.positional typesExpr]

private def abiDecodeStmtFn (body : Stmt) : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "f"
    params := [abiDecodeDataParam]
    returns := []
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    body := some (Stmt.block [body]) }

-- Bare single type `abi.decode(data, uint)` — REJECTED (error 6444).
def abiDecodeBareTypeRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "AbiDecodeBare"
    (abiDecodeStmtFn (Stmt.expr (abiDecodeExpr (Expr.typeName (Ty.uint 256)))))))

-- `(uint)` — one-element tuple — ACCEPTED.
def abiDecodeSingleTupleAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "AbiDecodeSingleTuple"
    (abiDecodeStmtFn (Stmt.expr (abiDecodeExpr
      (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 256))])))))

-- `(uint, bool)` — multi-element tuple — ACCEPTED.
def abiDecodeMultiTupleAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "AbiDecodeMultiTuple"
    (abiDecodeStmtFn (Stmt.expr (abiDecodeExpr
      (Expr.tuple
        [ TupleItem.value (Expr.typeName (Ty.uint 256))
        , TupleItem.value (Expr.typeName Ty.bool) ])))))

-- `address payable p = abi.decode(data, (address));` — ACCEPTED because the
-- decoded top-level `address` is coerced to `address payable`.
def abiDecodeAddressPayableAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "AbiDecodeAddrPayable"
    (abiDecodeStmtFn
      (Stmt.varDecl
        [{ name := some "p", ty := Ty.address true, location := none }]
        (some (abiDecodeExpr
          (Expr.tuple [TupleItem.value (Expr.typeName (Ty.address false))]))))))

-- ===========================================================================
-- #112 CREATE-SALT-LITERAL — the `new C{salt: e}(…)` salt option accepts any
-- value IMPLICITLY CONVERTIBLE to bytes32, not only a value already typed
-- bytes32. Per solc RationalNumberType::isImplicitlyConvertibleTo
-- (`Types.cpp` ~1035) an untyped number literal converts to a FixedBytesType
-- iff its value is 0 OR it is an exact-length hex literal matching the width.
-- Probed against pinned solc 0.8.35 (`--bin`):
--     salt: 0                        ACCEPT   (literal value 0)
--     salt: <32-byte hex literal>    ACCEPT   (exact bytes32-width hex)
--     salt: 5   / 256 / 0x01         REJECT   (nonzero, wrong-width)
-- The former strict `requireEqTy (bytesN 32)` over-rejected the two ACCEPTs.
-- (`salt: 1` rejection is already pinned by `literalSaltConstructorCreateRejected`
-- in `Witness/TypeCheck.lean`; here we pin the newly-accepted literals plus a
-- `salt: 5` neighbour so a future loosening cannot over-accept.)
-- ===========================================================================

def saltLiteralCreateSource (contractName : String)
    (saltExpr : Expr) : SourceUnit :=
  { items :=
      [ SourceItem.contract constructorTargetContract
      , SourceItem.contract
          { name := contractName
            items :=
              [ ContractItem.function
                  { constructorCreateFunction with
                    name := some "makeSaltLiteral"
                    body :=
                      some
                        (Stmt.block
                          [ Stmt.expr
                              (Expr.callWithOptions
                                (Expr.newExpr constructorTargetTy [])
                                [saltOption saltExpr]
                                [Arg.named "seed" (numberExpr "7")])
                          , Stmt.returnValues (some (numberExpr "1")) ]) } ] } ] }

-- Integer literal `0` as salt — ACCEPTED.
def saltLiteralZeroAccepted : Bool :=
  sourceUnitAccepted?
    (saltLiteralCreateSource "SaltZeroCtorMaker" (numberExpr "0"))

-- Exact 32-byte hex literal as salt — ACCEPTED.
def saltLiteralHex32Accepted : Bool :=
  sourceUnitAccepted?
    (saltLiteralCreateSource "SaltHex32CtorMaker"
      (numberExpr
        "0x0000000000000000000000000000000000000000000000000000000000000001"))

-- Nonzero, non-width integer literal `5` as salt — REJECTED (no over-accept).
def saltLiteralFiveRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (saltLiteralCreateSource "SaltFiveCtorMaker" (numberExpr "5")))

def createSaltLiteralAcceptanceMatches : Bool :=
  saltLiteralZeroAccepted &&
    saltLiteralHex32Accepted &&
    saltLiteralFiveRejected

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard saltLiteralZeroAccepted
#guard saltLiteralHex32Accepted
#guard saltLiteralFiveRejected
#guard abiDecodeBareTypeRejected
#guard abiDecodeSingleTupleAccepted
#guard abiDecodeMultiTupleAccepted
#guard abiDecodeAddressPayableAccepted
#guard badInternalPayableRejected
#guard badPrivatePayableRejected
#guard g11PayableNeighborsAccepted
#guard badStringToBytesAssignRejected
#guard explicitBytesCastAccepted
#guard badStringEqualityRejected
#guard badHexEtherLiteralRejected
#guard badHexWeiLiteralRejected
#guard badHexSecondsLiteralRejected
#guard hexDenomNeighborsAccepted
#guard commonTypeLiteralAddReturnsU16Accepted
#guard commonTypeLiteralNarrowAssignRejected
#guard negLitCommonTypeUnsignedMulRejected
#guard negLitCommonTypeUnsignedSiblingsRejected
#guard negLitCommonTypeSignedNeighborsAccepted
-- #110 QUALIFIED-STRUCT-CONSTRUCTION — constructing a struct through a type-name
-- qualifier where the struct is defined in ANOTHER (non-inherited) contract or a
-- library resolves to that struct's constructor exactly as an unqualified
-- in-scope struct name would (solc: FunctionCall with
-- FunctionType::Kind::StructConstructor; a MemberAccess to a struct type in
-- another contract/library yields a TypeType whose constructor is callable).
-- Probed against pinned solc 0.8.35 — all ACCEPT:
--   library L{struct P{uint x;uint y;}} …  L.P(1,2) / L.P({y:20,x:10})
--   contract Defs{struct Q{uint a;uint b;}} (NOT inherited) …  Defs.Q(4,5) / Defs.Q({a:1,b:2})
-- and all REJECT (must not over-accept):
--   wrong arity      A.S(1)            (error: wrong argument count)
--   wrong field name A.S({x:1,z:2})    (error: named argument does not match)
--   wrong arg type   A.S(true,2)       (error: invalid implicit conversion)
-- The qualified struct name imports as `Expr.typeName (Ty.user {segments:=[A,S]})`
-- (the type-expression MemberAccess collapse from #102), and the struct-
-- constructor arm resolves it via `lookupStruct?` on the qualified path, so no
-- model change was needed; these witnesses lock the behavior in.
-- ===========================================================================

private def qsLib : ContractDecl :=
  { kind := ContractKind.library, name := "QsLib"
    items := [ContractItem.structDecl
      { name := "P"
        fields := [{ name := "x", ty := su_uint256 }
                 , { name := "y", ty := su_uint256 }] }] }

private def qsDefs : ContractDecl :=
  { name := "QsDefs"
    items := [ContractItem.structDecl
      { name := "Q"
        fields := [{ name := "a", ty := su_uint256 }
                 , { name := "b", ty := su_uint256 }] }] }

-- A function `f` that does `<path> memory s = <path>(args); return s.f1 + s.f2;`.
private def qsFn (path : List Name) (args : List Arg) (f1 f2 : Name) :
    FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "s", ty := Ty.user { segments := path }
           , location := some DataLocation.memory }]
          (some (Expr.call (Expr.typeName (Ty.user { segments := path })) args))
      , Stmt.returnValues (some (Expr.binary BinaryOp.add
          (Expr.member (Expr.ident "s") f1) (Expr.member (Expr.ident "s") f2))) ]) }

private def qsSU (fn : FunctionDecl) : SourceUnit :=
  { items := [ SourceItem.contract qsLib
             , SourceItem.contract qsDefs
             , SourceItem.contract { name := "QsT", items := [ContractItem.function fn] } ] }

private def qsPathP : List Name := ["QsLib", "P"]
private def qsPathQ : List Name := ["QsDefs", "Q"]

-- Library-scoped and contract-scoped, positional and named — all ACCEPT.
def qstructQualifiedConstructionAccepted : Bool :=
  sourceUnitAccepted? (qsSU (qsFn qsPathP
      [Arg.positional (numberExpr "1"), Arg.positional (numberExpr "2")] "x" "y")) &&
    sourceUnitAccepted? (qsSU (qsFn qsPathP
      [Arg.named "y" (numberExpr "20"), Arg.named "x" (numberExpr "10")] "x" "y")) &&
    sourceUnitAccepted? (qsSU (qsFn qsPathQ
      [Arg.positional (numberExpr "4"), Arg.positional (numberExpr "5")] "a" "b")) &&
    sourceUnitAccepted? (qsSU (qsFn qsPathQ
      [Arg.named "a" (numberExpr "100"), Arg.named "b" (numberExpr "200")] "a" "b"))

-- Wrong arity `QsLib.P(1)` — REJECTED (solc: wrong argument count).
def qstructWrongArityRejected : Bool :=
  Result.isError (SourceUnit.check (qsSU (qsFn qsPathP
    [Arg.positional (numberExpr "1")] "x" "y")))

-- Wrong field name `QsLib.P({x:1,z:2})` — REJECTED (solc: named argument mismatch).
def qstructWrongFieldNameRejected : Bool :=
  Result.isError (SourceUnit.check (qsSU (qsFn qsPathP
    [Arg.named "x" (numberExpr "1"), Arg.named "z" (numberExpr "2")] "x" "y")))

-- Wrong argument type `QsLib.P(true,2)` — REJECTED (solc: bad implicit conversion).
def qstructWrongTypeRejected : Bool :=
  Result.isError (SourceUnit.check (qsSU (qsFn qsPathP
    [Arg.positional (boolExpr true), Arg.positional (numberExpr "2")] "x" "y")))

-- ===========================================================================
-- CONST-GETTER-PURE-OVERRIDE (#115) — a `public constant` state variable's
-- synthesized getter has state mutability PURE (not view), so it CAN override
-- a `pure` interface/base function (solc `Types.cpp`
-- `OverrideProxy::stateMutability()`: `isConstant() ? Pure : View`). A plain
-- (non-constant) public state var's getter is VIEW and CANNOT override a pure
-- base — that over-accept guard must stay closed.
-- ===========================================================================

private def cgPureInterface : ContractDecl :=
  { name := "CgI"
    kind := ContractKind.interface
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "X"
            returns := [{ name := none, ty := su_uint256, location := none }]
            visibility := some Visibility.external_
            mutability := StateMutability.pure
            body := none } ] }

private def cgViewInterface : ContractDecl :=
  { name := "CgI"
    kind := ContractKind.interface
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "X"
            returns := [{ name := none, ty := su_uint256, location := none }]
            visibility := some Visibility.external_
            mutability := StateMutability.view
            body := none } ] }

private def cgGetterContract (varMut : VarMutability) (init? : Option Expr) :
    ContractDecl :=
  { name := "CgC"
    bases := [{ base := userPath "CgI" }]
    items :=
      [ ContractItem.stateVar
          { name := "X"
            ty := su_uint256
            visibility := some Visibility.public_
            mutability := varMut
            override? := some {}
            init := init? } ] }

private def cgSourceUnit (iface getter : ContractDecl) : SourceUnit :=
  { items := [SourceItem.contract iface, SourceItem.contract getter] }

-- constant getter (PURE) overriding a pure base — ACCEPTED.
def cgConstOverPureAccepted : Bool :=
  sourceUnitAccepted?
    (cgSourceUnit cgPureInterface
      (cgGetterContract VarMutability.constant (some (numberExpr "5"))))

-- constant getter (PURE) overriding a view base — still ACCEPTED.
def cgConstOverViewAccepted : Bool :=
  sourceUnitAccepted?
    (cgSourceUnit cgViewInterface
      (cgGetterContract VarMutability.constant (some (numberExpr "5"))))

-- plain getter (VIEW) overriding a pure base — REJECTED (view ≠ pure). This is
-- the over-accept guard: the constant special-case must not leak to mutables.
def cgNonConstOverPureRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (cgSourceUnit cgPureInterface
        (cgGetterContract VarMutability.mutable none)))

-- plain getter (VIEW) overriding a view base — still ACCEPTED.
def cgNonConstOverViewAccepted : Bool :=
  sourceUnitAccepted?
    (cgSourceUnit cgViewInterface
      (cgGetterContract VarMutability.mutable none))

-- ===========================================================================
-- G#116 (TERNARY-STORAGE-STATELVALUE) — a `storage`-pointer local initialized
-- from a TERNARY of two storage state variables (`S storage p = b ? s0 : s1;`)
-- is ACCEPTED (solc `TypeChecker::visit(VariableDeclarationStatement)` gates the
-- pointer only on `isImplicitlyConvertibleTo`; a conditional of two storage
-- references is itself a storage reference). Formerly over-rejected because the
-- ternary CheckedExpr builder dropped the `stateLValue` marker. The genuinely
-- invalid MIXED-location form (`b ? m : s0` with `m` a memory struct → `S
-- storage`) has no common storage reference and stays REJECTED (matches pinned
-- solc: "… memory is not implicitly convertible to … storage pointer").
-- ===========================================================================

private def tsStruct : Solidity.Ty := Solidity.Ty.user (userPath "S")

private def tsStructItem : Solidity.ContractItem :=
  Solidity.ContractItem.structDecl
    { name := "S", fields := [{ name := "x", ty := su_uint256 }] }

private def tsStateVars : List Solidity.ContractItem :=
  [ Solidity.ContractItem.stateVar { name := "s0", ty := tsStruct }
  , Solidity.ContractItem.stateVar { name := "s1", ty := tsStruct } ]

private def tsContract (fn : Solidity.FunctionDecl) : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "TernStor"
          items := tsStructItem :: tsStateVars
            ++ [Solidity.ContractItem.function fn] }] }

private def tsPBinding : Solidity.VarBinding :=
  { name := some "p", ty := some tsStruct,
    location := some Solidity.DataLocation.storage }

-- ACCEPT: `S storage p = b ? s0 : s1; return p.x;`
private def tsAcceptFn : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "f"
    params := [{ name := some "b", ty := Solidity.Ty.bool, location := none }]
    returns := [{ name := none, ty := su_uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view
    body :=
      some (Solidity.Stmt.block
        [ Solidity.Stmt.varDecl [tsPBinding]
            (some (Solidity.Expr.ternary (Solidity.Expr.ident "b")
              (Solidity.Expr.ident "s0") (Solidity.Expr.ident "s1")))
        , Solidity.Stmt.returnValues
            (some (Solidity.Expr.member (Solidity.Expr.ident "p") "x")) ]) }

def ternaryStorageStateLValueAccepted : Bool :=
  sourceUnitAccepted? (tsContract tsAcceptFn)

-- REJECT (over-accept guard): a mixed-location ternary `b ? m : s0` where `m`
-- is a `memory` struct has no common storage reference, so it is NOT implicitly
-- convertible to `S storage p`.
private def tsRejectMixedFn : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "g"
    params :=
      [ { name := some "b", ty := Solidity.Ty.bool, location := none }
      , { name := some "m", ty := tsStruct,
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := su_uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view
    body :=
      some (Solidity.Stmt.block
        [ Solidity.Stmt.varDecl [tsPBinding]
            (some (Solidity.Expr.ternary (Solidity.Expr.ident "b")
              (Solidity.Expr.ident "m") (Solidity.Expr.ident "s0")))
        , Solidity.Stmt.returnValues
            (some (Solidity.Expr.member (Solidity.Expr.ident "p") "x")) ]) }

def ternaryStorageMixedLocationRejected : Bool :=
  Result.isError (SourceUnit.check (tsContract tsRejectMixedFn))

-- ACCEPT: the member-lvalue MUTATION target `(b ? s0 : s1).x = 5;` (solc accepts
-- — member access on a storage conditional is an lvalue). Pins the typecheck
-- path that reads `stateLValue` through the ternary base.
private def tsMemberTargetFn : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "h"
    params := [{ name := some "b", ty := Solidity.Ty.bool, location := none }]
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some (Solidity.Stmt.block
        [ Solidity.Stmt.expr
            (Solidity.Expr.assign
              (Solidity.Expr.member
                (Solidity.Expr.ternary (Solidity.Expr.ident "b")
                  (Solidity.Expr.ident "s0") (Solidity.Expr.ident "s1")) "x")
              Solidity.AssignOp.assign
              (Solidity.Expr.literal (Solidity.Literal.number "5"))) ]) }

def ternaryStorageMemberTargetAccepted : Bool :=
  sourceUnitAccepted? (tsContract tsMemberTargetFn)

#guard ternaryStorageStateLValueAccepted
#guard ternaryStorageMixedLocationRejected
#guard ternaryStorageMemberTargetAccepted

-- #117 FRAC-CMP-OVERACCEPT — solc 0.8.35 REJECTS every fractional-vs-fractional
-- literal comparison. Each fractional rational's mobile type is a FixedPointType
-- (Types.cpp:1234-1270); FixedPointType::binaryOperatorResult (Types.cpp:846-855)
-- yields no usable common type for a comparison (differing fractional-digit
-- counts have none, the same-count path is "Not yet implemented - FixedPointType"),
-- and non-terminating fractions have no fixed mobile type at all ("cannot be
-- applied to types rational_const ..."). Binary-confirmed reject: `0.5 < 0.25`,
-- `0.5 == 0.5`, `1/2 == 0.5`, `1/3 < 1/2`. The gate lives in the `<>≤≥`/`==!=`
-- arms of `checkExpr` via `numberComparisonFoldable?` → `comparisonFoldable`'s
-- both-fractional branch (`none, none => false`). Neighbors that stay ACCEPTED:
-- same-sign INTEGER literal comparisons (`1 < 2`, `3 == 3`), which fold to a bool
-- — the fix must not regress those into an over-reject.
-- ===========================================================================

private def cmpReturnBoolFn (body : Expr) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := none, ty := Ty.bool, location := none }]
    body := some (Stmt.returnValues (some body)) }

private def fracExpr (num den : String) : Expr :=
  Expr.binary BinaryOp.div (numberExpr num) (numberExpr den)

-- 0.5 < 0.25 — two terminating decimals: REJECT.
def fracCmpLtRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "FracLt"
    (cmpReturnBoolFn (Expr.binary BinaryOp.lt
      (numberExpr "0.5") (numberExpr "0.25")))))

-- 0.5 == 0.5 — equal terminating decimals: still REJECT.
def fracCmpEqRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "FracEq"
    (cmpReturnBoolFn (Expr.binary BinaryOp.eq
      (numberExpr "0.5") (numberExpr "0.5")))))

-- 1/2 == 0.5 — rational fraction vs decimal: REJECT.
def fracCmpMixedRatDecEqRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "FracRatDec"
    (cmpReturnBoolFn (Expr.binary BinaryOp.eq
      (fracExpr "1" "2") (numberExpr "0.5")))))

-- 1/3 < 1/2 — two non-terminating fractions: REJECT.
def fracCmpNonTermLtRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "FracNonTerm"
    (cmpReturnBoolFn (Expr.binary BinaryOp.lt
      (fracExpr "1" "3") (fracExpr "1" "2")))))

-- Over-reject guard: same-sign INTEGER literal comparisons still ACCEPT/fold.
def intCmpNeighborsAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "IntLt"
      (cmpReturnBoolFn (Expr.binary BinaryOp.lt
        (numberExpr "1") (numberExpr "2")))) &&
    sourceUnitAccepted? (su_singleContract "IntEq"
      (cmpReturnBoolFn (Expr.binary BinaryOp.eq
        (numberExpr "3") (numberExpr "3"))))

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard fracCmpLtRejected
#guard fracCmpEqRejected
#guard fracCmpMixedRatDecEqRejected
#guard fracCmpNonTermLtRejected
#guard intCmpNeighborsAccepted

-- CZB (#121 CONST-ZERO-BYTESN) — ANY constant expression that *folds to 0* is
-- implicitly convertible to any `bytesN` (solc
-- `RationalNumberType::isImplicitlyConvertibleTo`, Types.cpp:1035, the
-- `m_value == rational(0)` branch on the folded value). A nonzero fold does
-- NOT convert (over-accept guard); a two-candidate overload where the folded 0
-- matches BOTH `uint256` and `bytes32` is ambiguous → REJECTED.
-- ===========================================================================

-- `bytes32 x = 1-1; return x;` — the folded 0 converts to bytes32 → ACCEPTED.
def czbAssignZeroFoldFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "x", ty := some (Ty.bytesN 32)
                  location := none } ]
              (some
                (Expr.binary BinaryOp.sub (numberExpr "1") (numberExpr "1")))
          , Stmt.returnValues (some (Expr.ident "x")) ]) }

def czbAssignZeroFoldAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "CZBAssign" czbAssignZeroFoldFn)

-- `bytes32 x = 1+1;` — the folded 2 is NOT convertible to bytes32 → REJECTED
-- (over-accept guard: a nonzero fold must not leak through).
def czbAssignNonZeroFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "x", ty := some (Ty.bytesN 32)
                  location := none } ]
              (some
                (Expr.binary BinaryOp.add (numberExpr "1") (numberExpr "1")))
          , Stmt.returnValues (some (Expr.ident "x")) ]) }

def czbAssignNonZeroRejected : Bool :=
  Result.isError
    (SourceUnit.check (su_singleContract "CZBAssignNZ" czbAssignNonZeroFn))

-- Overloaded `g(uint256)` + `g(bytes32)`, call `g(1-1)`: the folded 0 matches
-- BOTH candidates → no unique declaration → REJECTED (mirror over-accept guard).
private def czbOverloadG (paramTy : Ty) (ret : String) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "g"
      params := [{ name := some "a", ty := paramTy, location := none }]
      returns := [{ name := none, ty := su_uint256, location := none }]
      visibility := some Visibility.public_
      mutability := StateMutability.pure
      body := some (Stmt.returnValues (some (numberExpr ret))) }

private def czbOverloadCaller : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "h"
      returns := [{ name := none, ty := su_uint256, location := none }]
      visibility := some Visibility.public_
      mutability := StateMutability.pure
      body :=
        some
          (Stmt.returnValues
            (some
              (Expr.call (Expr.ident "g")
                [ Arg.positional
                    (Expr.binary BinaryOp.sub
                      (numberExpr "1") (numberExpr "1")) ]))) }

def czbAmbiguousOverloadRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items :=
          [ SourceItem.contract
              { name := "CZBAmbig"
                items :=
                  [ czbOverloadG su_uint256 "1"
                  , czbOverloadG (Ty.bytesN 32) "2"
                  , czbOverloadCaller ] } ] })

-- ===========================================================================
-- #123 STRUCT-CYCLE-FUEL — a struct that reaches itself by value (through fixed
-- arrays / nested structs, i.e. WITHOUT a pointer = dynamic array or mapping) is
-- REJECTED ("Recursive struct definition.") for a by-value cycle of ANY length.
-- The detector previously used a fixed fuel of 64, so a by-value cycle of length
-- ≥ 65 escaped and was over-accepted. The fuel is now sized to an upper bound on
-- the by-value path cost (`sizeOf types.structs + 1`), catching cycles of any
-- length while a deep ACYCLIC chain still accepts (running out of fuel = accept;
-- the detector only flags a genuine return to the struct under check).
-- Over-accept only (solc emits no AST for the rejected program), so no Forge
-- lane — these #guards are the gate.
-- ===========================================================================

private def scCycleName (i : Nat) : Name := "SC" ++ toString i

-- N free structs S0..S(N-1) with S_i.f : S_((i+1) mod N) — a by-value cycle of
-- length N (every hop is a by-value nested struct, no pointer).
def structCycleByValueItems (n : Nat) : List Solidity.SourceItem :=
  (List.range n).map (fun i =>
    SourceItem.freeStruct
      { name := scCycleName i
        fields :=
          [ { name := "f"
              ty := Ty.user (userPath (scCycleName ((i + 1) % n))) } ] })

def structCycleByValue65Rejected : Bool :=
  Result.isError (SourceUnit.check { items := structCycleByValueItems 65 })

def structCycleByValue130Rejected : Bool :=
  Result.isError (SourceUnit.check { items := structCycleByValueItems 130 })

private def scChainName (i : Nat) : Name := "SA" ++ toString i

-- N free structs S0..S(N-1) forming a DEEP but ACYCLIC by-value chain: S_i.f :
-- S_(i+1), and the last one closes with a value type. Length 130 > 64 exercises
-- the key over-reject risk: the larger fuel must NOT false-positive here.
def structAcyclicChainItems (n : Nat) : List Solidity.SourceItem :=
  (List.range n).map (fun i =>
    SourceItem.freeStruct
      { name := scChainName i
        fields :=
          [ { name := "f"
              ty :=
                if i + 1 == n then su_uint256
                else Ty.user (userPath (scChainName (i + 1))) } ] })

def structAcyclicChain130Accepted : Bool :=
  sourceUnitAccepted? { items := structAcyclicChainItems 130 }

-- Short guards: direct by-value self-reference rejects; a dynamic-array
-- self-reference (a pointer) still accepts.
def structDirectSelfRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items :=
          [ SourceItem.freeStruct
              { name := "SCSelf"
                fields := [{ name := "f", ty := Ty.user (userPath "SCSelf") }] } ] })

def structDynArraySelfAccepted : Bool :=
  sourceUnitAccepted?
    { items :=
        [ SourceItem.freeStruct
            { name := "SCDyn"
              fields :=
                [ { name := "f"
                    ty := Ty.array (Ty.user (userPath "SCDyn")) none } ] } ] }

-- Build-time gate: pin every acceptance-boundary witness added here so a future
-- loosening cannot silently re-open them (`lake build` fails if any is false).
#guard structCycleByValue65Rejected
#guard structCycleByValue130Rejected
#guard structAcyclicChain130Accepted
#guard structDirectSelfRejected
#guard structDynArraySelfAccepted
#guard czbAssignZeroFoldAccepted
#guard czbAssignNonZeroRejected
#guard czbAmbiguousOverloadRejected
#guard qstructQualifiedConstructionAccepted
#guard qstructWrongArityRejected
#guard qstructWrongFieldNameRejected
#guard qstructWrongTypeRejected
#guard cgConstOverPureAccepted
#guard cgConstOverViewAccepted
#guard cgNonConstOverPureRejected
#guard cgNonConstOverViewAccepted

end Examples
end TypeCheck
end Solidity
end SolidCore
