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

end Examples
end TypeCheck
end Solidity
end SolidCore
