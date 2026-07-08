/-
Round-2 acceptance-boundary witnesses (2026-07-08) for the divergences E1, E2,
O1, PT1 (and the AE1 already-handled confirmation) from
`docs/solc-implementation-divergences-2.md`.

Each item pins BOTH sides of the boundary on the Lean side:
  * a program pinned-solc 0.8.35 REJECTS is now rejected by this typechecker
    (`…Rejected : Bool := Result.isError (SourceUnit.check …)`), and
  * a neighbor solc still ACCEPTS stays accepted (`…Accepted`,
    `sourceUnitAccepted? …`) — the tightening must not over-reject; and for the
    over-reject fix E2, the previously-rejected program is now accepted while the
    must-still-reject neighbor stays rejected.

Paired solc-REJECT `.sol` fixtures live under
`tests/forge-harness/acceptance-boundaries-round2/invalid/` and are compiled by
the differential harness to confirm pinned solc rejects them. Helpers
(`simpleReturnFunction`, `su_uint256`, `numberExpr`, `userPath`, `uintArrayTy`,
`SourceUnit.check`, `Result.isError`, `sourceUnitAccepted?`) come from
`SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- ===========================================================================
-- E1 — a NON-rational immutable read inside a `pure` function is REJECTED
-- (solc ViewPureChecker.cpp:194-199, TypeError 2527). Only a RationalNumber
-- initializer keeps the read Pure; keccak256/constant-ref/bool/conversion
-- initializers make it a View read. Neighbors: the same immutable read in a
-- `view` function, and a numeric-literal / constant-arithmetic immutable read
-- in `pure`, all still ACCEPT.
-- ===========================================================================

private def e1B32 : Ty := Ty.bytesN 32
private def e1KeccakInit : Expr :=
  Expr.call (Expr.ident "keccak256")
    [Arg.positional (Expr.literal (Literal.string "x"))]

private def e1ReadFn (sm : StateMutability) (retTy : Ty) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    mutability := sm
    returns := [{ name := none, ty := retTy, location := none }]
    body := some (Stmt.returnValues (some (Expr.ident "H"))) }

private def e1Contract (initExpr : Expr) (t : Ty)
    (sm : StateMutability) (retTy : Ty) : SourceUnit :=
  { items := [ SourceItem.contract
      { name := "C"
        items :=
          [ ContractItem.stateVar
              { name := "H", ty := t
                mutability := VarMutability.immutable, init := some initExpr }
          , ContractItem.function (e1ReadFn sm retTy) ] } ] }

def e1KeccakImmutableInPureRejected : Bool :=
  Result.isError
    (SourceUnit.check (e1Contract e1KeccakInit e1B32 StateMutability.pure e1B32))

def e1NeighborsAccepted : Bool :=
  -- same keccak immutable read in a VIEW function
  sourceUnitAccepted? (e1Contract e1KeccakInit e1B32 StateMutability.view e1B32) &&
    -- a numeric-literal immutable read in PURE stays pure (rational)
    sourceUnitAccepted?
      (e1Contract (numberExpr "5") su_uint256 StateMutability.pure su_uint256) &&
    -- constant-arithmetic immutable read in PURE stays pure (rational)
    sourceUnitAccepted?
      (e1Contract (Expr.binary BinaryOp.add (numberExpr "2") (numberExpr "3"))
        su_uint256 StateMutability.pure su_uint256)

-- ===========================================================================
-- E2 — `this.f.selector` in a `pure` function is now ACCEPTED (over-reject
-- fixed; solc ViewPureChecker.cpp:357-370 keeps it Pure). The must-still-reject
-- neighbor `this.f()` (an actual external call) stays a `pure`-violation.
-- ===========================================================================

private def e2FFn : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := su_uint256, location := none }]
    body := some (Stmt.returnValues (some (numberExpr "1"))) }

private def e2GFn (gBody : Expr) (gRet : Ty) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := gRet, location := none }]
    body := some (Stmt.returnValues (some gBody)) }

private def e2Contract (gBody : Expr) (gRet : Ty) : SourceUnit :=
  { items := [ SourceItem.contract
      { name := "C"
        items := [ ContractItem.function e2FFn
                 , ContractItem.function (e2GFn gBody gRet) ] } ] }

def e2ThisSelectorInPureAccepted : Bool :=
  sourceUnitAccepted?
    (e2Contract
      (Expr.member (Expr.member (Expr.ident "this") "f") "selector")
      (Ty.bytesN 4))

def e2ThisCallInPureStillRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (e2Contract (Expr.call (Expr.member (Expr.ident "this") "f") []) su_uint256))

-- ===========================================================================
-- O1 — a duplicate contract in an `override(...)` list is REJECTED (solc
-- OverrideChecker.cpp:850-879, error 4520). Neighbor: the legitimate diamond
-- `override(A, B)` still ACCEPTS.
-- ===========================================================================

private def o1VirtualF : FunctionDecl :=
  { name := some "f", visibility := some Visibility.public_
    virtual := true, body := some Stmt.empty }

private def o1BaseA : ContractDecl :=
  { name := "A", items := [ContractItem.function o1VirtualF] }
private def o1BaseB : ContractDecl :=
  { name := "B", items := [ContractItem.function o1VirtualF] }

private def o1Derived (overrideBases : List Path) : ContractDecl :=
  { name := "C"
    bases := [{ base := userPath "A" }, { base := userPath "B" }]
    items := [ ContractItem.function
      { name := some "f", visibility := some Visibility.public_
        override? := some { bases := overrideBases }, body := some Stmt.empty } ] }

private def o1Source (ob : List Path) : SourceUnit :=
  { items := [ SourceItem.contract o1BaseA
             , SourceItem.contract o1BaseB
             , SourceItem.contract (o1Derived ob) ] }

def o1DuplicateOverrideRejected : Bool :=
  Result.isError (SourceUnit.check (o1Source [userPath "A", userPath "A"]))

def o1DiamondOverrideAccepted : Bool :=
  sourceUnitAccepted? (o1Source [userPath "A", userPath "B"])

-- ===========================================================================
-- PT1 — a `constant` whose value cyclically depends on itself is REJECTED
-- (solc ConstStateVarCircularReferenceChecker, PostTypeChecker.cpp:154-245,
-- error 6161). Neighbor: a non-cyclic constant chain still ACCEPTS.
-- ===========================================================================

private def pt1Const (nm : Name) (e : Expr) : ContractItem :=
  ContractItem.stateVar
    { name := nm, ty := su_uint256, mutability := VarMutability.constant
      visibility := some Visibility.internal_, init := some e }

def pt1SelfCyclicConstantRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items := [ SourceItem.contract
          { name := "C", items := [ pt1Const "A" (Expr.ident "A") ] } ] })

def pt1MutualCyclicConstantRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items := [ SourceItem.contract
          { name := "C"
            items := [ pt1Const "A" (Expr.ident "B")
                     , pt1Const "B" (Expr.ident "A") ] } ] })

def pt1NonCyclicConstantAccepted : Bool :=
  sourceUnitAccepted?
    { items := [ SourceItem.contract
        { name := "C"
          items := [ pt1Const "A" (numberExpr "5")
                   , pt1Const "B"
                       (Expr.binary BinaryOp.add (Expr.ident "A") (numberExpr "1")) ] } ] }

-- ===========================================================================
-- AE1 — `abi.encodePacked` with an array-of-dynamic element (`bytes[]` /
-- `string[]`) is REJECTED (solc "Type not supported in packed mode"); this was
-- already handled — `Ty.isAbiEncodePackedArrayElementShape` omits `bytes`/
-- `string`. Neighbor: `abi.encodePacked(uint[])` still ACCEPTS.
-- ===========================================================================

private def ae1Fn (elemTy : Ty) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    params := [{ name := some "a", ty := Ty.array elemTy none
                 location := some DataLocation.memory }]
    returns := [{ name := none, ty := Ty.bytes
                  location := some DataLocation.memory }]
    body := some (Stmt.returnValues (some
      (Expr.call (Expr.member (Expr.ident "abi") "encodePacked")
        [Arg.positional (Expr.ident "a")]))) }

private def ae1Contract (elemTy : Ty) : SourceUnit :=
  { items := [ SourceItem.contract
      { name := "C", items := [ ContractItem.function (ae1Fn elemTy) ] } ] }

def ae1EncodePackedBytesArrayRejected : Bool :=
  Result.isError (SourceUnit.check (ae1Contract Ty.bytes)) &&
    Result.isError (SourceUnit.check (ae1Contract Ty.string))

def ae1EncodePackedUintArrayAccepted : Bool :=
  sourceUnitAccepted? (ae1Contract su_uint256)

-- ===========================================================================
-- Aggregate.
-- ===========================================================================

def round2AcceptanceBoundariesHold : Bool :=
  e1KeccakImmutableInPureRejected &&
    e1NeighborsAccepted &&
    e2ThisSelectorInPureAccepted &&
    e2ThisCallInPureStillRejected &&
    o1DuplicateOverrideRejected &&
    o1DiamondOverrideAccepted &&
    pt1SelfCyclicConstantRejected &&
    pt1MutualCyclicConstantRejected &&
    pt1NonCyclicConstantAccepted &&
    ae1EncodePackedBytesArrayRejected &&
    ae1EncodePackedUintArrayAccepted

end Examples
end TypeCheck
end Solidity
end SolidCore
