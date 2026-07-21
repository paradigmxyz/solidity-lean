/-
#200 (QUAL-DIRECT) contract-qualified member access resolves DIRECT
declarations only.

Pins a CONFIRMED over-accept fixed on the Lean side: solc 0.8.35's
`TypeType::nativeMembers` (Types.cpp) iterates `contract.declarations()` —
the named contract's OWN declarations, never inherited ones — so
`B.K` / `B.v` / `emit B.Ev` / `revert B.E` / `B.Ev.selector` where the
member is only INHERITED by `B` reject with error 9582 ("Member ... not
found or not visible"). Additionally a state variable has no
`isVisibleViaContractTypeAccess`, so OUTSIDE the named contract's own
hierarchy `A.K` / `A.v` never resolves either (even a public constant),
while from a DERIVING scope (including the contract itself) it resolves iff
`isVisibleInDerivedContracts` (>= internal, i.e. not private). A LIBRARY
member instead resolves anywhere iff `isVisibleAsLibraryMember`
(>= internal). Events/errors are visible via contract-type access from
anywhere — but only when declared DIRECTLY in the named contract.

The model resolved all of these through the named contract's full C3
linearization with no scope gate (probes r1-r22 vs pinned solc 0.8.35).
Kept in the built library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Checked

set_option maxHeartbeats 8000000

namespace SolidCore
namespace Solidity
namespace Executable
namespace QualifiedDirectMember

open Solidity

private def constK (vis : Visibility := Visibility.public_) : ContractItem :=
  ContractItem.stateVar
    { name := "K", ty := Ty.uint 256
      visibility := some vis
      mutability := VarMutability.constant
      override? := none
      init := some (Expr.literal (Literal.number "7")) }

private def varV : ContractItem :=
  ContractItem.stateVar
    { name := "v", ty := Ty.uint 256
      visibility := some Visibility.public_
      mutability := VarMutability.mutable
      override? := none
      init := none }

private def evD : ContractItem :=
  ContractItem.eventDecl
    { name := "Ev", params := [{ name := some "x", ty := Ty.uint 256 }] }

private def errD : ContractItem :=
  ContractItem.errorDecl
    { name := "E", params := [{ name := some "x", ty := Ty.uint 256 }] }

private def qual (c m : Name) : Expr :=
  Expr.member (Expr.typeName (Ty.user { segments := [c] })) m

private def fnG (body : List Stmt) (ret : Bool := true)
    (sm : StateMutability := StateMutability.pure) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "g"
      visibility := some Visibility.public_
      mutability := sm
      params := []
      returns := if ret then [{ name := none, ty := Ty.uint 256 }] else []
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block body) }

private def mkC (name : Name) (bases : List Name)
    (items : List ContractItem) : SourceItem :=
  SourceItem.contract
    { kind := ContractKind.contract
      name := name
      abstract := false
      bases := bases.map (fun b => { base := { segments := [b] } })
      items := items }

private def unit (cs : List SourceItem) : SourceUnit :=
  { items := SourceItem.pragma "solidity" "0.8.35" :: cs }

private def accepted? (u : SourceUnit) : Bool :=
  TypeCheck.sourceUnitAccepted? u

private def retQ (c m : Name) : List Stmt :=
  [Stmt.returnValues (some (qual c m))]

-- ===== REJECTS (solc 9582): the fixed over-accepts. =====

/-- r1: `B.K` from an unrelated contract where `K` is only inherited by `B`. -/
def inheritedConstUnrelatedRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [constK], mkC "B" ["A"] []
    , mkC "T" [] [fnG (retQ "B" "K")] ]) == false

/-- r2: even a DIRECT public constant `A.K` is not visible via contract-type
access from an UNRELATED scope (state vars have no
`isVisibleViaContractTypeAccess`). -/
def directConstUnrelatedRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [constK], mkC "T" [] [fnG (retQ "A" "K")] ]) == false

/-- r5: `B.K` inside `B is A` itself — the deriving scope does not help
because `K` is not a DIRECT declaration of `B`. -/
def inheritedConstSelfQualifiedRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [constK]
    , mkC "B" ["A"] [fnG (retQ "B" "K")] ]) == false

/-- r3: `emit B.Ev(...)` where `Ev` is only inherited by `B`. -/
def inheritedEventEmitRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [evD], mkC "B" ["A"] []
    , mkC "T" []
        [fnG
          [Stmt.emitEvent (Expr.call (qual "B" "Ev")
            [Arg.positional (Expr.literal (Literal.number "1"))])]
          false StateMutability.nonpayable] ]) == false

/-- r11: `revert B.E(...)` where `E` is only inherited by `B`. -/
def inheritedErrorRevertRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [errD], mkC "B" ["A"] []
    , mkC "T" []
        [fnG
          [Stmt.revertCall (Expr.call (qual "B" "E")
            [Arg.positional (Expr.literal (Literal.number "1"))])]
          false] ]) == false

/-- r13: `B.Ev.selector` where `Ev` is only inherited by `B`. -/
def inheritedEventSelectorRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [evD], mkC "B" ["A"] []
    , mkC "T" []
        [fnG
          [Stmt.returnValues (some
            (Expr.call (Expr.typeName (Ty.uint 256))
              [Arg.positional (Expr.member (qual "B" "Ev") "selector")]))]] ])
    == false

/-- r16: `B.v` from a deriving scope where `v` is only inherited by `B`. -/
def inheritedStateVarRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [varV], mkC "B" ["A"] []
    , mkC "C" ["B"] [fnG (retQ "B" "v") true StateMutability.view] ]) == false

/-- r16b: a direct state variable `A.v` from an UNRELATED scope. -/
def directStateVarUnrelatedRejected : Bool :=
  accepted? (unit
    [ mkC "A" [] [varV]
    , mkC "T" [] [fnG (retQ "A" "v") true StateMutability.view] ]) == false

/-- r22: a PRIVATE constant is not visible via `A.K` even inside `A`. -/
def privateConstSelfQualifiedRejected : Bool :=
  accepted? (unit
    [ mkC "A" []
        [constK Visibility.private_, fnG (retQ "A" "K")] ]) == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

/-- r6: `A.K` from the deriving `B is A` (direct declaration of `A`). -/
def directConstDerivingAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [constK]
    , mkC "B" ["A"] [fnG (retQ "A" "K")] ]) == true

/-- r21: `A.K` inside `A` itself. -/
def directConstSelfAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [constK, fnG (retQ "A" "K")] ]) == true

/-- r4: `emit A.Ev(...)` from an unrelated contract (events ARE visible via
contract-type access; direct declaration). -/
def directEventEmitAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [evD]
    , mkC "T" []
        [fnG
          [Stmt.emitEvent (Expr.call (qual "A" "Ev")
            [Arg.positional (Expr.literal (Literal.number "1"))])]
          false StateMutability.nonpayable] ]) == true

/-- r12: `revert A.E(...)` from an unrelated contract (direct declaration). -/
def directErrorRevertAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [errD]
    , mkC "T" []
        [fnG
          [Stmt.revertCall (Expr.call (qual "A" "E")
            [Arg.positional (Expr.literal (Literal.number "1"))])]
          false] ]) == true

/-- r14: `A.Ev.selector` from an unrelated contract (direct declaration). -/
def directEventSelectorAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [evD]
    , mkC "T" []
        [fnG
          [Stmt.returnValues (some
            (Expr.call (Expr.typeName (Ty.uint 256))
              [Arg.positional (Expr.member (qual "A" "Ev") "selector")]))]] ])
    == true

/-- r15: `A.v` (direct state variable) from the deriving `B is A`. -/
def directStateVarDerivingAccepted : Bool :=
  accepted? (unit
    [ mkC "A" [] [varV]
    , mkC "B" ["A"] [fnG (retQ "A" "v") true StateMutability.view] ]) == true

/-- r17: a library internal constant `L.K` from anywhere
(`isVisibleAsLibraryMember`). -/
def libraryConstAccepted : Bool :=
  accepted? (unit
    [ SourceItem.contract
        { kind := ContractKind.library
          name := "L"
          abstract := false
          bases := []
          items := [ContractItem.stateVar
            { name := "K", ty := Ty.uint 256
              visibility := some Visibility.internal_
              mutability := VarMutability.constant
              override? := none
              init := some (Expr.literal (Literal.number "9")) }] }
    , mkC "T" [] [fnG (retQ "L" "K")] ]) == true

def qualifiedDirectMemberMatches : Bool :=
  inheritedConstUnrelatedRejected && directConstUnrelatedRejected &&
    inheritedConstSelfQualifiedRejected && inheritedEventEmitRejected &&
    inheritedErrorRevertRejected && inheritedEventSelectorRejected &&
    inheritedStateVarRejected && directStateVarUnrelatedRejected &&
    privateConstSelfQualifiedRejected &&
    directConstDerivingAccepted && directConstSelfAccepted &&
    directEventEmitAccepted && directErrorRevertAccepted &&
    directEventSelectorAccepted && directStateVarDerivingAccepted &&
    libraryConstAccepted

#guard qualifiedDirectMemberMatches

end QualifiedDirectMember
end Executable
end Solidity
end SolidCore
