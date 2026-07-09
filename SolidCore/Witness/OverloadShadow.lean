/-
OV1 overload-shadow witnesses (2026-07-09).

solc removes a file-level (free) function from a contract's name scope whenever a
member function (the contract's own — any visibility — or a non-private
inherited one) declares the SAME NAME (name-based shadowing, warning 2519). A
single same-named member removes ALL free overloads of that name. This mirrors
the shadowing solidity-lean already implements for errors/events
(`ErrorSigs.withoutNamesOf` / `EventSigs.withoutNamesOf`) via the new
`FunctionSigs.withoutNamesOf`, applied when building `env.functions`.

This file pins the over-ACCEPT direction (solc REJECTS, so no Forge run): a bare
call whose only in-scope member candidate cannot accept the arguments must be
rejected even though a shadowed free overload would have matched. The
over-REJECT direction (solc ACCEPTS; the member body runs) is pinned by the
paired real contract + Forge test + solc_import in the `overload-shadow` lane
(`importedContractAccepted` and `checkedOwnCallWordMatches … "g" … 14`).

Helpers (`uint256`, `numberExpr`, `simpleReturnFunction`, `SourceUnit.check`,
`Result.isError`, `sourceUnitAccepted?`) come from `SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- A file-level (free) `f(uint256)`.
private def ov1FreeUintF : SourceItem :=
  SourceItem.freeFunction
    { simpleReturnFunction with
      name := some "f"
      visibility := none
      mutability := StateMutability.pure
      params := [{ name := some "a", ty := uint256, location := none }]
      returns := [{ name := none, ty := uint256, location := none }]
      body := some (Stmt.returnValues (some (Expr.ident "a"))) }

-- A contract member `f(string)` — shadows the free `f` by NAME.
private def ov1MemberStringF : ContractItem :=
  ContractItem.function
    { simpleReturnFunction with
      name := some "f"
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      params :=
        [{ name := some "s", ty := Ty.string,
           location := some DataLocation.memory }]
      returns := [{ name := none, ty := uint256, location := none }]
      body := some (Stmt.returnValues (some (numberExpr "0"))) }

-- A caller `g()` that makes the bare call `f(arg)`.
private def ov1CallerG (arg : Expr) : ContractItem :=
  ContractItem.function
    { simpleReturnFunction with
      name := some "g"
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := uint256, location := none }]
      body :=
        some
          (Stmt.returnValues
            (some (Expr.call (Expr.ident "f") [Arg.positional arg]))) }

-- Over-accept case: free `f(uint256)` + member `f(string)`, call `f(5)`.
-- The member shadows the free `f`, and `5` is not convertible to `string`, so
-- there is NO viable candidate — REJECTED (matches solc).
def ov1FreeShadowedByMemberSource : SourceUnit :=
  { items :=
      [ ov1FreeUintF
      , SourceItem.contract
          { name := "OverloadShadowReject"
            items := [ ov1MemberStringF, ov1CallerG (numberExpr "5") ] } ] }

def ov1FreeShadowedByMemberRejected : Bool :=
  Result.isError (SourceUnit.check ov1FreeShadowedByMemberSource)

-- Neighbor 1: same shadowing, but call `f("hi")` — the in-scope member
-- `f(string)` accepts it, so the program is ACCEPTED.
def ov1MemberCallAcceptedSource : SourceUnit :=
  { items :=
      [ ov1FreeUintF
      , SourceItem.contract
          { name := "OverloadShadowMemberOk"
            items :=
              [ ov1MemberStringF
              , ov1CallerG (Expr.literal (Literal.string "hi")) ] } ] }

-- Neighbor 2: free `f(uint256)` with NO shadowing member, call `f(5)` — the
-- free function is still callable, so the program is ACCEPTED (the fix must not
-- over-remove unshadowed free functions).
def ov1UnshadowedFreeCallAcceptedSource : SourceUnit :=
  { items :=
      [ ov1FreeUintF
      , SourceItem.contract
          { name := "OverloadShadowFreeOk"
            items := [ ov1CallerG (numberExpr "5") ] } ] }

def ov1ShadowNeighborsAccepted : Bool :=
  sourceUnitAccepted? ov1MemberCallAcceptedSource &&
    sourceUnitAccepted? ov1UnshadowedFreeCallAcceptedSource

end Examples
end TypeCheck
end Solidity
end SolidCore
