/-
CF2 — revert-pruning of always-reverting callees (2026-07-08).

solc's `ControlFlowRevertPruner` reroutes a call to a callee that ALWAYS
reverts to the revert node, so paths after such a call cannot reach the
function exit; the storage/calldata-pointer-return definite-assignment check
(error 3464) then runs on the pruned CFG. solidity-lean previously modelled a call as
a normal returning node, over-rejecting a `returns (T storage p)` whose only
unmet-obligation path runs through an always-reverting helper.

Each item pins BOTH sides of the boundary on the Lean side, matching pinned
solc 0.8.35 (probed):
  * ACCEPT (the fix / regression guards): the helper-revert form, the direct
    `revert` form, a transitive always-reverting helper, and an
    all-branches-revert helper — `sourceUnitAccepted?` is `true`.
  * REJECT (sound must-still-reject neighbors): a genuinely-unassigned path, a
    helper that only SOMETIMES reverts, a `require(false)` helper (`require` is
    not an always-revert terminator), and an EXTERNAL callee (`this.boom()`,
    which is not resolved/pruned) — `Result.isError (SourceUnit.check …)`.

Paired solc-REJECT `.sol` fixtures live under
`tests/forge-harness/cf2-revert-pruning/invalid/`; the Forge-paired accept lane
(`src/CF2RevertPruning.sol`) checks the helper-revert pointer-return computes
the right value on the non-reverting path.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- `revert("x")`
private def cf2Revert : Stmt :=
  Stmt.revertCall
    (Expr.call (Expr.ident "revert")
      [Arg.positional (Expr.literal (Literal.string "x"))])

-- An internal helper with the given parameters and (returns-nothing) body.
private def cf2Helper
    (nm : Name) (params : List Parameter) (body : Stmt) : FunctionDecl :=
  { simpleReturnFunction with
    name := some nm
    visibility := some Visibility.internal_
    mutability := StateMutability.pure
    params := params
    returns := []
    body := some body }

private def cf2BoolParam : List Parameter :=
  [{ name := some "q", ty := Ty.bool, location := none }]

-- `pick(bool c) internal returns (uint256[] storage p)` with a caller-chosen
-- tail statement after the `if (c) { p = xs; return p; }`.
private def cf2Pick (tail : Stmt) : FunctionDecl :=
  { simpleReturnFunction with
    name := some "pick"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    params := [{ name := some "c", ty := Ty.bool, location := none }]
    returns :=
      [ { name := some "p", ty := uintArrayTy,
          location := some DataLocation.storage } ]
    body :=
      some (Stmt.block
        [ Stmt.ifElse (Expr.ident "c")
            (Stmt.block
              [ Stmt.expr
                  (Expr.assign (Expr.ident "p") AssignOp.assign
                    (Expr.ident "xs"))
              , Stmt.returnValues (some (Expr.ident "p")) ])
            none
        , tail ]) }

private def cf2Source
    (helpers : List FunctionDecl) (tail : Stmt) : SourceUnit :=
  { items :=
      [ SourceItem.contract
          { name := "C"
            items :=
              [ ContractItem.stateVar { name := "xs", ty := uintArrayTy } ] ++
                helpers.map ContractItem.function ++
                [ ContractItem.function (cf2Pick tail) ] } ] }

private def cf2Call (nm : Name) (args : List Arg) : Stmt :=
  Stmt.expr (Expr.call (Expr.ident nm) args)

-- === ACCEPT side ==========================================================

-- The fix: the only obligation-unmet path runs through an always-reverting
-- internal helper.
def cf2HelperRevertAccepted : Bool :=
  sourceUnitAccepted?
    (cf2Source [cf2Helper "boom" [] (Stmt.block [cf2Revert])]
      (cf2Call "boom" []))

-- Regression guard: the direct inline-`revert` form still accepts.
def cf2DirectRevertAccepted : Bool :=
  sourceUnitAccepted? (cf2Source [] cf2Revert)

-- Transitive: `outer` always reverts because it calls always-reverting `inner`.
def cf2TransitiveRevertAccepted : Bool :=
  sourceUnitAccepted?
    (cf2Source
      [ cf2Helper "inner" [] (Stmt.block [cf2Revert])
      , cf2Helper "outer" [] (Stmt.block [cf2Call "inner" []]) ]
      (cf2Call "outer" []))

-- All branches of the helper revert.
def cf2AllBranchesRevertAccepted : Bool :=
  sourceUnitAccepted?
    (cf2Source
      [ cf2Helper "both" cf2BoolParam
          (Stmt.block
            [ Stmt.ifElse (Expr.ident "q") cf2Revert (some cf2Revert) ]) ]
      (cf2Call "both" [Arg.positional (Expr.ident "c")]))

-- === REJECT side (sound neighbors) ========================================

-- Genuinely unassigned: the `c == false` path just falls through.
def cf2UnassignedRejected : Bool :=
  Result.isError (SourceUnit.check (cf2Source [] Stmt.empty))

-- The helper only sometimes reverts (no `else`), so it does not always revert.
def cf2SometimesRevertsRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (cf2Source
        [ cf2Helper "maybe" cf2BoolParam
            (Stmt.block [Stmt.ifElse (Expr.ident "q") cf2Revert none]) ]
        (cf2Call "maybe" [Arg.positional (Expr.ident "c")])))

-- `require(false)` is not an always-revert terminator (solc connects it to a
-- following node), so the helper does not prune.
def cf2RequireHelperRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (cf2Source
        [ cf2Helper "req" []
            (Stmt.block
              [ cf2Call "require"
                  [ Arg.positional (boolExpr false)
                  , Arg.positional (Expr.literal (Literal.string "x")) ] ]) ]
        (cf2Call "req" [])))

-- External callee: `this.boom()` is an external call, never resolved/pruned.
def cf2ExternalCalleeRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (cf2Source
        [ { simpleReturnFunction with
            name := some "boom"
            visibility := some Visibility.public_
            mutability := StateMutability.nonpayable
            params := []
            returns := []
            body := some (Stmt.block [cf2Revert]) } ]
        (Stmt.expr
          (Expr.call
            (Expr.member (Expr.ident "this") "boom") []))))

def cf2AcceptanceBoundariesHold : Bool :=
  cf2HelperRevertAccepted &&
    cf2DirectRevertAccepted &&
    cf2TransitiveRevertAccepted &&
    cf2AllBranchesRevertAccepted &&
    cf2UnassignedRejected &&
    cf2SometimesRevertsRejected &&
    cf2RequireHelperRejected &&
    cf2ExternalCalleeRejected

end Examples
end TypeCheck
end Solidity
end SolidCore
