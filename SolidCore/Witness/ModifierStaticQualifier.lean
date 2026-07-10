import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
#157 MODIFIER-STATIC-QUALIFIER witnesses.

A statically QUALIFIED modifier invocation `Base.m` on a function binds to the
NAMED base contract's own modifier (solc `VirtualLookup::Static`), NOT to the
most-derived override. In the pinned solc 0.8.35 AST the invocation is an
`IdentifierPath name:"Base.m"` whose `referencedDeclaration` points at Base's
ModifierDefinition (id 11), not Derived's override (id 33). Deploying `Derived`
and calling `f()` leaves `tag == 1` on the real EVM (Base's modifier ran).

The model formerly dropped the `Base.` qualifier — it resolved every modifier
invocation by its LAST path segment (`pathLast?`) via a first-match (`find?`)
over the most-derived-first dispatch order, so `Base.m` wrongly ran Derived's
`m` (`tag == 2`). The fix stamps each modifier with its declaring contract
(`directModifiersStamped`) and resolves a qualified target STATICALLY against
that contract (`modifierResolve?`); an UNQUALIFIED `m` stays virtual.

`#eval`-confirmed booleans pinned with `#guard`. Real-EVM Forge ground truth is
in `tests/forge-harness/modifier-static-qualifier` (anvil: Derived.f() then
tag() returns 1).
-/

open SolidCore.Solidity.Source
open SolidCore.Solidity

namespace SolidCore
namespace Solidity
namespace Witness
namespace ModifierStaticQualifier

private def uintReturn : List Parameter :=
  [{ name := none, ty := Ty.uint 256 }]

-- modifier m() virtual { tag = 1; _; }
private def baseModifier : ModifierDecl :=
  { name := "m"
    virtual := true
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "tag") AssignOp.assign
                (Expr.literal (Literal.number "1")))
          , Stmt.modifierPlaceholder ]) }

-- modifier m() override { tag = 2; _; }
private def derivedModifier : ModifierDecl :=
  { name := "m"
    override? := some {}
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "tag") AssignOp.assign
                (Expr.literal (Literal.number "2")))
          , Stmt.modifierPlaceholder ]) }

-- function f() public <mod> returns (uint) { return 7; }
private def fWith (modTarget : List Name) : FunctionDecl :=
  { name := some "f"
    visibility := some Visibility.public_
    modifiers := [{ target := { segments := modTarget } }]
    returns := uintReturn
    body := some (Stmt.returnValues (some (Expr.literal (Literal.number "7")))) }

private def tagStateVar : ContractItem :=
  ContractItem.stateVar
    { name := "tag", ty := Ty.uint 256, visibility := some Visibility.public_ }

private def baseContract (fModTarget : List Name) : ContractDecl :=
  { name := "Base"
    items :=
      [ tagStateVar
      , ContractItem.modifierDecl baseModifier
      , ContractItem.function (fWith fModTarget) ] }

private def derivedContract : ContractDecl :=
  { name := "Derived"
    bases := [{ base := { segments := ["Base"] } }]
    items := [ContractItem.modifierDecl derivedModifier] }

/-- Base declares `f() public Base.m` — the QUALIFIED invocation. -/
def qualifiedSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "^0.8.0"
      , SourceItem.contract (baseContract ["Base", "m"])
      , SourceItem.contract derivedContract ] }

/-- Control: same shape but `f() public m` — the UNQUALIFIED invocation, which
must stay VIRTUAL and run Derived's override. -/
def unqualifiedSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "^0.8.0"
      , SourceItem.contract (baseContract ["m"])
      , SourceItem.contract derivedContract ] }

def qualifiedContractsAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit qualifiedSourceUnit)

def unqualifiedContractsAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit unqualifiedSourceUnit)

/-- Deploy `Derived`, call `f()`, and read back storage slot 0 (`tag`). -/
private def tagAfterF? (unit : SourceUnit) : Option Word :=
  match
    SolidCore.Solidity.TypeCheck.CheckedInput.callContract 64 unit "Derived"
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned state _) =>
      some (state.loadSlot 0)
  | _ => none

/-- QUALIFIED `Base.m` runs Base's modifier: `tag == 1` (matches pinned
solc / anvil, static bind). -/
def qualifiedTagMatches : Bool :=
  match tagAfterF? qualifiedSourceUnit with
  | some w => SolidCore.Solidity.Source.wordEq w 1
  | none => false

/-- UNQUALIFIED `m` stays virtual and runs Derived's override: `tag == 2`.
This is the control proving the fix did not blanket-staticize modifiers. -/
def unqualifiedTagMatches : Bool :=
  match tagAfterF? unqualifiedSourceUnit with
  | some w => SolidCore.Solidity.Source.wordEq w 2
  | none => false

#guard qualifiedContractsAccepted
#guard unqualifiedContractsAccepted
#guard qualifiedTagMatches
#guard unqualifiedTagMatches

end ModifierStaticQualifier
end Witness
end Solidity
end SolidCore
