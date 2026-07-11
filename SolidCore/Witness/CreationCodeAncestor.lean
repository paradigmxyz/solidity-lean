import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CREATIONCODE-ANCESTOR (#167) — `type(Base).creationCode` / `runtimeCode` for an
ANCESTOR is a normal acyclic bytecode dependency, not a cycle.

solc only forbids a genuine bytecode CYCLE: a contract's OWN code
(`type(C).creationCode` inside `C`, or a mutual reference), raised at codegen as
"Circular reference to contract bytecode" (CompilerStack.cpp:210). Accessing a
strict ANCESTOR's `creationCode`/`runtimeCode` is fine, and both members are
`pure` (TypeChecker.cpp:3482).

solidity-lean formerly rejected any `type(T).creationCode/runtimeCode` where `T`
is the current contract OR an ancestor (`isCurrentOrAncestorContract`), an
OVER-REJECT for the ancestor case. The fix narrows the self-reference guard to
the CURRENT contract only (`isCurrentContract`); the self case still rejects
(matches solc, which errors on the cycle).

Bonus, same MetaType handler: solc rejects `runtimeCode` (only runtimeCode, NOT
creationCode) for a contract whose whole linearized base set contains any
immutable variable — TypeChecker.cpp:3486-3493, error 9274 `"runtimeCode" is not
available for contracts containing immutable variables.` (verified on pinned
solc 0.8.35). The model previously had no such check (over-accept); the fix adds
`TypeContext.contractHasImmutable` and rejects that one member.

Real-EVM Forge ground truth for the primary over-reject:
`tests/forge-harness/creationcode-ancestor` (ancestor creationCode/runtimeCode
returned non-empty). `#eval`-confirmed booleans pinned with `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace CreationCodeAncestor

def importedSourceName : String :=
  "tests/forge-harness/creationcode-ancestor/src/CreationCodeAncestor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "CreationCodeAncestorBase"
  abstract := false
  bases := []
  items := [] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "CreationCodeAncestorTarget"
  abstract := false
  bases := [{ base := { segments := ["CreationCodeAncestorBase"] }, args := [] }]
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "ancestorCreation",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.typeName (Ty.user ({ segments := ["CreationCodeAncestorBase"] }))) "creationCode"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ancestorRuntime",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.typeName (Ty.user ({ segments := ["CreationCodeAncestorBase"] }))) "runtimeCode"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end CreationCodeAncestor
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace CreationCodeAncestor

open SolidCore.Solidity

private def accepts (su : SourceUnit) : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit su)

private def fnRet (nm : String) (body : Expr) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some nm,
      visibility := some Visibility.public_, mutability := StateMutability.pure,
      params := [], returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
      body := some (Stmt.block [Stmt.returnValues (some body)]) }

private def cc (nm : String) : Expr :=
  Expr.member (Expr.typeName (Ty.user { segments := [nm] })) "creationCode"
private def rc (nm : String) : Expr :=
  Expr.member (Expr.typeName (Ty.user { segments := [nm] })) "runtimeCode"

private def immVar : ContractItem :=
  ContractItem.stateVar { name := "x", ty := Ty.uint 256, mutability := VarMutability.immutable }

/-- PRIMARY: the imported forge target (ancestor creationCode + runtimeCode)
    type-checks. Was formerly REJECTED (`member creationCode`). -/
def importedAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.CreationCodeAncestor.importedContractAccepted

-- Grandparent creationCode (C is B, B is A; access `type(A).creationCode`): ACCEPT.
def grandparentAccepted : Bool :=
  accepts { items := [
    SourceItem.contract { name := "A", items := [] },
    SourceItem.contract { name := "B", bases := [{ base := { segments := ["A"] } }], items := [] },
    SourceItem.contract { name := "C", bases := [{ base := { segments := ["B"] } }], items := [fnRet "f" (cc "A")] }] }

-- Self-reference `type(C).creationCode` inside C: REJECT (solc: Circular reference).
def selfRejected : Bool :=
  ! accepts { items := [
    SourceItem.contract { name := "C", items := [fnRet "f" (cc "C")] }] }

-- Unrelated contract `type(D).creationCode`: ACCEPT (unchanged).
def unrelatedAccepted : Bool :=
  accepts { items := [
    SourceItem.contract { name := "D", items := [] },
    SourceItem.contract { name := "C", items := [fnRet "f" (cc "D")] }] }

-- BONUS: `type(D).runtimeCode` where D has an immutable var: REJECT (solc 9274).
def runtimeImmutableRejected : Bool :=
  ! accepts { items := [
    SourceItem.contract { name := "D", items := [immVar] },
    SourceItem.contract { name := "C", items := [fnRet "f" (rc "D")] }] }

-- BONUS: `type(D).creationCode` where D has an immutable var: ACCEPT (creationCode stays).
def creationImmutableAccepted : Bool :=
  accepts { items := [
    SourceItem.contract { name := "D", items := [immVar] },
    SourceItem.contract { name := "C", items := [fnRet "f" (cc "D")] }] }

-- The immutable rule follows the whole linearized base set: `type(D).runtimeCode`
-- where an ANCESTOR of D declares the immutable is also REJECTED (solc 9274).
def runtimeInheritedImmutableRejected : Bool :=
  ! accepts { items := [
    SourceItem.contract { name := "Base", items := [immVar] },
    SourceItem.contract { name := "D", bases := [{ base := { segments := ["Base"] } }], items := [] },
    SourceItem.contract { name := "C", items := [fnRet "f" (rc "D")] }] }

-- Over-reject regression guard: `type(D).runtimeCode`, D unrelated WITHOUT
-- immutables: ACCEPT.
def runtimeNoImmutableAccepted : Bool :=
  accepts { items := [
    SourceItem.contract { name := "D", items := [] },
    SourceItem.contract { name := "C", items := [fnRet "f" (rc "D")] }] }

#guard importedAccepted
#guard grandparentAccepted
#guard selfRejected
#guard unrelatedAccepted
#guard runtimeImmutableRejected
#guard creationImmutableAccepted
#guard runtimeInheritedImmutableRejected
#guard runtimeNoImmutableAccepted

end CreationCodeAncestor
end Witness
end Solidity
end SolidCore
