/-
#154 (DEPLOY-ABSTRACT) — the top-level deploy/acceptance entry must refuse to
instantiate a non-`contract` kind or an `abstract` contract, matching solc
0.8.35.

Pinned solc 0.8.35 ground truth (oracle
`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`):

  * `abstract contract A { function f() public virtual returns (uint); }`
    compiles to an EMPTY `Binary:`; `new A()` in a factory is rejected with
    "Cannot instantiate an abstract contract."
  * `interface I { function f() external returns (uint); }` compiles to an EMPTY
    `Binary:`; `new I()` -> "Invalid use of ...".
  * `library L { ... }` is not instantiable; `new L()` -> "Invalid use of a
    library name."

Only a concrete `contract` (kind == contract && !abstract) is creatable. The
`new`-expression site already enforces this via
`TypeCheck.requireCreatableContractDecl`; this witness pins the SAME guard now
applied at the top-level deploy entry `CheckedProgram.constructContractFrom`
(SolidCore/Solidity/Checked.lean), so deploying an abstract/interface/library is
rejected while every concrete contract (including one that implements an
abstract base) still deploys.

This is an over-accept fix (solc emits no AST/bytecode for a rejected deploy, so
it is not replay-reachable): witness-only, no Forge lane. The `abstract` flag and
the contract `kind` are both imported, so the information was present and merely
unchecked at the deploy entry.

Booleans are `#eval`-confirmed and pinned with `#guard` (the project avoids
`native_decide` to keep the axiom set empty).
-/
import SolidCore.Solidity.Checked

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace DeployAbstract

open Solidity

private def uintTy : Ty := Ty.uint 256

private def uintReturn : List Parameter :=
  [{ name := none, ty := uintTy, location := none }]

private def retNumber (n : String) : Stmt :=
  Stmt.returnValues (some (Expr.literal (Literal.number n)))

-- abstract contract A { function f() public virtual returns (uint); }
def abstractContract : ContractDecl :=
  { kind := ContractKind.contract
    name := "A"
    abstract := true
    items :=
      [ ContractItem.function
          { name := some "f"
            visibility := some Visibility.public_
            mutability := StateMutability.view
            virtual := true
            returns := uintReturn
            body := none } ] }

def abstractSource : SourceUnit :=
  { items := [SourceItem.contract abstractContract] }

-- interface I { function f() external returns (uint); }
def interfaceContract : ContractDecl :=
  { kind := ContractKind.interface
    name := "I"
    items :=
      [ ContractItem.function
          { name := some "f"
            visibility := some Visibility.external_
            mutability := StateMutability.view
            returns := uintReturn
            body := none } ] }

def interfaceSource : SourceUnit :=
  { items := [SourceItem.contract interfaceContract] }

-- library L { function g() internal pure returns (uint) { return 1; } }
def libraryContract : ContractDecl :=
  { kind := ContractKind.library
    name := "L"
    items :=
      [ ContractItem.function
          { name := some "g"
            visibility := some Visibility.internal_
            mutability := StateMutability.pure
            returns := uintReturn
            body := some (retNumber "1") } ] }

def librarySource : SourceUnit :=
  { items := [SourceItem.contract libraryContract] }

-- contract C { function f() public pure returns (uint) { return 7; } }
def concreteContract : ContractDecl :=
  { name := "C"
    items :=
      [ ContractItem.function
          { name := some "f"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            returns := uintReturn
            body := some (retNumber "7") } ] }

def concreteSource : SourceUnit :=
  { items := [SourceItem.contract concreteContract] }

-- abstract contract A { function f() public virtual returns (uint); }
-- contract D is A { function f() public override view returns (uint) { return 9; } }
def concreteImplContract : ContractDecl :=
  { name := "D"
    bases := [{ base := { segments := ["A"] } }]
    items :=
      [ ContractItem.function
          { name := some "f"
            visibility := some Visibility.public_
            mutability := StateMutability.view
            virtual := true
            override? := some {}
            returns := uintReturn
            body := some (retNumber "9") } ] }

def concreteImplSource : SourceUnit :=
  { items :=
      [ SourceItem.contract abstractContract
      , SourceItem.contract concreteImplContract ] }

/-- A deploy at the top-level entry is REJECTED (surfaces `Except.error`). -/
def deployRejected (source : SourceUnit) (name : Name) : Bool :=
  match CheckedInput.constructContract 32 source name
      SolidCore.Solidity.Source.State.empty [] with
  | Except.error _ => true
  | Except.ok _ => false

/-- A deploy at the top-level entry SUCCEEDS (`returned`). -/
def deploySucceeds (source : SourceUnit) (name : Name) : Bool :=
  match CheckedInput.constructContract 32 source name
      SolidCore.Solidity.Source.State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned _ _) => true
  | _ => false

-- Each non-instantiable program still TYPECHECKS (the abstract flag / kind are
-- valid to *declare*), proving it is the deploy guard — not a type error — that
-- refuses instantiation.
def abstractProgramTypechecks : Bool :=
  Result.isOk (CheckedInput.program abstractSource)
def interfaceProgramTypechecks : Bool :=
  Result.isOk (CheckedInput.program interfaceSource)
def libraryProgramTypechecks : Bool :=
  Result.isOk (CheckedInput.program librarySource)

#guard abstractProgramTypechecks
#guard interfaceProgramTypechecks
#guard libraryProgramTypechecks

-- Deploying an abstract contract / interface / library is now REJECTED.
def abstractDeployRejected : Bool := deployRejected abstractSource "A"
def interfaceDeployRejected : Bool := deployRejected interfaceSource "I"
def libraryDeployRejected : Bool := deployRejected librarySource "L"

#guard abstractDeployRejected
#guard interfaceDeployRejected
#guard libraryDeployRejected

-- A concrete contract still deploys, and so does a concrete contract that
-- implements an abstract base; the abstract base itself stays non-instantiable.
def concreteDeploySucceeds : Bool := deploySucceeds concreteSource "C"
def concreteImplDeploySucceeds : Bool := deploySucceeds concreteImplSource "D"
def abstractBaseStillRejected : Bool := deployRejected concreteImplSource "A"

#guard concreteDeploySucceeds
#guard concreteImplDeploySucceeds
#guard abstractBaseStillRejected

end DeployAbstract
end TypeCheck
end Solidity
end SolidCore
