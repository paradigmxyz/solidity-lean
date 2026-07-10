import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
USINGFOR-WIDEN-BIND (#158) — over-reject.

`using L for uint8` attaching a library function whose FIRST parameter is WIDER
than the target type. solc distinguishes two levels (Types.cpp):

* Directive APPLICABILITY (`usingForDirectivesForType`): the receiver type must
  EXACTLY equal the directive target (`uint8 == uint8`). Unchanged/exact.
* Function USABILITY (`Type::attachedFunctions`): the receiver need only be
  IMPLICITLY CONVERTIBLE to the function's first-parameter type
  (`_type.isImplicitlyConvertibleTo(...selfType())`). So a `uint8` receiver
  binds `f(uint256 self)` — the receiver is zero-extended, NO truncation.

The model formerly bound the first parameter with the exact-width
`Ty.matchesShape` and over-rejected. The fix (SolidCore/Solidity/Interface.lean)
uses DIRECTIONAL `Ty.canImplicitlyConvert receiverTy first.ty` for the receiver
bind (`FunctionDecl.firstParamMatchesWithInternalFunctions?`) and for the
re-checked receiver + additional args
(`Parameter.matchesArgWithInternalFunctions?`). Because convertibility is
directional, the WIDER-receiver, incompatible, and signedness cases stay
rejected.

Real solc 0.8.35 / EVM ground truth (forge lane `using-for-widen`):
`widenReceiver(255) == 256`, `widenReceiver(5) == 6`,
`widenAddArg(1000, 255) == 1255`.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace UsingForWiden

def importedSourceName : String := "tests/forge-harness/using-for-widen/src/UsingForWiden.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "self", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "self") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "addWiden",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "self", ty := Ty.uint 256, location := none }, { name := some "a", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "self") (Expr.ident "a")))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "UsingForWidenHarnessTarget"
  abstract := false
  bases := []
  items := [(ContractItem.usingDecl
  { library := { segments := ["L"] },
    functions := [],
    target := some (Ty.uint 8),
    global := false }), (ContractItem.usingDecl
  { library := { segments := ["L"] },
    functions := [],
    target := some (Ty.uint 256),
    global := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenReceiver",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "x") "f") []))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "widenAddArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }, { name := some "y", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "x") "addWiden") [Arg.positional (Expr.ident "y")]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end UsingForWiden
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace UsingForWiden

open SolidCore.Solidity.SolcAstImport.UsingForWiden (importedSourceUnit importedContractAccepted)

/-- The over-rejected using-for widened-receiver unit is now ACCEPTED. -/
def usingForWidenAccepted : Bool := importedContractAccepted

#guard usingForWidenAccepted

/-- Reduce an `Except _ Bool` execution result to a plain Bool for `#guard`. -/
private def okTrue {ε : Type} : Except ε Bool -> Bool
  | Except.ok b => b
  | _ => false

/-- Runtime: uint8 receiver 255 widened (zero-extended) to the uint256 first
parameter of `f`; 255 + 1 = 256, NO truncation to uint8. Matches real solc/EVM
(`widenReceiver(255) == 256`). -/
def usingForWidenReceiverMax : Bool :=
  okTrue
    (SolidCore.Solidity.TypeCheck.Examples.checkedCallWordMatches 64
      importedSourceUnit "UsingForWidenHarnessTarget" "widenReceiver"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 255] 256)

#guard usingForWidenReceiverMax

/-- Runtime: `widenReceiver(5) == 6`. -/
def usingForWidenReceiverSmall : Bool :=
  okTrue
    (SolidCore.Solidity.TypeCheck.Examples.checkedCallWordMatches 64
      importedSourceUnit "UsingForWidenHarnessTarget" "widenReceiver"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 5] 6)

#guard usingForWidenReceiverSmall

/-- Runtime: uint256 receiver (exact self) + uint8 additional arg 255 widened to
uint256: `widenAddArg(1000, 255) == 1255`. -/
def usingForWidenAddArg : Bool :=
  okTrue
    (SolidCore.Solidity.TypeCheck.Examples.checkedCallWordMatches 64
      importedSourceUnit "UsingForWidenHarnessTarget" "widenAddArg"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 1000,
       SolidCore.Solidity.Source.Value.word 255] 1255)

#guard usingForWidenAddArg

-- ────────────────────────────────────────────────────────────────────────
-- Over-ACCEPT guards: the directional fix must NOT loosen these. solc REJECTS
-- all three (verified with pinned solc 0.8.35: "Member ... not found or not
-- visible after argument-dependent lookup"), and the model must too. These are
-- hand-authored because solc emits no AST for a rejected program.

/-- Build `library L { function f(<selfTy>) internal pure returns (<selfTy>) }`
plus `contract C { using L for <targetTy>; function g(<argTy> x) external pure
returns (<retTy>) { return x.f(); } }`. -/
private def widenRejectSource
    (selfTy targetTy argTy retTy : Ty) : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "^0.8.35"
      , SourceItem.contract
          { kind := ContractKind.library
            name := "L"
            items :=
              [ ContractItem.function
                  { kind := FunctionKind.function
                    name := some "f"
                    visibility := some Visibility.internal_
                    mutability := StateMutability.pure
                    params := [{ name := some "self", ty := selfTy, location := none }]
                    returns := [{ name := none, ty := selfTy, location := none }]
                    body :=
                      some (Stmt.block
                        [Stmt.returnValues (some (Expr.ident "self"))]) } ] }
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "C"
            items :=
              [ ContractItem.usingDecl
                  { library := { segments := ["L"] }
                    functions := []
                    target := some targetTy
                    global := false }
              , ContractItem.function
                  { kind := FunctionKind.function
                    name := some "g"
                    visibility := some Visibility.external_
                    mutability := StateMutability.pure
                    params := [{ name := some "x", ty := argTy, location := none }]
                    returns := [{ name := none, ty := retTy, location := none }]
                    body :=
                      some (Stmt.block
                        [Stmt.returnValues
                          (some (Expr.call
                            (Expr.member (Expr.ident "x") "f") []))]) } ] } ] }

/-- WIDER receiver: `using L for uint256` + `f(uint8 self)`, receiver `uint256`.
`uint256` is NOT implicitly convertible to `uint8` — REJECT (matches solc). -/
def usingForWiderReceiverRejected : Bool :=
  TypeCheck.Result.isError
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (widenRejectSource (Ty.uint 8) (Ty.uint 256) (Ty.uint 256) (Ty.uint 8)))

#guard usingForWiderReceiverRejected

/-- INCOMPATIBLE: `using L for uint256` + `f(bytes32 self)`, receiver `uint256`.
`uint256` is not convertible to `bytes32` — REJECT (matches solc). -/
def usingForIncompatibleReceiverRejected : Bool :=
  TypeCheck.Result.isError
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (widenRejectSource (Ty.bytesN 32) (Ty.uint 256) (Ty.uint 256) (Ty.bytesN 32)))

#guard usingForIncompatibleReceiverRejected

/-- SIGNEDNESS: `using L for int8` + `f(uint256 self)`, receiver `int8`.
`int8` is not implicitly convertible to `uint256` — REJECT (matches solc). -/
def usingForSignednessReceiverRejected : Bool :=
  TypeCheck.Result.isError
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (widenRejectSource (Ty.uint 256) (Ty.int 8) (Ty.int 8) (Ty.uint 256)))

#guard usingForSignednessReceiverRejected

end UsingForWiden
end Witness
end Solidity
end SolidCore
