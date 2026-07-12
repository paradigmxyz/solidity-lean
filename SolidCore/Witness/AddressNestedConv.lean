import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ADDRESS-NESTED-CONVERSION (#181) — `address(address(address(<const>)))`.

A chain of >= 3 consecutive non-payable `address(...)` conversions whose
innermost argument is a CONSTANT literal (number / hex / arith-folded) is
ACCEPTED by pinned solc 0.8.35 and behaves as the identity on the folded
address value, so `address(address(address(0x1234)))` = `address(0x1234)` =
`0x1234` (= 4660) on the real EVM (`tests/forge-harness/address-nested-conv`,
Forge/anvil ground truth).

solidity-lean accepted the contract at typecheck but FAILED TO LOWER the nested
chain: `Expr.toCore?`'s nonpayable-`address` arm (`Interface.lean`) folded a
BARE literal via `toCoreAddressLiteral?`, else bailed with `none` whenever
`isAddressLiteralCandidate` held. At depth >= 3 the inner argument is itself an
`address(...)` call, for which `isAddressLiteralCandidate` returns `true` (it
recurses into the literal) while `toCoreAddressLiteral?` returns `none` (it only
folds bare literals) — so the arm bailed and returned `TypeError.unsupported`,
POISONING the whole contract (every function, even unrelated ones, then failed).
depth-2 already worked (bare-literal fold); a depth-3 chain over a PARAMETER
worked (the `else` recursion). The payable sibling arm (`payable(address(...))`)
had the identical structure.

The fix: in both arms, bail with `none` ONLY for a genuine bare-literal
candidate (`isAddressLiteralCandidate && !isConversionCall`); when the argument
is itself a nested conversion call, recurse via `Expr.toCore?` so the inner cast
lowers. A genuinely out-of-range bare inner literal stays rejected (the inner
fold returns `none`, matching solc).

Values pinned by `#guard` against real-EVM Forge ground truth, both via own-call
execution AND via whole-program `callContract` lowering (the path that
exhibited the poisoning).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AddressNestedConv

def importedSourceName : String := "tests/forge-harness/address-nested-conv/src/AddressNestedConv.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "AddressNestedConvTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "d3",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "d4",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "p3",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address true, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.payableConversion (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])])])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "d2",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "0x1234"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "7")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AddressNestedConv
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AddressNestedConv

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AddressNestedConv.importedContract

def importedSourceUnit : SourceUnit :=
  SolidCore.Solidity.SolcAstImport.AddressNestedConv.importedSourceUnit

-- The imported contract type-checks (accepted): the nested-`address` chains and
-- the unrelated function all pass the acceptance predicate.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AddressNestedConv.importedContractAccepted

-- Own-call execution: each function returns its real-EVM word (address chains
-- collapse to 0x1234 = 4660; the unrelated `h` returns 7).
def d3_is_4660 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "d3" State.empty [] 4660
def d4_is_4660 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "d4" State.empty [] 4660
def p3_is_4660 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "p3" State.empty [] 4660
def d2_is_4660 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "d2" State.empty [] 4660
def h_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "h" State.empty [] 7

-- Whole-program `callContract` lowering — the path that exhibited the #181
-- poisoning. Returns whether the runtime word of a single-word result matches.
def wpWordEq (fn : Name) (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 300 importedSourceUnit "AddressNestedConvTarget"
      (CallTarget.name fn) State.empty []
  match result with
  | CallResult.returned _ [Value.word v] => Except.ok (wordEq v expected)
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue d3_is_4660
#guard isOkTrue d4_is_4660
#guard isOkTrue p3_is_4660
#guard isOkTrue d2_is_4660
#guard isOkTrue h_is_7

-- Whole-program lowering succeeds for every function (no TypeError.unsupported)
-- and pins the identity-chain / unrelated values.
#guard isOkTrue (wpWordEq "d3" 4660)
#guard isOkTrue (wpWordEq "d4" 4660)
#guard isOkTrue (wpWordEq "p3" 4660)
#guard isOkTrue (wpWordEq "d2" 4660)
#guard isOkTrue (wpWordEq "h" 7)

end AddressNestedConv
end Witness
end Solidity
end SolidCore
