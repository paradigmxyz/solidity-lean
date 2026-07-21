import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EVENT-OVERLOAD-TABLE (soundness) — same-contract event OVERLOADS resolve by
SIGNATURE, not by name.

```solidity
contract C {
    event E(uint256 v);
    event E(address who);
    function fireWord() external { uint256 v = 5; emit E(v); }
    function fireAddr(address a) external { emit E(a); }
}
```

solc allows same-scope event overloads (error 5883 only rejects EQUAL
parameter types) and resolves each `emit E(...)` by argument types, so
`fireAddr` emits topic0 = keccak256("E(address)").

solidity-lean's runtime event table was keyed by NAME only
(`Context.eventDecl?` = `find?` on `name`), so BOTH emits bound the FIRST decl
named `E`: `fireAddr` emitted topic0 = keccak256("E(uint256)") — the WRONG
topic0 (or, for arity/type-incompatible overloads, a spurious typeMismatch
revert).

Fix: the lowering pass `Stmt.resolveOverloadedEventEmits` (threading the same
TypeEnv `annotateAbi` uses) rewrites an overloaded bare-name emit to the
resolved decl's canonical-ABI-signature key (`"E(uint256)"` /
`"E(address)"` — parentheses never collide with identifiers), and the
contract assembly registers signature-keyed event-table entries for every
overloaded name. Non-overloaded contracts are untouched byte-identically.

Real-EVM ground truth (forge lane `event-overload`): `fireWord()` emits
topic0 = keccak256("E(uint256)") with data = abi.encode(5); `fireAddr(a)`
emits topic0 = keccak256("E(address)") with data = abi.encode(a).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EventOverloadTable

private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def fireWordFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "fireWord",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.varDecl
            [{ name := some "v", ty := Ty.uint 256 }] (some (lit "5"))
        , Stmt.emitEvent
            (Expr.call (Expr.ident "E") [Arg.positional (Expr.ident "v")]) ]) }

private def fireAddrFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "fireAddr",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [{ name := some "a", ty := Ty.address false }], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.emitEvent
            (Expr.call (Expr.ident "E") [Arg.positional (Expr.ident "a")]) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.eventDecl
          { name := "E"
            params := [{ name := some "v", ty := Ty.uint 256 }] }
      , ContractItem.eventDecl
          { name := "E"
            params := [{ name := some "who", ty := Ty.address false }] }
      , fireWordFn
      , fireAddrFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EventOverloadTable
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EventOverloadTable

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.EventOverloadTable.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EventOverloadTable.importedContractAccepted

private def singleEventMatches (which : String)
    (args : List SolidCore.Solidity.Source.Value)
    (signature : String) (dataWord : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 Fam
      (SolidCore.Solidity.Source.CallTarget.name which)
      SolidCore.Solidity.Source.State.empty args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.topics ==
                [SolidCore.Solidity.Source.Keccak.digestWord signature] &&
              event.dataBytes ==
                SolidCore.Solidity.Source.wordToBytesBE
                  SolidCore.Solidity.Source.wordBytes dataWord)
      | _ => Except.ok false
  | _ => Except.ok false

-- `fireWord()` resolves the `E(uint256)` overload: topic0 is the keccak of
-- THAT canonical signature and the data word is 5.
def fireWord_uses_uint_overload : Except TypeError Bool :=
  singleEventMatches "fireWord" [] "E(uint256)" 5

-- `fireAddr(0xabcd)` resolves the `E(address)` overload — pre-fix the
-- name-keyed table bound the FIRST decl named `E` and emitted topic0 =
-- keccak("E(uint256)") (WRONG); solc+EVM emit keccak("E(address)").
def fireAddr_uses_address_overload : Except TypeError Bool :=
  singleEventMatches "fireAddr" [Value.word 0xabcd] "E(address)" 0xabcd

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue fireWord_uses_uint_overload
#guard isOkTrue fireAddr_uses_address_overload

end EventOverloadTable
end Witness
end Solidity
end SolidCore
