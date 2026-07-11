import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-INTERNAL-CALL-ARG (#174) — a direct internal call used as an argument
to the `abi.encode` / `abi.encodePacked` builtin.

solc accepts and lowers `abi.encode(g())` for an internal `g()` by evaluating the
call first and then ABI-encoding its result, so on the real EVM
`abi.encode(g())` (with `g()` returning `uint256(3)`) is the 32-byte word 3, and
`abi.encode(uint256(9), g())` is the two 32-byte words 9 and 3.

solidity-lean formerly ACCEPTED such a contract (`importedContractAccepted =
true`) but failed to LOWER it: the three `abi.*` member-call arms of
`Stmt.toCoreWithInternalCalls?` (RETURN, VAR-DECL, and DISCARD positions) fell
through to the env-less `Stmt.toCore?` WITHOUT invoking the argument-position
call hoister. `Stmt.toCore?` lowers each abi argument via `exprToCore?`, which
cannot lower an internal call, so the whole function returned `none` and the
contract's executable lowering was poisoned
(`TypeError.unsupported "checked executable checked contract C"`).

The fix routes those three arms through the EXISTING hoisting machinery before
the env-less fallback — exactly as the ident-call / tuple-return / newExpr arms
already do:
* RETURN and DISCARD positions use the block-wrapping `Stmt.argPositionHoist?`.
* VAR-DECL position uses the flat-prefix `Expr.argPositionHoistPrefix?` (so the
  declared local stays a SIBLING in scope for later statements).
The hoister peels the strictly-nested internal call into a prefix temp and
re-lowers `abi.encode((retTy)(_tmp))`, which lowers cleanly (a pure-local abi
arg). The generic argument-position walker `Expr.findArgPosInnerCall?` descends
through wrappers, so `abi.encode(uint256(g()) + 1)` and the call-in-2nd-arg case
`abi.encode(uint256(9), g())` are peeled too. It fires only when a nested call is
actually found, so every previously-accepted `abi.*` statement is byte-identical.

Real-EVM Forge ground truth: `tests/forge-harness/abi-encode-call-arg`.
`#eval`-confirmed runtime byte lists pinned with `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeCallArg

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def gcall : Expr := Expr.call (Expr.ident "g") []
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (lit "3"))]) }

private def bytesReturn (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

private def encVarDeclFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "encVarDecl",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [
      Stmt.varDecl [{ name := some "b", ty := Ty.bytes, location := some DataLocation.memory }]
        (some (abiEncode [Arg.positional gcall])),
      Stmt.returnValues (some (Expr.ident "b")) ]) }

private def encDiscardFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "encDiscard",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [
      Stmt.expr (abiEncode [Arg.positional gcall]),
      Stmt.returnValues (some (lit "7")) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "AbiEncodeCallArgTarget",
    abstract := false, bases := [],
    items := [ gFn,
      bytesReturn "encReturn" (abiEncode [Arg.positional gcall]),
      bytesReturn "encTwoArgs" (abiEncode [Arg.positional (u256 (lit "9")), Arg.positional gcall]),
      bytesReturn "encWrapper" (abiEncode [Arg.positional (Expr.binary BinaryOp.add (u256 gcall) (lit "1"))]),
      encVarDeclFn,
      encDiscardFn ] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeCallArg
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeCallArg

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AbiEncodeCallArg.importedContract

-- The imported contract type-checks (accepted): it was already accepted before
-- the fix; the fix restores its executable lowering.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallArg.importedContractAccepted

-- A 32-byte big-endian word as a raw byte list.
private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- Runtime byte lists (the abi.encode results), matched in full against the
-- real-EVM ABI encoding.
def encReturn_is_word3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "encReturn" State.empty [] (w32 3)

def encTwoArgs_is_words_9_3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "encTwoArgs" State.empty [] (w32 9 ++ w32 3)

def encWrapper_is_word4 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "encWrapper" State.empty [] (w32 4)

def encVarDecl_is_word3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "encVarDecl" State.empty [] (w32 3)

-- Discard position: the discarded `abi.encode(g())` lowers and runs, then the
-- function returns 7.
def encDiscard_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "encDiscard" State.empty [] 7

-- STAY MATCHING: `keccak256(abi.encode(g()))` already lowered (its ident-call
-- return path routes through the hoister) and must keep lowering. Assert the
-- concrete keccak of `abi.encode(uint256(3))` (32-byte word 3).
private def gcall : Expr := Expr.call (Expr.ident "g") []
private def abiEnc (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args

private def kecFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "kec",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.fixedBytes 32, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some
      (Expr.call (Expr.ident "keccak256") [Arg.positional (abiEnc [Arg.positional gcall])]))]) }

private def kecDecl : ContractDecl :=
  { SolidCore.Solidity.SolcAstImport.AbiEncodeCallArg.importedContractDecl0 with
    items := SolidCore.Solidity.SolcAstImport.AbiEncodeCallArg.importedContractDecl0.items
      ++ [kecFn] }

def keccak_still_lowers : Bool :=
  match SolidCore.Solidity.TypeCheck.CheckedInput.ownCall 256 kecDecl
      (CallTarget.name "kec") State.empty [] with
  | Except.ok (CallResult.returned _ _) => true
  | _ => false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue encReturn_is_word3
#guard isOkTrue encTwoArgs_is_words_9_3
#guard isOkTrue encWrapper_is_word4
#guard isOkTrue encVarDecl_is_word3
#guard isOkTrue encDiscard_is_7
#guard keccak_still_lowers

end AbiEncodeCallArg
end Witness
end Solidity
end SolidCore
