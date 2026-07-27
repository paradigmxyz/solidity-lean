import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-NEG-LITERAL (S, abi-encode-rational) — a bare NEGATIVE integer literal
used directly as an `abi.encode` argument.

`return abi.encode(1, -2);`: solc types `1` as `uint8` and `-2` as `int8`, and
`abi.encode` pads/sign-extends each to a 32-byte word, so the encoded content is
`0x…0001` followed by `0x…fffe` (`-2` in 2's-complement). solidity-lean lowers the
negated literal `-2` via the `UnaryOp.neg` fold to an `Expr.intWord` (a signed
constant), which evaluates to a `Value.int`, while the env-less `Expr.abiTy?`
reports the negation's magnitude type `uint256` (`Literal.number ⇒ uint256`,
`neg` recurses). So the argument reaches a `uint256` abi slot at RUNTIME as a
`Value.int`. `abiStaticBytes?` had arms for `uint256/Value.word`, `int256/
Value.int`, and `int256/Value.word`, but NOT `uint256/Value.int`, so the value
fell through to `none` → `RevertData.typeMismatch` = a SPURIOUS `Panic(0)`
(revert-vs-success), where solc+EVM succeed with the two words.

This is the dual of ABI-ENCODE-SIGNED-CONST-SHIFT (`int256/Value.word`): here a
folded signed constant reaches a `uint256` slot as a `Value.int`. A full-width
32-byte abi word is byte-identical whether tagged int or uint (both dump the 256
2's-complement bits), so encoding the word bits directly is correct.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeNegLiteral

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def neg (e : Expr) : Expr := Expr.unary UnaryOp.neg e

private def bytesFn (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `abi.encode(1, -2)` = the two 32-byte words `1` and `-2`.
private def fFn : ContractItem :=
  bytesFn "f" (abiEncode [Arg.positional (num "1"), Arg.positional (neg (num "2"))])
-- CONTROL (single negative literal): `abi.encode(-2)` = the 32-byte word `-2`.
private def gFn : ContractItem :=
  bytesFn "g" (abiEncode [Arg.positional (neg (num "2"))])
-- CONTROL (all positive, already agreed): `abi.encode(1, 2)` = words `1`, `2`.
private def hFn : ContractItem :=
  bytesFn "h" (abiEncode [Arg.positional (num "1"), Arg.positional (num "2")])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [fFn, gFn, hFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeNegLiteral
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeNegLiteral

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeNegLiteral.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeNegLiteral.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n
private def wNeg (n : Int) : List Nat :=
  SolidCore.Solidity.Source.wordToBytesBE 32
    (SolidCore.Solidity.Shared.signedToWord n)

-- `f()`: `abi.encode(1, -2)` = word 1 ++ word (-2), NOT the spurious Panic(0).
def f_encodes_1_neg2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty [] (w32 1 ++ wNeg (-2))
def g_encodes_neg2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "g" State.empty [] (wNeg (-2))
def h_encodes_1_2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "h" State.empty [] (w32 1 ++ w32 2)

#guard accepted
#guard isOkTrue f_encodes_1_neg2
#guard isOkTrue g_encodes_neg2
#guard isOkTrue h_encodes_1_2

end AbiEncodeNegLiteral
end Witness
end Solidity
end SolidCore
