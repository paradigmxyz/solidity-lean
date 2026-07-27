import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-ADDRESS-OF-BYTESN (S, address-converted-from-bytes20-as-abi-encoder-argument)
— an `address` obtained by CONVERTING a `bytes20` and used DIRECTLY as an
`abi.encode`/`abi.encodePacked` argument.

  bytes20 b = hex"00112233445566778899aabbccddeeff00112233";
  return abi.encode(address(b));   // 32-byte left-padded address

solc 0.8.35 + EVM encode the address as the 32-byte left-padded word
(`0x00…00112233445566778899aabbccddeeff00112233`). solidity-lean reverted with
`Panic(0)`.

ROOT CAUSE: `address(bytes20 x)` lowers as an IDENTITY with no core node
(VALUE_TYPING_DESIGN.md §1), so the R3 width-tagged `Value.fixedBytes 20 w`
reaches the ABI encoder while the DECLARED type is `address`. The static scalar
encoders (`abiStaticBytes?` / `abiEncodePackedValue?`) had a `Ty.address,
Value.word` arm but NO `Ty.address, Value.fixedBytes` arm, so the tagged word
fell through to `none` → `RevertData.typeMismatch` = a spurious `Panic(0)`.
`Ty.coerceValue?` was already taught to be tag-agnostic for `address` (post-gate
hardening item 1); the encoder head arms were the missed sibling.

The fix mirrors the `Ty.fixedBytes, Value.fixedBytes` arm already present: an
`address` slot holding a `Value.fixedBytes _ w` encodes byte-identically to the
`Value.word w` case (the low 20 bytes are the address; the tag never changed the
word bits). CONTROL: binding to an `address` local first (`address a = address(b);
abi.encode(a)`) already agrees — the local decl routes through `Ty.coerceValue?`
which untags — so that path stays byte-identical.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeAddressOfBytesN

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def abiEncodePacked (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args
private def hexLit (s : String) : Expr := Expr.literal (Literal.hexString s)
private def addr (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.address false)) [Arg.positional e]

private def bLit : String := "00112233445566778899aabbccddeeff00112233"

private def bytesFn (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl
          [ { name := some "b", ty := some (Ty.bytesN 20), location := none } ]
          (some (hexLit bLit))
      , Stmt.returnValues (some e) ]) }

-- The submission `f()`: `abi.encode(address(b))` = the 32-byte left-padded address.
private def fFn : ContractItem :=
  bytesFn "f" (abiEncode [Arg.positional (addr (Expr.ident "b"))])
-- FAMILY: same trigger under `abi.encodePacked` — packed `address` is 20 bytes.
private def fpFn : ContractItem :=
  bytesFn "fp" (abiEncodePacked [Arg.positional (addr (Expr.ident "b"))])
-- CONTROL (bind to an `address` local FIRST, already agreed): the local decl
-- untags via `Ty.coerceValue?`, so `abi.encode(a)` encodes fine.
private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl
          [ { name := some "b", ty := some (Ty.bytesN 20), location := none } ]
          (some (hexLit bLit))
      , Stmt.varDecl
          [ { name := some "a", ty := some (Ty.address false), location := none } ]
          (some (addr (Expr.ident "b")))
      , Stmt.returnValues (some (abiEncode [Arg.positional (Expr.ident "a")])) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [fFn, fpFn, gFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeAddressOfBytesN
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeAddressOfBytesN

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeAddressOfBytesN.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeAddressOfBytesN.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def addrNat : Nat := 0x00112233445566778899aabbccddeeff00112233
private def w32addr : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 addrNat
private def packedAddr : List Nat := SolidCore.Solidity.Source.wordToBytesBE 20 addrNat

-- The submission `f()`: `abi.encode(address(b))` = the 32-byte left-padded
-- address (solc+EVM), NOT the spurious `Panic(0)` the tagged-word path produced.
def f_encodes_addr : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty [] w32addr
def fp_encodes_addr : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fp" State.empty [] packedAddr
def g_encodes_addr : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "g" State.empty [] w32addr

#guard accepted
#guard isOkTrue f_encodes_addr
#guard isOkTrue fp_encodes_addr
#guard isOkTrue g_encodes_addr

end AbiEncodeAddressOfBytesN
end Witness
end Solidity
end SolidCore
