/-
STRINGCONCAT-HEXLIT-UTF8 witnesses (divergence #152).

Pinned solc 0.8.35 ACCEPTS `string.concat(<hex-string literal>)` exactly when the
literal's decoded bytes are valid UTF-8, because `string.concat`
(`typeCheckStringConcatFunction`, TypeChecker.cpp) accepts any argument that
`isImplicitlyConvertibleTo(string memory)`, and for a `StringLiteralType`
(Types.cpp) that conversion succeeds iff the literal is valid UTF-8
(`util::validateUTF8`). solidity-lean formerly REJECTED every hex-string literal
here because `checkStringConcatArgs` inspected only the argument's `Ty`
(`isStringConcatArg`, which accepts `Ty.string` only) — and a hex-string literal
is typed `Ty.bytes`, so it was rejected regardless of UTF-8 validity.

Probed against pinned solc (`solc-0.8.35 --bin`):
  * `string.concat(hex"61")`         accepts (0x61 == "a", valid UTF-8)
  * `string.concat("a", hex"62")`    accepts ("ab")
  * `string.concat(hex"e298ba")`     accepts ("☺", valid 3-byte UTF-8)
  * `string.concat(hex"ff")`         REJECTS (Error 9977, 0xff not valid UTF-8)
  * `string.concat(uint8(1))`        REJECTS (number/typed-int not a string)
  * `string.concat(bytes-literal)`   REJECTS

Runtime ground truth from a real EVM: pinned-solc runtime code deployed to anvil
and called with `cast`:
  * `f() = string.concat(hex"61")`        -> abi string "a"  (0x61)
  * `f() = string.concat("a", hex"62")`   -> abi string "ab" (0x6162)
  * `f() = string.concat("x", hex"79")`   -> abi string "xy" (0x7879)
The `abiString`/`wordN` helpers below reconstruct those exact return words.
-/
import SolidCore.Witness.Checked

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

/-- `string.concat(args)` as a builtin member-call expression. -/
private def stringConcatCall (args : List Solidity.Arg) : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.member (Solidity.Expr.ident "string") "concat") args

private def hexArg (text : String) : Solidity.Arg :=
  Solidity.Arg.positional (Solidity.Expr.literal (Solidity.Literal.hexString text))

private def strArg (text : String) : Solidity.Arg :=
  Solidity.Arg.positional (Solidity.Expr.literal (Solidity.Literal.string text))

private def stringConcatSourceUnit (name : String) (args : List Solidity.Arg) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := name
            items :=
              [ Solidity.ContractItem.function
                  { stringReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (stringConcatCall args))) } ] } ] }

-- Acceptance boundary (typechecker) --------------------------------------------

def hexLitStringConcatAccepted : Bool :=
  sourceUnitAccepted? (stringConcatSourceUnit "HexLit" [hexArg "61"])

def mixedHexLitStringConcatAccepted : Bool :=
  sourceUnitAccepted? (stringConcatSourceUnit "MixedHexLit" [strArg "a", hexArg "62"])

def multibyteHexLitStringConcatAccepted : Bool :=
  sourceUnitAccepted? (stringConcatSourceUnit "MultibyteHexLit" [hexArg "e298ba"])

/-- Non-UTF-8 hex-string literal must still REJECT (solc Error 9977). -/
def nonUtf8HexLitStringConcatRejected : Bool :=
  Result.isError (SourceUnit.check (stringConcatSourceUnit "NonUtf8HexLit" [hexArg "ff"]))

/-- Surrogate-range 3-byte sequence (`0xED 0xA0 0x80`) must still REJECT. -/
def surrogateHexLitStringConcatRejected : Bool :=
  Result.isError
    (SourceUnit.check (stringConcatSourceUnit "SurrogateHexLit" [hexArg "eda080"]))

/-- Overlong 2-byte lead (`0xC0`) must still REJECT. -/
def overlongHexLitStringConcatRejected : Bool :=
  Result.isError
    (SourceUnit.check (stringConcatSourceUnit "OverlongHexLit" [hexArg "c0"]))

/-- A typed integer argument (`uint8(1)`) must still REJECT. -/
def numberStringConcatRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (stringConcatSourceUnit "NumberConcat"
        [ Solidity.Arg.positional
            (Solidity.Expr.call
              (Solidity.Expr.typeName (Solidity.Ty.uint 8))
              [Solidity.Arg.positional
                (Solidity.Expr.literal (Solidity.Literal.number "1"))]) ]))

/-- A bytes literal argument must still REJECT. -/
def bytesLitStringConcatRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (stringConcatSourceUnit "BytesLitConcat"
        [Solidity.Arg.positional
          (Solidity.Expr.literal (Solidity.Literal.bytes [1]))]))

def hexLitStringConcatBoundaryHolds : Bool :=
  hexLitStringConcatAccepted &&
    mixedHexLitStringConcatAccepted &&
    multibyteHexLitStringConcatAccepted &&
    nonUtf8HexLitStringConcatRejected &&
    surrogateHexLitStringConcatRejected &&
    overlongHexLitStringConcatRejected &&
    numberStringConcatRejected &&
    bytesLitStringConcatRejected

#guard hexLitStringConcatBoundaryHolds

-- Runtime witnesses (interpreter output == real EVM) ---------------------------

/-- Left of a 32-byte word holding the small nat `n`. -/
private def wordN (n : Nat) : List Byte := List.replicate 31 0 ++ [n]

/-- Right-pad a byte run to a full 32-byte word. -/
private def padR32 (bs : List Byte) : List Byte :=
  bs ++ List.replicate (32 - bs.length) 0

/-- The ABI return encoding for a single `string memory` value `bs`
(offset 0x20, length, then the right-padded data word) — as produced by a real
EVM (verified against anvil/cast for the three cases below). -/
private def abiString (bs : List Byte) : List Byte :=
  wordN 0x20 ++ wordN bs.length ++ padR32 bs

/-- Contract exercised at runtime; each `join*` returns a `string memory`. -/
def stringConcatHexLitContract : Solidity.ContractDecl :=
  { name := "StringConcatHexLit"
    items :=
      [ Solidity.ContractItem.function
          { stringReturnFunction with
            name := some "joinHex"
            body := some (Solidity.Stmt.returnValues
              (some (stringConcatCall [hexArg "61"]))) }
      , Solidity.ContractItem.function
          { stringReturnFunction with
            name := some "joinMixed"
            body := some (Solidity.Stmt.returnValues
              (some (stringConcatCall [strArg "a", hexArg "62"]))) }
      , Solidity.ContractItem.function
          { stringReturnFunction with
            name := some "joinXy"
            body := some (Solidity.Stmt.returnValues
              (some (stringConcatCall [strArg "x", hexArg "79"]))) } ] }

private def exceptOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

/-- `string.concat(hex"61") == "a"` (0x61). -/
def joinHexRuntimeMatches : Except TypeError Bool :=
  checkedContractAbiOutputMatches 256 stringConcatHexLitContract "joinHex" []
    (some (abiString [0x61]))

/-- `string.concat("a", hex"62") == "ab"` (0x6162). -/
def joinMixedRuntimeMatches : Except TypeError Bool :=
  checkedContractAbiOutputMatches 256 stringConcatHexLitContract "joinMixed" []
    (some (abiString [0x61, 0x62]))

/-- `string.concat("x", hex"79") == "xy"` (0x7879). -/
def joinXyRuntimeMatches : Except TypeError Bool :=
  checkedContractAbiOutputMatches 256 stringConcatHexLitContract "joinXy" []
    (some (abiString [0x78, 0x79]))

def stringConcatHexLitRuntimeHolds : Bool :=
  exceptOkTrue joinHexRuntimeMatches &&
    exceptOkTrue joinMixedRuntimeMatches &&
    exceptOkTrue joinXyRuntimeMatches

#guard exceptOkTrue joinHexRuntimeMatches
#guard exceptOkTrue joinMixedRuntimeMatches
#guard exceptOkTrue joinXyRuntimeMatches
#guard stringConcatHexLitRuntimeHolds

end Examples
end TypeCheck
end Solidity
end SolidCore
