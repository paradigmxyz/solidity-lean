import SolidCore.Solidity.Shared.Call

namespace SolidCore.Solidity.Shared
namespace Precompile

abbrev Byte := Call.Byte
abbrev Bytes := Call.Bytes
abbrev Result := Call.Result Call.ExternalCallKind

def wordBytes : Nat := 32

def byte (value : Nat) : Byte :=
  Account.byte value

def normalizeBytes : Bytes → Bytes :=
  Account.normalizeBytes

def bytesToWordBE (bytes : Bytes) : Word :=
  SolidCore.Solidity.Shared.norm
    (bytes.foldl (fun acc b => acc * 256 + byte b) 0)

def bytesToNatBE (bytes : Bytes) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + byte b) 0

def wordToBytesBE : Nat -> Word -> Bytes
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [byte value]

def wordBytesBE (value : Word) : Bytes :=
  wordToBytesBE wordBytes value

def readWord? (bytes : Bytes) (offset : Nat) : Option Word :=
  let rest := (normalizeBytes bytes).drop offset
  if wordBytes <= rest.length then
    some (bytesToWordBE (rest.take wordBytes))
  else
    none

def natOfSliceRightPadded (bytes : Bytes) (offset width : Nat) : Nat :=
  let slice := (normalizeBytes bytes).drop offset |>.take width
  bytesToNatBE slice * 256 ^ (width - slice.length)

inductive Kind where
  | ecrecover
  | sha256
  | ripemd160
  | identity
  | modexp
  | bnAdd
  | bnMul
  | bnPairing
  | blake2f
  | pointEvaluation
  deriving Repr, BEq, DecidableEq

def address : Kind -> Word
  | Kind.ecrecover => 1
  | Kind.sha256 => 2
  | Kind.ripemd160 => 3
  | Kind.identity => 4
  | Kind.modexp => 5
  | Kind.bnAdd => 6
  | Kind.bnMul => 7
  | Kind.bnPairing => 8
  | Kind.blake2f => 9
  | Kind.pointEvaluation => 10

def mainnetKinds : List Kind :=
  [ Kind.ecrecover
  , Kind.sha256
  , Kind.ripemd160
  , Kind.identity
  , Kind.modexp
  , Kind.bnAdd
  , Kind.bnMul
  , Kind.bnPairing
  , Kind.blake2f
  , Kind.pointEvaluation ]

def callKind : Call.ExternalCallKind :=
  Call.ExternalCallKind.staticcall

def request (kind : Kind) (input : Bytes) (gas? : Option Word := none) :
    Call.Request Call.ExternalCallKind :=
  { kind := callKind
    target := address kind
    calldata := normalizeBytes input
    value := 0
    gas? := gas? }

def lookup? (results : List Result) (kind : Kind) (input : Bytes)
    (gas? : Option Word := none) :
    Option Result :=
  let req := request kind input (gas? := gas?)
  Call.Result.lookup? results req.kind req.target req.calldata req.value req.gas?

-- Precompile-alignment (2026-07-06 decision): the identity/modexp *computation*
-- (`successfulStaticcall`/`identityStaticcall`/`expMod`/`modexpOutput`/
-- `modexpStaticcall`/`builtinStaticcallResult?`) has been removed from the
-- semantics — precompiles are ordinary external calls answered by the open-world
-- environment (responder), matching evm-compiler, with no in-semantics
-- computation. `modexpInput` (input encoding, not computation) stays; it builds
-- a staticcall's calldata and is still used by a witness.

def modexpInput (base exponent modulus : Bytes) : Bytes :=
  wordBytesBE base.length ++
    wordBytesBE exponent.length ++
    wordBytesBE modulus.length ++
    normalizeBytes base ++
    normalizeBytes exponent ++
    normalizeBytes modulus


def outputWord? (result : Result) : Option Word :=
  if result.success then
    readWord? result.output 0
  else
    none

def lookupOutputWord? (results : List Result) (kind : Kind)
    (input : Bytes) (gas? : Option Word := none) : Option Word := do
  let result ← lookup? results kind input (gas? := gas?)
  outputWord? result

def ecrecoverInput (digest v r s : Word) : Bytes :=
  wordBytesBE digest ++ wordBytesBE v ++ wordBytesBE r ++ wordBytesBE s

def ecrecover? (results : List Result) (digest v r s : Word) :
    Option Word :=
  lookupOutputWord? results Kind.ecrecover (ecrecoverInput digest v r s)

def ecrecoverAt (results : List Result) (digest v r s : Word) : Word :=
  (ecrecover? results digest v r s).getD 0

end Precompile
end SolidCore.Solidity.Shared
