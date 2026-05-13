import SharedSemantics.Call

namespace SharedSemantics
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
  SharedSemantics.norm
    (bytes.foldl (fun acc b => acc * 256 + byte b) 0)

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

inductive Kind where
  | ecrecover
  | sha256
  | ripemd160
  deriving Repr, BEq, DecidableEq

def address : Kind -> Word
  | Kind.ecrecover => 1
  | Kind.sha256 => 2
  | Kind.ripemd160 => 3

def callKind : Call.ExternalCallKind :=
  Call.ExternalCallKind.staticcall

def lookup? (results : List Result) (kind : Kind) (input : Bytes) :
    Option Result :=
  Call.Result.lookup? results callKind (address kind) (normalizeBytes input)
    0 none

def outputWord? (result : Result) : Option Word :=
  if result.success then
    readWord? result.output 0
  else
    none

def lookupOutputWord? (results : List Result) (kind : Kind)
    (input : Bytes) : Option Word := do
  let result ← lookup? results kind input
  outputWord? result

def ecrecoverInput (digest v r s : Word) : Bytes :=
  wordBytesBE digest ++ wordBytesBE v ++ wordBytesBE r ++ wordBytesBE s

def ecrecover? (results : List Result) (digest v r s : Word) :
    Option Word :=
  lookupOutputWord? results Kind.ecrecover (ecrecoverInput digest v r s)

def ecrecoverAt (results : List Result) (digest v r s : Word) : Word :=
  (ecrecover? results digest v r s).getD 0

end Precompile
end SharedSemantics
