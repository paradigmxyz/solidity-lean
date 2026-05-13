import SharedSemantics.Word

namespace SharedSemantics
namespace Account

abbrev Byte := Nat
abbrev Bytes := List Byte
abbrev WordMap := List (Word × Word)
abbrev BytesMap := List (Word × Bytes)

def byte (value : Nat) : Byte :=
  value % 256

def normalizeBytes (bytes : Bytes) : Bytes :=
  bytes.map byte

def bytesEq (lhs rhs : Bytes) : Bool :=
  normalizeBytes lhs == normalizeBytes rhs

def wordEq (lhs rhs : Word) : Bool :=
  norm lhs == norm rhs

def addressModulus : Nat := 2 ^ 160

def addressWord (address : Word) : Word :=
  norm address % addressModulus

def lookupWord? : WordMap → Word → Option Word
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if wordEq candidate key then
        some (norm value)
      else
        lookupWord? rest key

def lookupBytes? : BytesMap → Word → Option Bytes
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if wordEq candidate key then
        some (normalizeBytes value)
      else
        lookupBytes? rest key

def balanceAt (balances : WordMap) (address : Word) : Word :=
  (lookupWord? balances address).getD 0

def codehashAt (codehashes : WordMap) (address : Word) : Word :=
  (lookupWord? codehashes address).getD 0

def codeAt (codes : BytesMap) (address : Word) : Bytes :=
  (lookupBytes? codes address).getD []

structure EcrecoverSignature where
  v : Word := 0
  r : Word := 0
  s : Word := 0
  deriving DecidableEq, Repr

namespace EcrecoverSignature

def matches? (lhs rhs : EcrecoverSignature) : Bool :=
  wordEq lhs.v rhs.v && wordEq lhs.r rhs.r && wordEq lhs.s rhs.s

end EcrecoverSignature

abbrev EcrecoverMap := List (Word × EcrecoverSignature × Word)

def lookupEcrecover? : EcrecoverMap → Word → EcrecoverSignature → Option Word
  | [], _, _ => none
  | (candidateDigest, candidateSignature, address) :: rest, digest, signature =>
      if wordEq candidateDigest digest &&
          EcrecoverSignature.matches? candidateSignature signature then
        some (addressWord address)
      else
        lookupEcrecover? rest digest signature

def ecrecoverAt (results : EcrecoverMap) (digest : Word)
    (signature : EcrecoverSignature) : Word :=
  (lookupEcrecover? results digest signature).getD 0

end Account
end SharedSemantics
