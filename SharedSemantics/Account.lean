import SharedSemantics.Block
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

def addressIn (address : Word) : List Word -> Bool
  | [] => false
  | candidate :: rest =>
      wordEq (addressWord candidate) (addressWord address) ||
        addressIn address rest

structure SelfdestructRecord where
  fromAddress : Word
  recipient : Word
  deletesAccount : Bool := true
  deriving Repr

def selfdestructDeletesAccount
    (evmVersion : Block.EvmVersion) (createdThisTransaction : Bool) :
    Bool :=
  !evmVersion.cancunOrLater || createdThisTransaction

def selfdestructRecord (evmVersion : Block.EvmVersion)
    (createdAccounts : List Word) (self recipient : Word) :
    SelfdestructRecord :=
  let selfAddress := addressWord self
  { fromAddress := selfAddress
    recipient := addressWord recipient
    deletesAccount :=
      selfdestructDeletesAccount evmVersion
        (addressIn selfAddress createdAccounts) }

end Account
end SharedSemantics
