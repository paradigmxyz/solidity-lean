import SharedSemantics.Word

namespace SharedSemantics
namespace Block

abbrev WordMap := List (Word × Word)

def wordEq (lhs rhs : Word) : Bool :=
  norm lhs == norm rhs

def lookupWord? : WordMap → Word → Option Word
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if wordEq candidate key then
        some (norm value)
      else
        lookupWord? rest key

def wordListAt (values : List Word) (index : Word) : Word :=
  norm ((values[norm index]?).getD 0)

def blobHashAt (hashes : List Word) (index : Word) : Word :=
  wordListAt hashes index

def blockhashNumberInRange (current requested : Word) : Bool :=
  let current := norm current
  let requested := norm requested
  requested < current && current - requested <= 256

def blockHashAt (current : Word) (hashes : WordMap)
    (requested : Word) : Word :=
  if blockhashNumberInRange current requested then
    (lookupWord? hashes requested).getD 0
  else
    0

structure BlockEnv where
  basefee : Word
  blobbasefee : Word
  chainid : Word
  coinbase : Word
  difficulty : Word
  gaslimit : Word
  number : Word
  prevrandao : Word
  timestamp : Word
  blockHashes : WordMap
  deriving Repr

namespace BlockEnv

def empty : BlockEnv :=
  { basefee := 0
    blobbasefee := 0
    chainid := 0
    coinbase := 0
    difficulty := 0
    gaslimit := 0
    number := 0
    prevrandao := 0
    timestamp := 0
    blockHashes := [] }

inductive WordField where
  | basefee
  | blobbasefee
  | chainid
  | coinbase
  | difficulty
  | gaslimit
  | number
  | prevrandao
  | timestamp
  deriving Repr, DecidableEq

def evalWord (env : BlockEnv) : WordField → Word
  | WordField.basefee => norm env.basefee
  | WordField.blobbasefee => norm env.blobbasefee
  | WordField.chainid => norm env.chainid
  | WordField.coinbase => norm env.coinbase
  | WordField.difficulty => norm env.difficulty
  | WordField.gaslimit => norm env.gaslimit
  | WordField.number => norm env.number
  | WordField.prevrandao => norm env.prevrandao
  | WordField.timestamp => norm env.timestamp

def blockhash (env : BlockEnv) (requested : Word) : Word :=
  blockHashAt env.number env.blockHashes requested

end BlockEnv

structure TxEnv where
  gasprice : Word
  origin : Word
  blobHashes : List Word
  deriving Repr

namespace TxEnv

def empty : TxEnv :=
  { gasprice := 0
    origin := 0
    blobHashes := [] }

inductive WordField where
  | gasprice
  | origin
  deriving Repr, DecidableEq

def evalWord (env : TxEnv) : WordField → Word
  | WordField.gasprice => norm env.gasprice
  | WordField.origin => norm env.origin

def blobhash (env : TxEnv) (index : Word) : Word :=
  blobHashAt env.blobHashes index

end TxEnv

end Block
end SharedSemantics
