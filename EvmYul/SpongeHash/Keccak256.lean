import Std

namespace EvmYul
namespace SpongeHash
namespace Keccak256

abbrev Byte := Nat

def word64 : Nat := 18446744073709551616
def mask64 : Nat := 18446744073709551615

def u64 (n : Nat) : Nat :=
  n % word64

def bxor (a b : Nat) : Nat :=
  u64 (Nat.xor (u64 a) (u64 b))

def band (a b : Nat) : Nat :=
  u64 (Nat.land (u64 a) (u64 b))

def bnot (a : Nat) : Nat :=
  mask64 - u64 a

def rotl64 (x r : Nat) : Nat :=
  let x := u64 x
  if r % 64 == 0 then
    x
  else
    u64 (((x * (2 ^ (r % 64))) % word64) + (x / (2 ^ (64 - r % 64))))

def getD (xs : List Nat) (i : Nat) : Nat :=
  xs.getD i 0

def setD : List Nat -> Nat -> Nat -> List Nat
  | [], _, _ => []
  | _ :: xs, 0, value => value :: xs
  | x :: xs, i + 1, value => x :: setD xs i value

def laneIndex (x y : Nat) : Nat :=
  (x % 5) + 5 * (y % 5)

def lane (st : List Nat) (x y : Nat) : Nat :=
  getD st (laneIndex x y)

def xorList : List Nat -> Nat
  | [] => 0
  | x :: xs => bxor x (xorList xs)

def columnXor (st : List Nat) (x : Nat) : Nat :=
  xorList ((List.range 5).map fun y => lane st x y)

def rhoOffset (x y : Nat) : Nat :=
  match x % 5, y % 5 with
  | 0, 0 => 0  | 0, 1 => 36 | 0, 2 => 3  | 0, 3 => 41 | 0, _ => 18
  | 1, 0 => 1  | 1, 1 => 44 | 1, 2 => 10 | 1, 3 => 45 | 1, _ => 2
  | 2, 0 => 62 | 2, 1 => 6  | 2, 2 => 43 | 2, 3 => 15 | 2, _ => 61
  | 3, 0 => 28 | 3, 1 => 55 | 3, 2 => 25 | 3, 3 => 21 | 3, _ => 56
  | _, 0 => 27 | _, 1 => 20 | _, 2 => 39 | _, 3 => 8  | _, _ => 14

def roundConstants : List Nat :=
  [0x0000000000000001, 0x0000000000008082,
   0x800000000000808A, 0x8000000080008000,
   0x000000000000808B, 0x0000000080000001,
   0x8000000080008081, 0x8000000000008009,
   0x000000000000008A, 0x0000000000000088,
   0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B,
   0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080,
   0x000000000000800A, 0x800000008000000A,
   0x8000000080008081, 0x8000000000008080,
   0x0000000080000001, 0x8000000080008008]

def theta (st : List Nat) : List Nat :=
  let c := (List.range 5).map fun x => columnXor st x
  let d := (List.range 5).map fun x =>
    bxor (getD c ((x + 4) % 5)) (rotl64 (getD c ((x + 1) % 5)) 1)
  (List.range 25).map fun i =>
    bxor (getD st i) (getD d (i % 5))

def rhoPiSet (a : List Nat) (x y : Nat) (b : List Nat) : List Nat :=
  let dest := y + 5 * ((2 * x + 3 * y) % 5)
  setD b dest (rotl64 (lane a x y) (rhoOffset x y))

def rhoPi (st : List Nat) : List Nat :=
  Id.run do
    let mut b := List.replicate 25 0
    for y in List.range 5 do
      for x in List.range 5 do
        b := rhoPiSet st x y b
    pure b

def chi (b : List Nat) : List Nat :=
  (List.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    bxor (lane b x y) (band (bnot (lane b (x + 1) y)) (lane b (x + 2) y))

def iota (st : List Nat) (rc : Nat) : List Nat :=
  setD st 0 (bxor (getD st 0) rc)

def round (st : List Nat) (rc : Nat) : List Nat :=
  iota (chi (rhoPi (theta st))) rc

def permute : List Nat -> List Nat -> List Nat
  | st, [] => st
  | st, rc :: rest => permute (round st rc) rest

def keccakF1600 (st : List Nat) : List Nat :=
  permute st roundConstants

def byteShift (i : Nat) : Nat :=
  2 ^ (8 * (i % 8))

def absorbByte (st : List Nat) (i byte : Nat) : List Nat :=
  let li := i / 8
  let value := bxor (getD st li) ((byte % 256) * byteShift i)
  setD st li value

def absorbBlockFrom : List Nat -> Nat -> List Byte -> List Nat
  | st, _, [] => st
  | st, i, byte :: bytes =>
      absorbBlockFrom (absorbByte st i byte) (i + 1) bytes

def absorbBlock (st : List Nat) (block : List Byte) : List Nat :=
  keccakF1600 (absorbBlockFrom st 0 block)

def rateBytes : Nat := 136

def padKeccak (msg : List Byte) : List Byte :=
  let rem := msg.length % rateBytes
  let padLen := rateBytes - rem
  if padLen == 1 then
    msg ++ [0x81]
  else
    msg ++ [0x01] ++ List.replicate (padLen - 2) 0 ++ [0x80]

def chunksOfWithFuel : Nat -> Nat -> List Byte -> List (List Byte)
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, n, bytes =>
      bytes.take n :: chunksOfWithFuel fuel n (bytes.drop n)

def chunksOf (n : Nat) (bytes : List Byte) : List (List Byte) :=
  if n == 0 then
    []
  else
    chunksOfWithFuel (bytes.length + 1) n bytes

def absorbBlocks : List Nat -> List (List Byte) -> List Nat
  | st, [] => st
  | st, block :: blocks => absorbBlocks (absorbBlock st block) blocks

def laneByte (lane : Nat) (i : Nat) : Byte :=
  (lane / (2 ^ (8 * i))) % 256

def laneBytesLE (lane : Nat) : List Byte :=
  (List.range 8).map fun i => laneByte lane i

def squeezeBytes (st : List Nat) : List Byte :=
  ((List.range 25).flatMap fun i => laneBytesLE (getD st i)).take 32

def bytesOfString (s : String) : List Byte :=
  s.toUTF8.toList.map UInt8.toNat

def keccak256Bytes (bytes : List Byte) : List Byte :=
  squeezeBytes
    (absorbBlocks (List.replicate 25 0)
      (chunksOf rateBytes (padKeccak bytes)))

def keccak256String (s : String) : List Byte :=
  keccak256Bytes (bytesOfString s)

def wordFromBytesBE : List Byte -> Nat
  | [] => 0
  | byte :: bytes =>
      (byte % 256) * (2 ^ (8 * bytes.length)) + wordFromBytesBE bytes

def selector4 (signature : String) : Nat :=
  wordFromBytesBE ((keccak256String signature).take 4)

def digestWord (signature : String) : Nat :=
  wordFromBytesBE (keccak256String signature)

def transferSelectorExample : Bool :=
  selector4 "transfer(address,uint256)" == 0xa9059cbb

def balanceOfSelectorExample : Bool :=
  selector4 "balanceOf(address)" == 0x70a08231

def setSelectorExample : Bool :=
  selector4 "set(uint256)" == 0x60fe47b1

end Keccak256
end SpongeHash
end EvmYul
