import Std

/-!
Compatibility surface for Nethermind's `EvmYul.UInt256` primitive.

The upstream EVMYulLean repository is currently pinned to an older Lean toolchain
than this project.  This file keeps the source layer importing an `EvmYul`
primitive module while preserving the repo's working Lean version.  The API is
the small UInt256 slice used by `SharedSemantics.Word`; it follows EVM 256-bit
word behavior and is intended to be replaced by the upstream module once the
toolchains converge.
-/

namespace EvmYul

structure UInt256 where
  value : Nat
  deriving DecidableEq, Repr

namespace UInt256

def size : Nat := 2 ^ 256

def halfSize : Nat := 2 ^ 255

def maxValue : Nat := size - 1

def norm (value : Nat) : Nat :=
  value % size

def ofNat (value : Nat) : UInt256 :=
  ⟨norm value⟩

def toNat (value : UInt256) : Nat :=
  norm value.value

def ofBool (value : Bool) : UInt256 :=
  if value then ofNat 1 else ofNat 0

def add (lhs rhs : UInt256) : UInt256 :=
  ofNat (lhs.toNat + rhs.toNat)

def sub (lhs rhs : UInt256) : UInt256 :=
  ofNat (lhs.toNat + size - rhs.toNat)

def mul (lhs rhs : UInt256) : UInt256 :=
  ofNat (lhs.toNat * rhs.toNat)

def div (lhs rhs : UInt256) : UInt256 :=
  if rhs.toNat = 0 then ofNat 0 else ofNat (lhs.toNat / rhs.toNat)

def mod (lhs rhs : UInt256) : UInt256 :=
  if rhs.toNat = 0 then ofNat 0 else ofNat (lhs.toNat % rhs.toNat)

def addMod (lhs rhs modulus : UInt256) : UInt256 :=
  if modulus.toNat = 0 then
    ofNat 0
  else
    ofNat ((lhs.toNat + rhs.toNat) % modulus.toNat)

def mulMod (lhs rhs modulus : UInt256) : UInt256 :=
  if modulus.toNat = 0 then
    ofNat 0
  else
    ofNat ((lhs.toNat * rhs.toNat) % modulus.toNat)

def powModAux (base exponent acc : Nat) : Nat :=
  if h : exponent = 0 then
    acc % size
  else
    let acc' :=
      if exponent % 2 = 1 then
        (acc * base) % size
      else
        acc % size
    let base' := (base * base) % size
    powModAux base' (exponent / 2) acc'
termination_by exponent
decreasing_by
  have hpos : 0 < exponent := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by decide : 1 < 2)

def exp (base exponent : UInt256) : UInt256 :=
  ofNat (powModAux base.toNat exponent.toNat 1)

def isZero (value : UInt256) : UInt256 :=
  ofBool (value.toNat = 0)

def eq (lhs rhs : UInt256) : UInt256 :=
  ofBool (lhs.toNat = rhs.toNat)

def lt (lhs rhs : UInt256) : UInt256 :=
  ofBool (lhs.toNat < rhs.toNat)

def gt (lhs rhs : UInt256) : UInt256 :=
  ofBool (rhs.toNat < lhs.toNat)

def fromSigned (value : UInt256) : Int :=
  let raw := value.toNat
  if raw < halfSize then
    (raw : Int)
  else
    (raw : Int) - (size : Int)

def intNorm : Int -> Nat
  | Int.ofNat value => norm value
  | Int.negSucc value =>
      let magnitude := value + 1
      let remainder := magnitude % size
      if remainder = 0 then 0 else size - remainder

def toSigned (value : Int) : UInt256 :=
  ofNat (intNorm value)

def slt (lhs rhs : UInt256) : UInt256 :=
  ofBool (fromSigned lhs < fromSigned rhs)

def sgt (lhs rhs : UInt256) : UInt256 :=
  ofBool (fromSigned rhs < fromSigned lhs)

def truncDiv (lhs rhs : Int) : Int :=
  if rhs = 0 then
    0
  else
    let quotient := lhs.natAbs / rhs.natAbs
    if (decide (lhs < 0)) != (decide (rhs < 0)) then
      - (quotient : Int)
    else
      (quotient : Int)

def signedMod (lhs rhs : Int) : Int :=
  if rhs = 0 then
    0
  else
    let remainder := lhs.natAbs % rhs.natAbs
    if lhs < 0 then
      - (remainder : Int)
    else
      (remainder : Int)

def sdiv (lhs rhs : UInt256) : UInt256 :=
  toSigned (truncDiv (fromSigned lhs) (fromSigned rhs))

def smod (lhs rhs : UInt256) : UInt256 :=
  toSigned (signedMod (fromSigned lhs) (fromSigned rhs))

def land (lhs rhs : UInt256) : UInt256 :=
  ofNat (Nat.land lhs.toNat rhs.toNat)

def lor (lhs rhs : UInt256) : UInt256 :=
  ofNat (Nat.lor lhs.toNat rhs.toNat)

def xor (lhs rhs : UInt256) : UInt256 :=
  ofNat (Nat.xor lhs.toNat rhs.toNat)

def lnot (value : UInt256) : UInt256 :=
  ofNat (maxValue - value.toNat)

def shiftLeft (value shift : UInt256) : UInt256 :=
  if 256 ≤ shift.toNat then
    ofNat 0
  else
    ofNat (value.toNat * 2 ^ shift.toNat)

def shiftRight (value shift : UInt256) : UInt256 :=
  if 256 ≤ shift.toNat then
    ofNat 0
  else
    ofNat (value.toNat / 2 ^ shift.toNat)

def sar (shift value : UInt256) : UInt256 :=
  if 256 ≤ shift.toNat then
    if fromSigned value < 0 then ofNat maxValue else ofNat 0
  else
    toSigned (fromSigned value / (2 ^ shift.toNat : Nat))

def byteAt (index value : UInt256) : UInt256 :=
  if 32 ≤ index.toNat then
    ofNat 0
  else
    let shift := 8 * (31 - index.toNat)
    ofNat ((value.toNat / 2 ^ shift) % 256)

def signextend (index value : UInt256) : UInt256 :=
  if 32 ≤ index.toNat then
    ofNat value.toNat
  else
    let bit := 8 * index.toNat + 7
    let signBit := 2 ^ bit
    let lowMask := 2 ^ (bit + 1) - 1
    if 0 < Nat.land value.toNat signBit then
      ofNat (Nat.lor value.toNat (maxValue - lowMask))
    else
      ofNat (Nat.land value.toNat lowMask)

instance : HAdd UInt256 UInt256 UInt256 where
  hAdd := add

instance : HSub UInt256 UInt256 UInt256 where
  hSub := sub

instance : HMul UInt256 UInt256 UInt256 where
  hMul := mul

instance : HDiv UInt256 UInt256 UInt256 where
  hDiv := div

instance : HMod UInt256 UInt256 UInt256 where
  hMod := mod

end UInt256
end EvmYul
