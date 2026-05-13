import Std

namespace SharedSemantics

def wordModulus : Nat := 2 ^ 256

def halfWordModulus : Nat := 2 ^ 255

abbrev Word := Nat

def norm (n : Nat) : Word :=
  n % wordModulus

theorem norm_norm (value : Word) :
    norm (norm value) = norm value := by
  simp [norm, wordModulus]

def addWord (a b : Word) : Word :=
  norm (a + b)

def mulWord (a b : Word) : Word :=
  norm (a * b)

def divWord (a b : Word) : Word :=
  if norm b = 0 then 0 else norm (norm a / norm b)

def modWord (a b : Word) : Word :=
  if norm b = 0 then 0 else norm (norm a % norm b)

def addmodWord (a b n : Word) : Word :=
  if norm n = 0 then 0 else norm ((norm a + norm b) % norm n)

def mulmodWord (a b n : Word) : Word :=
  if norm n = 0 then 0 else norm ((norm a * norm b) % norm n)

def powModWordAux (base exponent acc : Nat) : Nat :=
  if h : exponent = 0 then
    acc % wordModulus
  else
    let acc' :=
      if exponent % 2 = 1 then
        (acc * base) % wordModulus
      else
        acc % wordModulus
    let base' := (base * base) % wordModulus
    powModWordAux base' (exponent / 2) acc'
termination_by exponent
decreasing_by
  have hpos : 0 < exponent := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by decide : 1 < 2)

def expWord (base exponent : Word) : Word :=
  powModWordAux (norm base) (norm exponent) 1

def subWord (a b : Word) : Word :=
  norm (wordModulus + norm a - norm b)

def iszeroWord (a : Word) : Word :=
  if norm a = 0 then 1 else 0

def eqWord (a b : Word) : Word :=
  if norm a = norm b then 1 else 0

def ltWord (a b : Word) : Word :=
  if norm a < norm b then 1 else 0

def gtWord (a b : Word) : Word :=
  if norm b < norm a then 1 else 0

def signedValue (a : Word) : Int :=
  if norm a < halfWordModulus then
    Int.ofNat (norm a)
  else
    Int.ofNat (norm a) - Int.ofNat wordModulus

def sltWord (a b : Word) : Word :=
  if signedValue a < signedValue b then 1 else 0

def sgtWord (a b : Word) : Word :=
  if signedValue b < signedValue a then 1 else 0

def signedToWord (value : Int) : Word :=
  if value < 0 then norm (wordModulus - Int.natAbs value) else norm value.toNat

def sdivWord (a b : Word) : Word :=
  if norm b = 0 then
    0
  else
    let lhs := signedValue a
    let rhs := signedValue b
    let quotient := (Int.natAbs lhs) / (Int.natAbs rhs)
    if (lhs < 0) = (rhs < 0) then
      signedToWord (Int.ofNat quotient)
    else
      signedToWord (-(Int.ofNat quotient))

def smodWord (a b : Word) : Word :=
  if norm b = 0 then
    0
  else
    let lhs := signedValue a
    let rhs := signedValue b
    let unsignedMod := (Int.natAbs lhs) % (Int.natAbs rhs)
    if lhs < 0 then
      signedToWord (-(Int.ofNat unsignedMod))
    else
      signedToWord (Int.ofNat unsignedMod)

def andWord (a b : Word) : Word :=
  norm (Nat.land (norm a) (norm b))

def orWord (a b : Word) : Word :=
  norm (Nat.lor (norm a) (norm b))

def xorWord (a b : Word) : Word :=
  norm (Nat.xor (norm a) (norm b))

def notWord (a : Word) : Word :=
  norm (wordModulus - 1 - norm a)

def shlWord (shift value : Word) : Word :=
  if 256 <= norm shift then 0 else norm (Nat.shiftLeft (norm value) (norm shift))

def shrWord (shift value : Word) : Word :=
  if 256 <= norm shift then 0 else norm (Nat.shiftRight (norm value) (norm shift))

def sarWord (shift value : Word) : Word :=
  if 256 <= norm shift then
    if signedValue value < 0 then norm (wordModulus - 1) else 0
  else
    signedToWord (Int.shiftRight (signedValue value) (norm shift))

def byteWord (ix value : Word) : Word :=
  if norm ix < 32 then
    norm (Nat.land (Nat.shiftRight (norm value) (8 * (31 - norm ix))) 255)
  else
    0

def signextendWord (ix value : Word) : Word :=
  if norm ix < 32 then
    let bitPos := 8 * norm ix + 7
    let modulus := 2 ^ (bitPos + 1)
    let signBit := 2 ^ bitPos
    let low := norm value % modulus
    if signBit <= low then norm (wordModulus - modulus + low) else norm low
  else
    norm value

def clzWordAux : Nat -> Nat -> Word -> Word
  | 0, _, _ => 256
  | remaining + 1, bit, value =>
      if 0 < Nat.land (norm value) (2 ^ bit) then
        255 - bit
      else
        clzWordAux remaining (bit - 1) value

def clzWord (value : Word) : Word :=
  norm (clzWordAux 256 255 value)

def ceil32 (n : Nat) : Nat :=
  if n = 0 then 0 else ((n + 31) / 32) * 32

def memorySizeAfter (current offset size : Word) : Word :=
  if norm size = 0 then
    norm current
  else
    Nat.max (norm current) (ceil32 (norm offset + norm size))

theorem memorySizeAfter_zero_size (current offset : Word) :
    memorySizeAfter current offset 0 = norm current := by
  rfl

theorem memorySizeAfter_empty_word :
    memorySizeAfter 0 0 32 = 32 := by
  rfl

end SharedSemantics
