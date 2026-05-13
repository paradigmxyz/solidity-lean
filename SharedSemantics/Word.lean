import Std
import EvmYul.UInt256

namespace SharedSemantics

def wordModulus : Nat := EvmYul.UInt256.size

def halfWordModulus : Nat := 2 ^ 255

abbrev Word := Nat

abbrev EvmWord := EvmYul.UInt256

def norm (n : Nat) : Word :=
  n % wordModulus

def toEvmWord (value : Word) : EvmWord :=
  EvmYul.UInt256.ofNat (norm value)

def ofEvmWord (value : EvmWord) : Word :=
  norm value.toNat

def liftEvmUnary (f : EvmWord -> EvmWord) (value : Word) : Word :=
  ofEvmWord (f (toEvmWord value))

def liftEvmBinary (f : EvmWord -> EvmWord -> EvmWord)
    (lhs rhs : Word) : Word :=
  ofEvmWord (f (toEvmWord lhs) (toEvmWord rhs))

def liftEvmTernary (f : EvmWord -> EvmWord -> EvmWord -> EvmWord)
    (a b c : Word) : Word :=
  ofEvmWord (f (toEvmWord a) (toEvmWord b) (toEvmWord c))

theorem norm_norm (value : Word) :
    norm (norm value) = norm value := by
  simp [norm, wordModulus]

def addWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.add a b

def mulWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.mul a b

def divWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.div a b

def modWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.mod a b

def addmodWord (a b n : Word) : Word :=
  liftEvmTernary EvmYul.UInt256.addMod a b n

def mulmodWord (a b n : Word) : Word :=
  liftEvmTernary EvmYul.UInt256.mulMod a b n

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
  liftEvmBinary EvmYul.UInt256.exp base exponent

def subWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.sub a b

def iszeroWord (a : Word) : Word :=
  liftEvmUnary EvmYul.UInt256.isZero a

def eqWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.eq a b

def ltWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.lt a b

def gtWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.gt a b

def signedValue (a : Word) : Int :=
  EvmYul.UInt256.fromSigned (toEvmWord a)

def sltWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.slt a b

def sgtWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.sgt a b

def signedToWord (value : Int) : Word :=
  ofEvmWord (EvmYul.UInt256.toSigned value)

def sdivWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.sdiv a b

def smodWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.smod a b

def andWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.land a b

def orWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.lor a b

def xorWord (a b : Word) : Word :=
  liftEvmBinary EvmYul.UInt256.xor a b

def notWord (a : Word) : Word :=
  liftEvmUnary EvmYul.UInt256.lnot a

def shlWord (shift value : Word) : Word :=
  ofEvmWord
    (EvmYul.UInt256.shiftLeft (toEvmWord value) (toEvmWord shift))

def shrWord (shift value : Word) : Word :=
  ofEvmWord
    (EvmYul.UInt256.shiftRight (toEvmWord value) (toEvmWord shift))

def sarWord (shift value : Word) : Word :=
  ofEvmWord (EvmYul.UInt256.sar (toEvmWord shift) (toEvmWord value))

def byteWord (ix value : Word) : Word :=
  ofEvmWord (EvmYul.UInt256.byteAt (toEvmWord ix) (toEvmWord value))

def signextendWord (ix value : Word) : Word :=
  ofEvmWord (EvmYul.UInt256.signextend (toEvmWord ix) (toEvmWord value))

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
