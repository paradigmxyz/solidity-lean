import Init.Data.Array.Lemmas
import EvmYul.SpongeHash.Keccak256

namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
def ByteArray.zeroes (n : USize) : ByteArray :=
  ⟨Array.replicate n.toNat 0⟩

@[simp] theorem ByteArray.size_zeroes (n : USize) :
    (ByteArray.zeroes n).size = n.toNat := by
  change (Array.replicate n.toNat 0).size = n.toNat
  simp

@[simp] theorem ByteArray.getElem_zeroes
    (n : USize) (index : Nat)
    (hIndex : index < (ByteArray.zeroes n).size) :
    (ByteArray.zeroes n)[index] = 0 := by
  rw [ByteArray.size_zeroes] at hIndex
  change
    (Array.replicate n.toNat 0)[index]'(by simpa using hIndex) = 0
  simp

@[simp] theorem ByteArray.data_getD_zeroes
    (n : USize) (index : Nat) :
    (ByteArray.zeroes n).data.getD index 0 = 0 := by
  simp [ByteArray.zeroes, Array.getD]

@[simp] theorem ByteArray.data_getElem?_zeroes
    (n : USize) (index : Nat) :
    (ByteArray.zeroes n).data[index]? =
      if index < n.toNat then some 0 else none := by
  simp [ByteArray.zeroes, Array.getElem?_replicate]

private theorem ByteArray.toList_loop
    (bytes : ByteArray) (index : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes index acc =
      acc.reverse ++ bytes.data.toList.drop index := by
  fun_induction ByteArray.toList.loop bytes index acc with
  | case1 index acc hIndex ih =>
      rw [ih]
      simp only [List.reverse_cons, List.singleton_append,
        List.append_assoc]
      have hDataIndex : index < bytes.data.toList.length := by
        simpa [ByteArray.size_data] using hIndex
      rw [List.drop_eq_getElem_cons hDataIndex]
      congr 2
      unfold ByteArray.get!
      cases bytes with
      | mk data =>
          exact getElem!_pos data index (by simpa using hDataIndex)
  | case2 index acc hIndex =>
      have hData : bytes.data.toList.length ≤ index := by
        simpa [ByteArray.size_data, Nat.not_lt] using hIndex
      simp [List.drop_eq_nil_iff.mpr hData]

@[simp] theorem ByteArray.toList_eq_data_toList
    (bytes : ByteArray) :
    bytes.toList = bytes.data.toList := by
  unfold ByteArray.toList
  simpa using ByteArray.toList_loop bytes 0 []

/-- Keccak-256 of the first `len` bytes of `input`.

No longer `opaque`: the logical meaning is the pure sponge implementation in
`EvmYul.SpongeHash.Keccak256`, so `KEC` is provable-about; the `@[extern]`
attribute keeps compiled execution on the native `keccak256` symbol
(byte-parity with the pure body is asserted by downstream witnesses). -/
@[extern "keccak256"]
def keccak256 (input : @& ByteArray) (len : USize) : ByteArray :=
  EvmYul.SpongeHash.Keccak256.keccak256
    (ByteArray.mk (input.data.extract 0 len.toNat))

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
