/-!
# Hex: the bytes a manifest's hex spells

The decoder the certified theorems use to tie the bytes their stages run to the hex an export's
manifest records (the hex `--emit=bin-runtime` printed): `hexBytes (codes s)` is the list of
bytes the lowercase hex string `s` spells, or `none` when `s` is not one, and `hexChars bs` is
the lowercase hex of the bytes `bs`.

The kernel unfolds a string literal to `String.ofList` of its characters cheaply, but evaluating
`String.toUTF8` or `String.toList` of a literal of a few hundred characters exhausts 3 GB. So a
manifest's hex is tied to the bytes in two steps: the literal is `String.ofList (hexChars bytes)`
by the kernel's definitional unfolding (`rfl`), and `String.toList_ofList` turns its codes into
`(hexChars bytes).map Char.toNat`, which the kernel decodes. For codes read through
`String.toUTF8`, `toUTF8_toList_ofList` does the same: the UTF-8 bytes of `String.ofList l` are
`l.flatMap String.utf8EncodeChar`, which the kernel evaluates char by char, where
`ByteArray.toList`'s well-founded loop would cost it gigabytes.
-/

namespace SolidCore.Refinement.Solar.Hex

/-- The value of a lowercase hex digit's ASCII code. -/
def hexDigit (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- The bytes a string of lowercase hex digits spells, from its ASCII codes. -/
def hexBytes : List Nat → Option (List Nat)
  | [] => some []
  | a :: b :: rest =>
    match hexDigit a, hexDigit b, hexBytes rest with
    | some x, some y, some r => some ((16 * x + y) :: r)
    | _, _, _ => none
  | [_] => none

/-- The ASCII codes of a string. -/
def codes (s : String) : List Nat := s.toList.map (·.toNat)

/-- `ByteArray.toList`'s loop from index `i` with the reversed prefix `r`. -/
theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    have hg : bs.get! i = bs.data.toList[i] :=
      getElem!_pos bs.data i (by rw [← Array.length_toList]; exact hi)
    rw [List.drop_eq_getElem_cons hi, hg, List.reverse_cons, List.append_assoc]
    rfl
  | case2 i r h =>
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le this, List.append_nil]

/-- `ByteArray.toList` is the list of the bytes. -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]; rfl

/-- The UTF-8 bytes of `String.ofList l`, char by char. -/
theorem toUTF8_toList_ofList (l : List Char) :
    (String.ofList l).toUTF8.toList = l.flatMap String.utf8EncodeChar := by
  rw [toList_eq_data_toList]
  exact List.toList_data_toByteArray

/-- The lowercase hex digit of a number below 16. -/
def hexChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The lowercase hex of a list of bytes, two digits a byte. -/
def hexChars : List Nat → List Char
  | [] => []
  | b :: rest => hexChar (b / 16) :: hexChar (b % 16) :: hexChars rest

/-- A string that is not hex spells nothing: the decoder fails closed. -/
theorem hexBytes_odd : hexBytes (codes "abc") = none := by decide +kernel

/-- An uppercase digit is not lowercase hex. -/
theorem hexBytes_upper : hexBytes (codes "0A") = none := by decide +kernel

end SolidCore.Refinement.Solar.Hex
