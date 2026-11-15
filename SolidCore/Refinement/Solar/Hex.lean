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
`(hexChars bytes).map Char.toNat`, which the kernel decodes.
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
