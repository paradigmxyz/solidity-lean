import Contracts.UniswapV2.ERC20.NoCallAt

/-!
# Control: the refusal comes from the refused instructions alone

`scrubWith qs c` is `c` with the byte at each counter of `qs` replaced by INVALID (0xfe), and
`scrubbed` scrubs exactly `refusedAt code` (`scrubbed_eq`, from `refusedAt_eq`). It has the runtime's size and its bytes off those counters
(`scrubWith_size`, `scrubWith_get`, by proof, not evaluation), and it **passes** `callFree`
(`scrubbed_callFree`): the decode stays aligned, and nothing but those instructions fails the check.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly

def scrubList (qs : List Nat) : Nat → List UInt8 → List UInt8
  | _, [] => []
  | i, b :: bs => (if qs.contains i then 0xfe else b) :: scrubList qs (i + 1) bs

def scrubWith (qs : List Nat) (c : ByteArray) : ByteArray := ⟨(scrubList qs 0 c.data.toList).toArray⟩

theorem scrubList_length (qs : List Nat) : ∀ i (l : List UInt8), (scrubList qs i l).length = l.length
  | _, [] => rfl
  | i, _ :: bs => by rw [scrubList, List.length_cons, List.length_cons, scrubList_length qs (i + 1) bs]

theorem scrubList_get (qs : List Nat) : ∀ i (l : List UInt8) k (hk : k < l.length),
    qs.contains (i + k) = false →
      (scrubList qs i l)[k]'(by rw [scrubList_length]; exact hk) = l[k]
  | _, [], _, hk, _ => absurd hk (by simp)
  | i, b :: bs, 0, _, hq => by
    simp only [scrubList, List.getElem_cons_zero]
    rw [Nat.add_zero] at hq
    rw [hq]; rfl
  | i, b :: bs, k + 1, hk, hq => by
    simp only [scrubList, List.getElem_cons_succ]
    exact scrubList_get qs (i + 1) bs k (Nat.lt_of_succ_lt_succ hk) (by rw [← hq]; congr 1; omega)

theorem scrubWith_size (qs : List Nat) (c : ByteArray) : (scrubWith qs c).size = c.size := by
  show (scrubList qs 0 c.data.toList).toArray.size = c.data.size
  rw [List.size_toArray, scrubList_length, Array.length_toList]

theorem scrubWith_get (qs : List Nat) (c : ByteArray) (i : Nat) (hi : i < c.size)
    (hq : qs.contains i = false) :
    (scrubWith qs c).data[i]'(by rw [← ByteArray.size, scrubWith_size]; exact hi) = c.data[i] := by
  have h := scrubList_get qs 0 c.data.toList i (by rw [Array.length_toList]; exact hi)
    (by rw [Nat.zero_add]; exact hq)
  exact h.trans (by simp)

def scrubbed : ByteArray := scrubWith [903, 1158, 1161, 1162] code

theorem scrubbed_eq : scrubbed = scrubWith (refusedAt code) code := by rw [refusedAt_eq]; rfl

theorem scrubbed_callFree : callFree scrubbed = true := by decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.scrubbed_callFree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms scrubbed_callFree

end SolidCore.Spec.UniswapV2.ERC20.NoCall
