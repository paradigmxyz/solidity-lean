import SolidCore.Refinement.Dirty.Source

/-!
# The clean scope inside the full scope

A contract whose refinement is proved symbolically (`SolidCore.Refinement.Wide`) gets it on
`Abi.fullScope`, every call on any argument words below `2 ^ 256`. `refines_of_full` gives
from it the refinement on `Abi.calls`, the clean calls the enumeration route checks one by
one, when every parameter's clean words are words (`Param.fits`, which `decide` checks for
a contract's list of functions).
-/

namespace SolidCore.Refinement.Wide

open SolidCore.Refinement.Abi

/-- Whether every clean word of the parameter is below `2 ^ 256`. -/
def paramFits : Param → Bool
  | .uint b => decide (b ≤ 256)
  | .int b => decide (0 < b ∧ b ≤ 256)
  | .bool => true
  | .enum n => decide (n ≤ 2 ^ 256)

theorem lt_of_mem_values {p : Param} (hp : paramFits p = true) {v : Nat} (hv : v ∈ p.values) :
    v < 2 ^ 256 := by
  cases p with
  | uint b =>
    simp only [paramFits, decide_eq_true_eq] at hp
    simp only [Param.values, List.mem_range] at hv
    exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hp)
  | int b =>
    simp only [paramFits, decide_eq_true_eq] at hp
    have hle : 2 ^ (b - 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [Param.values, List.mem_append, List.mem_map, List.mem_range] at hv
    rcases hv with ⟨i, hi, rfl⟩ | hv
    · omega
    · omega
  | bool =>
    simp only [Param.values, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> decide
  | enum n =>
    simp only [paramFits, decide_eq_true_eq] at hp
    simp only [Param.values, List.mem_range] at hv
    omega

theorem of_mem_tuples : ∀ {ps : List Param}, ps.all paramFits = true → ∀ {args : List Nat},
    args ∈ tuples ps → args.length = ps.length ∧ ∀ a ∈ args, a < 2 ^ 256
  | [], _, args, h => by
    simp only [tuples, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp
  | p :: ps, hps, args, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨v, hv, rest, hrest, rfl⟩ := h
    obtain ⟨hl, hlt⟩ := of_mem_tuples hps.2 hrest
    refine ⟨by simp [hl], fun a ha => ?_⟩
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact lt_of_mem_values hps.1 hv
    · exact hlt a ha

/-- A clean call is in the full scope. -/
theorem fullScope_of_mem_calls {fns : List Fn} (hf : fns.all (·.params.all paramFits) = true)
    {s : List (Nat × Nat)} {call : Call} (h : call ∈ calls fns [s]) : fullScope fns s call := by
  simp only [calls, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap,
    List.mem_map] at h
  obtain ⟨fn, hfn, args, hargs, rfl⟩ := h
  obtain ⟨hl, hlt⟩ := of_mem_tuples (List.all_eq_true.mp hf fn hfn) hargs
  exact ⟨fn, hfn, args, hl, hlt, rfl⟩

/-- The refinement on the full scope gives it on the clean calls. -/
theorem refines_of_full {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {fns : List Fn} {s : List (Nat × Nat)}
    (hf : fns.all (·.params.all paramFits) = true) (h : Refines fuel c code (fullScope fns s)) :
    Refines fuel c code (· ∈ calls fns [s]) :=
  fun call hc => h call (fullScope_of_mem_calls hf hc)

end SolidCore.Refinement.Wide
