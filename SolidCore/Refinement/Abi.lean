import SolidCore.Refinement.Check
import EthLib.Execution.Proofs.Evm.Logic.NatCode

/-!
# ABI calls of a contract's functions

A function of the corpus takes parameters of small ABI types. `Param.values` lists
every word a well-formed ABI encoding can give a parameter: the clean words.
`calls` lists every call of a function with clean argument words, from each of a list
of initial storages, with no value. A proof about a contract checks `agree` on all of
them and gets `Refines` for that scope from `refines_of_all`.
-/

namespace SolidCore.Refinement.Abi

open EthLib.Base

/-- The ABI type of a parameter, as far as cleaning its word goes. -/
inductive Param where
  /-- `uintN`, with `N` bits. -/
  | uint (bits : Nat)
  /-- `intN`, with `N` bits. -/
  | int (bits : Nat)
  /-- `bool`. -/
  | bool
  /-- An enum with `n` members. -/
  | enum (n : Nat)
  deriving Repr, DecidableEq

/-- Whether `v` is a word the ABI encoding of the parameter can give. -/
def Param.clean : Param → Nat → Bool
  | .uint b, v => v < 2 ^ b
  | .int b, v => v < 2 ^ (b - 1) || (2 ^ 256 - 2 ^ (b - 1) ≤ v && v < 2 ^ 256)
  | .bool, v => v < 2
  | .enum n, v => v < n

/-- Every clean word of the parameter, in increasing order of the value it encodes. -/
def Param.values : Param → List Nat
  | .uint b => List.range (2 ^ b)
  | .int b => ((List.range (2 ^ (b - 1))).map fun i => 2 ^ 256 - 2 ^ (b - 1) + i) ++
      List.range (2 ^ (b - 1))
  | .bool => [0, 1]
  | .enum n => List.range n

/-- The call data of a call of the function with selector `sel` on the argument words
`args`: the selector, then each word big-endian. -/
def calldata (sel : Nat) (args : List Nat) : ByteArray :=
  ⟨(natToBytes 4 sel ++ args.flatMap (natToBytes 32)).toArray⟩

/-- Every list of clean argument words for the parameters. -/
def tuples : List Param → List (List Nat)
  | [] => [[]]
  | p :: ps => p.values.flatMap fun v => (tuples ps).map (v :: ·)

instance : Inhabited Call := ⟨{ calldata := .empty, callvalue := 0, storage := [] }⟩

/-- A function of a contract: its selector and its parameters. -/
structure Fn where
  /-- The function's selector. -/
  sel : Nat
  /-- Its parameters, in order. -/
  params : List Param

/-- Every call of a function in `fns` with clean argument words, from each initial
storage in `storages`, with no value. -/
def calls (fns : List Fn) (storages : List (List (Nat × Nat))) : List Call :=
  storages.flatMap fun storage => fns.flatMap fun fn => (tuples fn.params).map fun args =>
    { calldata := calldata fn.sel args, callvalue := 0, storage }

end SolidCore.Refinement.Abi

namespace SolidCore.Refinement.Abi

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The storage SolidCore's constructor of `contract` leaves, as (slot, value) pairs
sorted by slot, or none when it does not return. A call from it is a call to the
freshly deployed contract. -/
def deployedStorage (fuel : Nat) (contract : TypeCheck.CheckedContract) :
    Option (List (Nat × Nat)) :=
  let base := contract.core.context
  let context := { base with sender := callerAddress, self := selfAddress, value := 0 }
  match TypeCheck.CheckedContract.constructWithContext? fuel contract context
      State.empty selfAddress 0 [] with
  | some (CallResult.returned deployed _) =>
    some ((deployed.storage.toList.filter (·.2 != 0)).mergeSort (fun a b => a.1 ≤ b.1))
  | _ => none

end SolidCore.Refinement.Abi

namespace SolidCore.Refinement.Abi

/-- Whether `p` holds of every element of `arr` whose index is `i` modulo `parts`.
A long check splits into `parts` of these, which separate modules can run at once. -/
def checkPart {α : Type} [Inhabited α] (p : α → Bool) (arr : Array α) (parts i : Nat) : Bool :=
  (List.range arr.size).all fun j => j % parts != i || p arr[j]!

theorem all_of_parts {α : Type} [Inhabited α] {p : α → Bool} {l : List α} {parts : Nat}
    (hp : 0 < parts) (h : ∀ i < parts, checkPart p l.toArray parts i = true) :
    l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h (j % parts) (Nat.mod_lt _ hp)
  simp only [checkPart, List.all_eq_true, List.mem_range, List.size_toArray, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at this
  rcases this j hj with h' | h'
  · exact absurd rfl h'
  · simpa [List.getElem!_toArray, hj] using h'

end SolidCore.Refinement.Abi
