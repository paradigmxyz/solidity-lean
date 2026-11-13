import Verify.Abi

/-!
# Models of functions that touch neither storage nor logs, on finite scopes

A function with only small parameters has finitely many clean calls, so the
model's agreement with SolidCore (`Implements`) can be checked call by call, as the
refinement corpus checks its finite scopes. `ofPure f` is the model of a function
that returns `f` of its argument words or reverts, leaving storage alone and
emitting no logs; `checkPure` evaluates SolidCore on every call of a list and
compares its result with `f`, and `implements_of_checkPure` turns a successful check
into `Implements` on the list. The check runs by `native_decide`.
-/

namespace SolidCore.Verify

open SolidCore.Refinement SolidCore.Solidity SolidCore.Solidity.Source

/-- The model of a function that touches neither storage nor logs. -/
def ofPure (f : List Nat → Except Revert (List Nat)) (ws : List Nat) : SolM (List Nat) :=
  fun s => (f ws).map (·, s)

@[simp] theorem wp_ofPure (f : List Nat → Except Revert (List Nat)) (ws : List Nat)
    (post : List Nat → Assn) :
    wp (ofPure f ws) post = fun herr s => match f ws with
      | .ok out => post out herr s
      | .error e => herr e := by
  rw [wp_eq]; funext herr s
  simp only [ofPure]
  rcases f ws with e | out <;> rfl

/-- Whether SolidCore's result `r` is `o`: the same success and output, and on success
empty storage and no logs. -/
def resultMatches (r : TypeCheck.CoreAbiCallResult) : Except Revert (List Nat) → Bool
  | .ok out => r.success && r.output == out && r.state.storage.isEmpty &&
      (r.state.logEntries selfAddress).isEmpty
  | .error e => !r.success && r.output == e

/-- Whether SolidCore with `fuel` runs every call of `calls`, from empty storage, as `f`
of its first `n` argument words says. -/
def checkPure (fuel : Nat) (contract : TypeCheck.CheckedContract) (n : Nat)
    (f : List Nat → Except Revert (List Nat)) (calls : List Call) : Bool :=
  calls.all fun call => call.storage.isEmpty &&
    match Source.result? fuel contract call with
    | some r => resultMatches r (f (argWords n call))
    | none => false

theorem implements_of_checkPure {fuel : Nat} {contract : TypeCheck.CheckedContract} {n : Nat}
    {f : List Nat → Except Revert (List Nat)} {calls : List Call}
    (h : checkPure fuel contract n f calls = true) :
    Implements fuel contract (· ∈ calls) (argWords n) (ofPure f) := by
  intro call hcall
  have h1 := List.all_eq_true.mp h call hcall
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h1
  obtain ⟨hst, h2⟩ := h1
  have hinit : initStorage call = fun _ => 0 := by
    funext k; simp [initStorage, hst, slotValue]
  split at h2
  next r hr =>
    simp only [Source.run, hr, Option.map_some, hinit, ofPure]
    unfold resultMatches at h2
    rcases hf : f (argWords n call) with e | out <;> rw [hf] at h2
    · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h2
      obtain ⟨hs, ho⟩ := h2
      simp [Source.observe, observe, hs, ho, Except.map, hst, slotValue]
    · simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h2
      obtain ⟨⟨⟨hs, ho⟩, hstore⟩, hlogs⟩ := h2
      simp only [Source.observe, observe, hs, ho, hlogs, Except.map, if_true, List.map_nil,
        Option.some.injEq]
      congr
      funext slot
      simp [State.loadSlot, StorageMap.lookup?, Wide.getElem?_of_isEmpty hstore]
  next => simp at h2

end SolidCore.Verify
