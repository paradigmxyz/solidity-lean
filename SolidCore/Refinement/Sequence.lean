import SolidCore.Refinement.Statement

/-!
# Refinement of sequences of calls

`Refines` is about one call from a given initial storage. A deployed contract
sees a sequence of calls, each starting from the storage the previous one left.
This module states that once and lifts single-call refinements to it.

`Observable.storage` is a function from every slot to a word, while the next
`Call` takes its storage as a finite list of (slot, value) pairs. A sequence is
therefore run with a function `next` that turns an observable into that list,
the same on both sides. `runSeq` runs a list of messages (call data and value)
from an initial storage list, feeding `next obs` to each following call.

`Exact next obs` says the list `next obs` reads back, slot by slot through
`slotValue`, as exactly the final storage of `obs`: under it, the next call
starts from the previous call's final storage, not an approximation of it.
`RefinesSeqUpTo` asks that every sequence of at most `n` messages of a scope
finishes on both sides with the same list of observables, each of them but the
last exact (no call reads the last one's storage list); `RefinesSeq` asks it
for every length.

`refinesSeqUpTo_of_levels` is the lifting theorem: storages graded by depth,
the initial one at depth 0, and every step from depth `d < n` refining, landing at
depth `d + 1` and exact unless it is the `n`-th, give `RefinesSeqUpTo n`. `refinesSeq_of_closed` is the
unbounded case in terms of `Refines`: if every single call of the scope refines
from every storage of a set that contains the initial storage and is closed under
the steps, every sequence refines.

The source side starts each call from the deployed storage overwritten by the
call's list (see `Source.result?`). A `next` that lists every slot the
constructor writes, with its current value even when that is zero, makes that
the previous final storage; the corpus's `Seq.canon` does.
-/

namespace SolidCore.Refinement

/-- One call of a sequence without its initial storage, which the sequence supplies. -/
structure Msg where
  /-- The call data. -/
  calldata : ByteArray
  /-- The wei sent with the call. -/
  callvalue : Nat

/-- The call of `m` from the storage `storage`. -/
def Msg.call (m : Msg) (storage : List (Nat × Nat)) : Call :=
  { calldata := m.calldata, callvalue := m.callvalue, storage }

/-- Run the messages `ms` one after the other with `run`, the first from `σ` and each
later one from `next` of the previous observable. `none` when any run is `none`. -/
def runSeq (run : Call → Option Observable) (next : Observable → List (Nat × Nat)) :
    List (Nat × Nat) → List Msg → Option (List Observable)
  | _, [] => some []
  | σ, m :: ms =>
    match run (m.call σ) with
    | some obs => (runSeq run next (next obs) ms).map (obs :: ·)
    | none => none

/-- The storage list `next` gives for `obs` reads as exactly the final storage of `obs`. -/
def Exact (next : Observable → List (Nat × Nat)) (obs : Observable) : Prop :=
  slotValue (next obs) = obs.storage

/-- `code` implements `contract` on every sequence of at most `n` messages of `scope`
from the storage `σ0`: SolidCore with `fuel` and EthLib both finish every call and
show the same observables, and `next` carries each final storage a later call reads
exactly. -/
def RefinesSeqUpTo (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (next : Observable → List (Nat × Nat)) (σ0 : List (Nat × Nat))
    (scope : Msg → Prop) (n : Nat) : Prop :=
  ∀ ms : List Msg, ms.length ≤ n → (∀ m ∈ ms, scope m) →
    ∃ obss, runSeq (Source.run fuel contract) next σ0 ms = some obss ∧
      runSeq (Target.run code) next σ0 ms = some obss ∧ ∀ obs ∈ obss.dropLast, Exact next obs

/-- `code` implements `contract` on every finite sequence of messages of `scope` from
the storage `σ0`. -/
def RefinesSeq (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (next : Observable → List (Nat × Nat)) (σ0 : List (Nat × Nat))
    (scope : Msg → Prop) : Prop :=
  ∀ n, RefinesSeqUpTo fuel contract code next σ0 scope n

/-- Storages graded by depth, with `σ0` at depth 0, on which every message of `scope`
from depth `d < n` refines, lands at depth `d + 1` and is exact unless `d + 1 = n`,
give every sequence of at most `n` messages. -/
theorem refinesSeqUpTo_of_levels {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {next : Observable → List (Nat × Nat)} {σ0 : List (Nat × Nat)} {scope : Msg → Prop}
    {n : Nat} (S : Nat → List (Nat × Nat) → Prop) (h0 : S 0 σ0)
    (hstep : ∀ d < n, ∀ σ, S d σ → ∀ m, scope m →
      ∃ obs, Source.run fuel contract (m.call σ) = some obs ∧
        Target.run code (m.call σ) = some obs ∧ (d + 1 < n → Exact next obs) ∧
          S (d + 1) (next obs)) :
    RefinesSeqUpTo fuel contract code next σ0 scope n := by
  intro ms hlen hms
  suffices h : ∀ (ms : List Msg) (d : Nat) (σ : List (Nat × Nat)), d + ms.length ≤ n →
      S d σ → (∀ m ∈ ms, scope m) →
      ∃ obss, runSeq (Source.run fuel contract) next σ ms = some obss ∧
        runSeq (Target.run code) next σ ms = some obss ∧ obss.length = ms.length ∧
          ∀ obs ∈ obss.dropLast, Exact next obs by
    obtain ⟨obss, hs, ht, -, hex⟩ := h ms 0 σ0 (by omega) h0 hms
    exact ⟨obss, hs, ht, hex⟩
  intro ms
  induction ms with
  | nil => exact fun _ _ _ _ _ => ⟨[], rfl, rfl, rfl, by simp⟩
  | cons m ms ih =>
    intro d σ hlen hS hms
    simp only [List.length_cons] at hlen
    obtain ⟨obs, hs, ht, hex, hS'⟩ :=
      hstep d (by omega) σ hS m (hms m List.mem_cons_self)
    obtain ⟨obss, hs', ht', hl', hex'⟩ :=
      ih (d + 1) (next obs) (by omega) hS' fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    refine ⟨obs :: obss, ?_, ?_, by simp [hl'], ?_⟩
    · simp only [runSeq, hs, hs', Option.map_some]
    · simp only [runSeq, ht, ht', Option.map_some]
    · cases obss with
      | nil => simp
      | cons o os =>
        simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil o os), List.mem_cons,
          forall_eq_or_imp]
        simp only [List.length_cons] at hl'
        exact ⟨hex (by omega), hex'⟩

/-- A set of storages that holds `σ0`, on each of which every single call of `scope`
refines, and that every such call keeps exact and inside, gives every sequence. -/
theorem refinesSeq_of_closed {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {next : Observable → List (Nat × Nat)} {σ0 : List (Nat × Nat)} {scope : Msg → Prop}
    (S : List (Nat × Nat) → Prop) (h0 : S σ0)
    (href : ∀ σ, S σ → Refines fuel contract code fun call => ∃ m, scope m ∧ call = m.call σ)
    (hnext : ∀ σ, S σ → ∀ m, scope m → ∀ obs, Target.run code (m.call σ) = some obs →
      Exact next obs ∧ S (next obs)) :
    RefinesSeq fuel contract code next σ0 scope := fun _ =>
  refinesSeqUpTo_of_levels (fun _ σ => S σ) h0 fun _ _ σ hS m hm => by
    obtain ⟨obs, hs, ht⟩ := href σ hS _ ⟨m, hm, rfl⟩
    obtain ⟨hex, hS'⟩ := hnext σ hS m hm obs ht
    exact ⟨obs, hs, ht, fun _ => hex, hS'⟩

end SolidCore.Refinement
