import SolidCore.Refinement.Sequence
import SolidCore.Refinement.Dirty.Source

/-!
# Checking sequence refinement on a certificate of reachable storages

`Sequence.lean` lifts single calls to sequences over a set of storages closed
under the calls. This module makes that set a finite, checkable certificate for
the corpus's ABI scope.

* `canon keys base obs` is the `next` of the corpus: the slots of `keys`, in
  order, whose final value is nonzero or that the constructor wrote (`base`),
  with their values. With `keys` sorted it is a canonical list, so equal
  storages give equal lists and a set of storages is a list of lists.
* `exactOn zero f σ` checks `slotValue σ = f` on finitely many slots: those `σ`
  names and those `zero` names, off which `f` is zero (`slotValue_eq_of_exactOn`).
* `stepCheck` runs one call: both semantics agree (`agreeAt`, `agree` with
  SolidCore's result already computed, so each check runs SolidCore once), the
  next storage is exact on SolidCore's final storage when a later call reads it,
  and `target` accepts it.
* A certificate is a list of levels of storages. `items` lists every clean call
  from every storage of every level, `states` every storage with its level.
  `target` accepts what a step from level `d` must reach: for a closed
  certificate any storage of any level, otherwise one of the levels up to the
  next, and anything from the last level.
* `refinesSeq_of_cert` (closed) and `refinesSeqUpTo_of_cert` (as many messages as
  there are levels) turn a passing check into `RefinesSeq` and `RefinesSeqUpTo`
  on `fullMsg fns`: every message of a corpus function on any argument words
  below `2 ^ 256`, with no value. Dirty argument words reuse `Dirty.run_dirty`
  and `Dirty.TargetDirty`, which hold from every storage, so the check of a
  dirty message is one cheap `dirtyOk` per storage: it keeps the storage, which
  must be exact and reach the target.
-/

namespace SolidCore.Refinement.Seq

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State
open SolidCore.Solidity SolidCore.Refinement.Abi

/-! ## The next storage and its exactness -/

/-- The keys `keys` as words, sorted and without duplicates. -/
def normKeys (keys : List Nat) : List Nat :=
  ((keys.map (· % wordSize)).mergeSort (· ≤ ·)).eraseDups

/-- The slots of `keys` whose final value in `obs` is nonzero or that `base` names,
in the order of `keys`, with their final values. -/
def canon (keys base : List Nat) (obs : Observable) : List (Nat × Nat) :=
  keys.filterMap fun k =>
    let v := obs.storage k
    if v != 0 || base.contains k then some (k, v) else none

/-- Whether `slotValue σ` and `f` agree on every slot `σ` or `zero` names. -/
def exactOn (zero : List Nat) (f : Nat → Nat) (σ : List (Nat × Nat)) : Bool :=
  (σ.map (·.1 % wordSize) ++ zero).all fun k => slotValue σ k == f k

/-- A storage function read modulo `2 ^ 256` and zero off `zero` is the one `σ`
reads as, once `exactOn` accepts them. -/
theorem slotValue_eq_of_exactOn {zero : List Nat} {f : Nat → Nat} {σ : List (Nat × Nat)}
    (fp : ∀ s, f s = f (s % wordSize)) (fz : ∀ s, s % wordSize ∉ zero → f s = 0)
    (h : exactOn zero f σ = true) : slotValue σ = f :=
  storage_ext (σ.map (·.1 % wordSize) ++ zero) (slotValue_mod σ) fp
    (fun s hs => slotValue_of_not_mem { calldata := .empty, callvalue := 0, storage := σ } s
      fun m => hs (List.mem_append_left _ m))
    (fun s hs => fz s fun m => hs (List.mem_append_right _ m))
    (fun k hk => by simpa using List.all_eq_true.mp h k hk)

/-! ## One call -/

/-- `agree` on `call`, given SolidCore's result `r` of it. -/
def agreeAt (code : ByteArray) (call : Call) (r : TypeCheck.CoreAbiCallResult) : Bool :=
  match processMessage (Meter := Nat) .fusaka (Target.message code call)
      (Target.preState code call) Substate.empty, Target.run code call with
  | .ok ⟨evm, _⟩, some tgt =>
    let src := Source.observe call r
    src.success == tgt.success && src.output == tgt.output && src.logs == tgt.logs &&
      (sourceKeys r.state ++ targetKeys evm.state (Target.address selfAddress) ++
        callKeys call).all fun k => src.storage k == tgt.storage k
  | _, _ => false

theorem agree_of_agreeAt {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {call : Call} {r : TypeCheck.CoreAbiCallResult} (hr : Source.result? fuel c call = some r)
    (h : agreeAt code call r = true) : agree fuel c code call = true := by
  unfold agreeAt at h
  unfold agree
  rw [hr]
  split at h
  next evm sub tgt hpm htgt => simp only [hpm, htgt]; exact h
  next => exact absurd h (by simp)

/-- Whether `call` refines, its next storage under `next` is exact when `exact` asks
for it, and `target` accepts that storage. SolidCore runs once. -/
def stepCheck (fuel : Nat) (c : TypeCheck.CheckedContract) (code : ByteArray)
    (next : Observable → List (Nat × Nat)) (exact : Bool) (target : List (Nat × Nat) → Bool)
    (call : Call) : Bool :=
  match Source.result? fuel c call with
  | some r =>
    let obs := Source.observe call r
    agreeAt code call r &&
      (!exact || exactOn (sourceKeys r.state ++ callKeys call) obs.storage (next obs)) &&
      target (next obs)
  | none => false

theorem stepCheck_sound {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {next : Observable → List (Nat × Nat)} {exact : Bool} {target : List (Nat × Nat) → Bool}
    {call : Call} (h : stepCheck fuel c code next exact target call = true) :
    ∃ obs, Source.run fuel c call = some obs ∧ Target.run code call = some obs ∧
      (exact = true → Exact next obs) ∧ target (next obs) = true := by
  unfold stepCheck at h
  split at h
  next r hr =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hex⟩, ht⟩ := h
    obtain ⟨obs, hs, htg⟩ := agree_sound (agree_of_agreeAt hr ha)
    have hobs : obs = Source.observe call r := by
      simp only [Source.run, hr, Option.map_some, Option.some.injEq] at hs
      exact hs.symm
    subst hobs
    refine ⟨_, hs, htg, fun he => ?_, ht⟩
    simp only [he, Bool.not_true, Bool.false_or] at hex
    apply slotValue_eq_of_exactOn _ _ hex
    · intro s
      simp only [Source.observe]
      split
      · exact loadSlot_mod _ s
      · exact slotValue_mod _ s
    · intro s hs'
      simp only [Source.observe]
      split
      · exact loadSlot_of_not_mem _ _ fun m => hs' (List.mem_append_left _ m)
      · exact slotValue_of_not_mem _ _ fun m => hs' (List.mem_append_right _ m)
  next => exact absurd h (by simp)

/-! ## Certificates -/

/-- What a step from level `d` of `levels` must reach: any storage of any level when
the certificate is closed; otherwise one of a level up to `d + 1`, or anything from the
last level. -/
def target (levels : List (List (List (Nat × Nat)))) (closed : Bool) (d : Nat)
    (σ : List (Nat × Nat)) : Bool :=
  if closed then levels.any (·.contains σ)
  else levels.length ≤ d + 1 || (levels.take (d + 2)).any (·.contains σ)

/-- Every storage of `levels` with its level. -/
def states (levels : List (List (List (Nat × Nat)))) : List (Nat × List (Nat × Nat)) :=
  (List.range levels.length).flatMap fun d => (levels.getD d []).map (d, ·)

/-- Every clean call of a function of `fns` from every storage of `levels`, with the
storage's level. -/
def items (fns : List Fn) (levels : List (List (List (Nat × Nat)))) : List (Nat × Call) :=
  (states levels).flatMap fun ds => (calls fns [ds.2]).map (ds.1, ·)

/-- Whether a step from level `d` must carry its storage exactly: always in a closed
certificate, otherwise unless it is from the last level, whose next storage no call
of the sequences it covers reads. -/
def needExact (levels : List (List (List (Nat × Nat)))) (closed : Bool) (d : Nat) : Bool :=
  closed || d + 1 < levels.length

/-- The check of one clean call of the certificate. -/
def itemOk (fuel : Nat) (c : TypeCheck.CheckedContract) (code : ByteArray)
    (next : Observable → List (Nat × Nat)) (levels : List (List (List (Nat × Nat))))
    (closed : Bool) (item : Nat × Call) : Bool :=
  stepCheck fuel c code next (needExact levels closed item.1) (target levels closed item.1)
    item.2

/-- The check of every dirty call from one storage of the certificate: such a call
keeps the storage, which must be exact when `needExact` asks and reach the target. -/
def dirtyOk (next : Observable → List (Nat × Nat)) (levels : List (List (List (Nat × Nat))))
    (closed : Bool) (ds : Nat × List (Nat × Nat)) : Bool :=
  (!needExact levels closed ds.1 ||
      exactOn (ds.2.map (·.1 % wordSize)) (rejected ds.2).storage (next (rejected ds.2))) &&
    target levels closed ds.1 (next (rejected ds.2))

/-- Every message of a function of `fns` on any argument words below `2 ^ 256`, with
no value. -/
def fullMsg (fns : List Fn) (m : Msg) : Prop :=
  ∃ fn ∈ fns, ∃ args : List Nat, args.length = fn.params.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
    m = { calldata := calldata fn.sel args, callvalue := 0 }

theorem mem_states {levels : List (List (List (Nat × Nat)))} {d : Nat}
    {σ : List (Nat × Nat)} (hd : d < levels.length) (hσ : σ ∈ levels.getD d []) :
    (d, σ) ∈ states levels := by
  simp only [states, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨d, hd, σ, hσ, rfl⟩

/-- A passing certificate check gives every message of `fullMsg fns` from a storage of
level `d`: both sides agree, the next storage is exact, and `target` accepts it. -/
theorem step_of_cert {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {s0 : List (Nat × Nat)} {fns : List Fn} {next : Observable → List (Nat × Nat)}
    {levels : List (List (List (Nat × Nat)))} {closed : Bool}
    (hdep : deployedStorage fuel c = some s0)
    (hitems : (items fns levels).all (itemOk fuel c code next levels closed) = true)
    (hdirty : (states levels).all (dirtyOk next levels closed) = true)
    (hshape : fns.all (Dirty.fnShapeOk c) = true) (htgt : Dirty.TargetDirty code fns)
    {d : Nat} {σ : List (Nat × Nat)} (hσ : (d, σ) ∈ states levels) {m : Msg}
    (hm : fullMsg fns m) :
    ∃ obs, Source.run fuel c (m.call σ) = some obs ∧ Target.run code (m.call σ) = some obs ∧
      (needExact levels closed d = true → Exact next obs) ∧
        target levels closed d (next obs) = true := by
  obtain ⟨fn, hfn, args, hlen, hargs, rfl⟩ := hm
  have hcall : Msg.call { calldata := calldata fn.sel args, callvalue := 0 } σ =
      { calldata := calldata fn.sel args, callvalue := 0, storage := σ } := rfl
  rw [hcall]
  by_cases hd : Dirty fn.params args
  · have hok := List.all_eq_true.mp hdirty _ hσ
    simp only [dirtyOk, Bool.and_eq_true] at hok
    refine ⟨rejected σ,
      Dirty.run_dirty hdep fn (List.all_eq_true.mp hshape fn hfn) σ args hlen hargs hd,
      htgt fn hfn σ args hlen hargs hd, fun he => ?_, hok.2⟩
    have h1 := hok.1
    simp only [he, Bool.not_true, Bool.false_or] at h1
    exact slotValue_eq_of_exactOn (slotValue_mod σ)
      (fun s hs => slotValue_of_not_mem { calldata := .empty, callvalue := 0, storage := σ } s hs)
      h1
  · have hmem := mem_calls (s := σ) hfn hlen hargs fun i hp ha => by
      cases h : fn.params[i].clean args[i]
      · exact absurd ⟨i, hp, ha, h⟩ hd
      · rfl
    have hit : (d, { calldata := calldata fn.sel args, callvalue := 0, storage := σ }) ∈
        items fns levels := by
      simp only [items, List.mem_flatMap, List.mem_map]
      exact ⟨(d, σ), hσ, _, hmem, rfl⟩
    exact stepCheck_sound (List.all_eq_true.mp hitems _ hit)

/-- A passing check of a closed certificate whose levels hold the deployed storage gives
every finite sequence of messages of `fullMsg fns` from it. -/
theorem refinesSeq_of_cert {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {s0 : List (Nat × Nat)} {fns : List Fn} {next : Observable → List (Nat × Nat)}
    {levels : List (List (List (Nat × Nat)))}
    (hdep : deployedStorage fuel c = some s0) (h0 : ∃ L ∈ levels, s0 ∈ L)
    (hitems : (items fns levels).all (itemOk fuel c code next levels true) = true)
    (hdirty : (states levels).all (dirtyOk next levels true) = true)
    (hshape : fns.all (Dirty.fnShapeOk c) = true) (htgt : Dirty.TargetDirty code fns) :
    RefinesSeq fuel c code next s0 (fullMsg fns) := fun _ =>
  refinesSeqUpTo_of_levels (fun _ σ => ∃ L ∈ levels, σ ∈ L) h0
    fun _ _ σ ⟨L, hL, hσ⟩ m hm => by
      obtain ⟨d, hd, rfl⟩ := List.getElem_of_mem hL
      have hs : (d, σ) ∈ states levels :=
        mem_states hd (by simpa [List.getD_eq_getElem?_getD, hd] using hσ)
      obtain ⟨obs, h1, h2, h3, h4⟩ := step_of_cert hdep hitems hdirty hshape htgt hs hm
      simp only [target, ite_true, List.any_eq_true, List.contains_iff_mem] at h4
      exact ⟨obs, h1, h2, fun _ => h3 (by simp [needExact]), h4⟩

/-- A passing check of an open certificate whose first level holds the deployed storage
gives every sequence of at most as many messages of `fullMsg fns` as it has levels. -/
theorem refinesSeqUpTo_of_cert {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {s0 : List (Nat × Nat)} {fns : List Fn} {next : Observable → List (Nat × Nat)}
    {levels : List (List (List (Nat × Nat)))}
    (hdep : deployedStorage fuel c = some s0) (h0 : s0 ∈ levels.getD 0 [])
    (hitems : (items fns levels).all (itemOk fuel c code next levels false) = true)
    (hdirty : (states levels).all (dirtyOk next levels false) = true)
    (hshape : fns.all (Dirty.fnShapeOk c) = true) (htgt : Dirty.TargetDirty code fns) :
    RefinesSeqUpTo fuel c code next s0 (fullMsg fns) levels.length :=
  refinesSeqUpTo_of_levels
    (fun d σ => levels.length ≤ d ∨ ∃ j ≤ d, j < levels.length ∧ σ ∈ levels.getD j [])
    (.inr ⟨0, Nat.le_refl 0, by
      cases levels with
      | nil => simp at h0
      | cons _ _ => simp, h0⟩)
    fun d hd σ hS m hm => by
      obtain ⟨j, hj, hjl, hσ⟩ := hS.resolve_left (by omega)
      obtain ⟨obs, h1, h2, h3, h4⟩ :=
        step_of_cert hdep hitems hdirty hshape htgt (mem_states hjl hσ) hm
      have h3' : d + 1 < levels.length → Exact next obs := fun hn =>
        h3 (by simp only [needExact, Bool.false_or, decide_eq_true_eq]; omega)
      refine ⟨obs, h1, h2, h3', ?_⟩
      simp only [target, Bool.false_eq_true, ite_false, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.contains_iff_mem] at h4
      rcases h4 with h4 | ⟨L, hL, hn⟩
      · exact .inl (by omega)
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
        simp only [List.length_take] at hi
        refine .inr ⟨i, by omega, by omega, ?_⟩
        rw [List.getElem_take] at hn
        simpa [List.getD_eq_getElem?_getD, show i < levels.length by omega] using hn

end SolidCore.Refinement.Seq
