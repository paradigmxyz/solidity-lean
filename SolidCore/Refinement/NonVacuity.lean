import SolidCore.Refinement.Headline
import SolidCore.Refinement.Behaviours

/-!
# The headline theorems on concrete calls

Each headline theorem (`Headline.c1`, `w1`, `w4`, `c4`, `w5`) states that a specification
holds of solar's bytecode on EthLib. This module checks that none of them holds for a trivial
reason, by reading off them, for concrete calls, the exact observable both sides give:

* each `*_target` theorem is EthLib's run of the bytecode on one call, derived from the headline
  alone; each `*_source` theorem is SolidCore's run of the same call, derived from the verified
  specification alone, and the two agree (the relation is checked on a call both sides finish);
* the calls include a success that returns data, a success that writes storage, and a revert with
  `Panic(0x11)` data, so return data, storage and revert data are each pinned;
* each `*_rejects` theorem shows the bytecode does not give a neighbouring observable (one
  more in the returned word, or success where it reverts).

Were `Satisfies`, `Stage` or `Refines` a relation that related everything, the headline would
carry no information about `Target.run`, and neither the `*_target` nor the `*_rejects`
theorems could be proved.
-/

namespace SolidCore.Refinement.NonVacuity

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Verify

/-- A specification whose postcondition pins one observable gives that observable. -/
theorem run_of_pinned {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (h : Satisfies S p scope pre post) {call : Call}
    (hc : scope call) (hp : pre call) {o : Observable} (pin : ∀ obs, post call obs → obs = o) :
    S.run p call = some o := by
  obtain ⟨obs, hrun, hpost⟩ := h call hc hp
  rw [hrun, pin obs hpost]

/-- The call of `sel` on `args` with no value from the storage `σ`. -/
def callAt (sel : Nat) (args : List Nat) (σ : List (Nat × Nat)) : Call :=
  { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }

theorem argWords_callAt (sel : Nat) (args : List Nat) (σ : List (Nat × Nat))
    (h : ∀ a ∈ args, a < 2 ^ 256) : argWords args.length (callAt sel args σ) = args :=
  argWords_calldata sel args h 0 σ

theorem fullScope_callAt {fn : Fn} {fns : List Fn} (hfn : fn ∈ fns) (args : List Nat)
    (hlen : args.length = fn.params.length) (h : ∀ a ∈ args, a < 2 ^ 256) (σ : List (Nat × Nat)) :
    fullScope fns σ (callAt fn.sel args σ) :=
  ⟨fn, hfn, args, hlen, h, rfl⟩

theorem obs_eq {o : Observable} {s : Bool} {out : List Nat} {logs : List (List Nat × List Nat)}
    {st : Nat → Nat} (h1 : o.success = s) (h2 : o.output = out) (h3 : o.logs = logs)
    (h4 : ∀ slot, o.storage slot = st slot) : o = ⟨s, out, logs, st⟩ := by
  cases o
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  rw [show _ = st from funext h4]

/-! ## w5: `f(a, b)` returns `a + b` or reverts with `Panic(0x11)` -/

namespace W5

open SolidCore.Refinement.Corpus.W5

def fn : Fn := ⟨Bytecode.W5.Main.fSelector, [(.uint 256), (.uint 256)]⟩

/-- `f(1, 2)`. -/
def add : Call := callAt fn.sel [1, 2] []

/-- `f(2 ^ 256 - 1, 1)`, which overflows. -/
def overflow : Call := callAt fn.sel [2 ^ 256 - 1, 1] []

def addObs : Observable := ⟨true, word 3, [], fun _ => 0⟩

def overflowObs : Observable := ⟨false, panic 0x11, [], fun _ => 0⟩

theorem add_scope : Verify.W5.scope add :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [1, 2] rfl (by decide) []

theorem overflow_scope : Verify.W5.scope overflow :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [2 ^ 256 - 1, 1] rfl (by decide) []

theorem add_pin (obs : Observable) (h : Verify.W5.post add obs) : obs = addObs := by
  have hw : argWords 2 add = [1, 2] := argWords_callAt fn.sel [1, 2] [] (by decide)
  simp only [Verify.W5.post, hw] at h
  obtain ⟨⟨hs, ho⟩, hl, hst⟩ := (by simpa using h :
    (obs.success = true ∧ obs.output = word 3) ∧ obs.logs = [] ∧ ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

theorem overflow_pin (obs : Observable) (h : Verify.W5.post overflow obs) : obs = overflowObs := by
  have hw : argWords 2 overflow = [2 ^ 256 - 1, 1] := argWords_callAt fn.sel [2 ^ 256 - 1, 1] [] (by decide)
  simp only [Verify.W5.post, hw] at h
  obtain ⟨⟨hs, ho⟩, hl, hst⟩ := (by simpa using h :
    (obs.success = false ∧ obs.output = panic 0x11) ∧ obs.logs = [] ∧
      ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

/-- solar's bytecode returns `3` on `f(1, 2)`, read off the headline. -/
theorem add_target : Target.run code add = some addObs :=
  run_of_pinned Headline.w5 add_scope trivial add_pin

/-- solar's bytecode reverts with `Panic(0x11)` on `f(2 ^ 256 - 1, 1)`. -/
theorem overflow_target : Target.run code overflow = some overflowObs :=
  run_of_pinned Headline.w5 overflow_scope trivial overflow_pin

/-- SolidCore gives the same observables, read off the verified specification. -/
theorem source : ∃ c, contract? = .ok c ∧
    Source.run fuel c add = some addObs ∧ Source.run fuel c overflow = some overflowObs := by
  obtain ⟨c, hc, h⟩ := Verify.W5.satisfies
  exact ⟨c, hc, run_of_pinned h add_scope trivial add_pin,
    run_of_pinned h overflow_scope trivial overflow_pin⟩

theorem rejects : Target.run code add ≠ some ⟨true, word 4, [], fun _ => 0⟩ ∧
    Target.run code overflow ≠ some ⟨true, [], [], fun _ => 0⟩ := by
  rw [add_target, overflow_target]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (Option.map fun o : Observable => o.output) h
    simp only [addObs, Option.map_some, Option.some.injEq] at this
    exact absurd this (by decide)
  · have := congrArg (Option.map fun o : Observable => o.success) h
    simp [overflowObs] at this

end W5

/-! ## w1: `f(x)` returns `x + 1` or reverts with `Panic(0x11)` -/

namespace W1

open SolidCore.Refinement.Corpus.W1

def fn : Fn := ⟨Bytecode.W1.Main.fSelector, [(.uint 256)]⟩

def inc : Call := callAt fn.sel [41] []

def overflow : Call := callAt fn.sel [2 ^ 256 - 1] []

def incObs : Observable := ⟨true, word 42, [], fun _ => 0⟩

def overflowObs : Observable := ⟨false, panic 0x11, [], fun _ => 0⟩

theorem inc_pin (obs : Observable) (h : Verify.W1.post inc obs) : obs = incObs := by
  have hw : argWords 1 inc = [41] := argWords_callAt fn.sel [41] [] (by decide)
  simp only [Verify.W1.post, hw] at h
  obtain ⟨⟨hs, ho⟩, hl, hst⟩ := (by simpa using h :
    (obs.success = true ∧ obs.output = word 42) ∧ obs.logs = [] ∧ ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

theorem overflow_pin (obs : Observable) (h : Verify.W1.post overflow obs) : obs = overflowObs := by
  have hw : argWords 1 overflow = [2 ^ 256 - 1] := argWords_callAt fn.sel [2 ^ 256 - 1] [] (by decide)
  simp only [Verify.W1.post, hw] at h
  obtain ⟨⟨hs, ho⟩, hl, hst⟩ := (by simpa using h :
    (obs.success = false ∧ obs.output = panic 0x11) ∧ obs.logs = [] ∧
      ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

theorem inc_scope : Verify.W1.scope inc :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [41] rfl (by decide) []

theorem overflow_scope : Verify.W1.scope overflow :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [2 ^ 256 - 1] rfl (by decide) []

theorem inc_target : Target.run code inc = some incObs :=
  run_of_pinned Headline.w1 inc_scope trivial inc_pin

theorem overflow_target : Target.run code overflow = some overflowObs :=
  run_of_pinned Headline.w1 overflow_scope trivial overflow_pin

theorem source : ∃ c, contract? = .ok c ∧
    Source.run fuel c inc = some incObs ∧ Source.run fuel c overflow = some overflowObs := by
  obtain ⟨c, hc, h⟩ := Verify.W1.satisfies
  exact ⟨c, hc, run_of_pinned h inc_scope trivial inc_pin,
    run_of_pinned h overflow_scope trivial overflow_pin⟩

theorem rejects : Target.run code inc ≠ some ⟨true, word 43, [], fun _ => 0⟩ := by
  rw [inc_target]
  intro h
  have := congrArg (Option.map fun o : Observable => o.output) h
  simp only [incObs, Option.map_some, Option.some.injEq] at this
  exact absurd this (by decide)

end W1

/-! ## w4: `set(v)` stores `v` in slot 0 -/

namespace W4

open SolidCore.Refinement.Corpus.W4

def fn : Fn := ⟨Bytecode.W4.Main.setSelector, [(.uint 256)]⟩

def set9 : Call := callAt fn.sel [9] []

def set9Obs : Observable := ⟨true, [], [], fun slot => if slot % 2 ^ 256 = 0 then 9 else 0⟩

theorem set9_pin (obs : Observable) (h : Verify.W4.post set9 obs) : obs = set9Obs := by
  have hw : argWords 1 set9 = [9] := argWords_callAt fn.sel [9] [] (by decide)
  simp only [Verify.W4.post, hw] at h
  obtain ⟨hs, ho, hl, hst⟩ := (by simpa using h :
    obs.success = true ∧ obs.output = [] ∧ obs.logs = [] ∧
      ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then 9 else 0)
  exact obs_eq hs ho hl hst

theorem set9_scope : Verify.W4.scope set9 :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [9] rfl (by decide) []

/-- solar's bytecode leaves `9` in slot 0 on `set(9)`, read off the headline. -/
theorem set9_target : Target.run code set9 = some set9Obs :=
  run_of_pinned Headline.w4 set9_scope trivial set9_pin

theorem source : ∃ c, contract? = .ok c ∧ Source.run fuel c set9 = some set9Obs := by
  obtain ⟨c, hc, h⟩ := Verify.W4.satisfies
  exact ⟨c, hc, run_of_pinned h set9_scope trivial set9_pin⟩

/-- It does not leave slot 0 holding `8`. -/
theorem rejects : Target.run code set9 ≠ some ⟨true, [], [], fun slot => if slot = 0 then 8 else 0⟩ := by
  rw [set9_target]
  intro h
  have := congrArg (Option.map fun o => o.storage 0) h
  simp [set9Obs] at this

end W4

/-! ## c1: `f(x)` on a `uint8` returns `3 * x + 1` or reverts with `Panic(0x11)` -/

namespace C1

open SolidCore.Refinement.Corpus.C1

def two : Call := callAt Bytecode.C1.Main.fSelector [2] []

def big : Call := callAt Bytecode.C1.Main.fSelector [85] []

def twoObs : Observable := ⟨true, word 7, [], fun _ => 0⟩

def bigObs : Observable := ⟨false, panic 0x11, [], fun _ => 0⟩

theorem mem_calls {x : Nat} (hx : x < 2 ^ 8) :
    callAt Bytecode.C1.Main.fSelector [x] [] ∈ calls fns [[]] := by
  unfold calls
  refine List.mem_flatMap.mpr ⟨[], List.mem_singleton_self _, ?_⟩
  refine List.mem_flatMap.mpr ⟨⟨Bytecode.C1.Main.fSelector, [.uint 8]⟩, List.mem_singleton_self _, ?_⟩
  refine List.mem_map.mpr ⟨[x], ?_, rfl⟩
  show [x] ∈ (Param.uint 8).values.flatMap fun v => ([[]] : List (List Nat)).map (v :: ·)
  exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, List.mem_singleton_self _⟩

theorem two_pin (obs : Observable) (h : Verify.C1.post two obs) : obs = twoObs := by
  have hw : argWords 1 two = [2] := argWords_callAt Bytecode.C1.Main.fSelector [2] [] (by decide)
  simp only [Verify.C1.post, hw] at h
  obtain ⟨⟨hs, ho⟩, -, hl, hst⟩ := (by simpa using h :
    (obs.success = true ∧ obs.output = word 7) ∧ True ∧ obs.logs = [] ∧
      ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

theorem big_pin (obs : Observable) (h : Verify.C1.post big obs) : obs = bigObs := by
  have hw : argWords 1 big = [85] := argWords_callAt Bytecode.C1.Main.fSelector [85] [] (by decide)
  simp only [Verify.C1.post, hw] at h
  obtain ⟨-, ⟨hs, ho⟩, hl, hst⟩ := (by simpa using h :
    True ∧ (obs.success = false ∧ obs.output = panic 0x11) ∧ obs.logs = [] ∧
      ∀ slot, obs.storage slot = 0)
  exact obs_eq hs ho hl hst

theorem two_target : Target.run code two = some twoObs :=
  run_of_pinned Headline.c1 (mem_calls (by decide)) trivial two_pin

theorem big_target : Target.run code big = some bigObs :=
  run_of_pinned Headline.c1 (mem_calls (by decide)) trivial big_pin

theorem source : ∃ c, contract? = .ok c ∧
    Source.run fuel c two = some twoObs ∧ Source.run fuel c big = some bigObs := by
  obtain ⟨c, hc, -, h⟩ := Verify.C1.satisfies
  exact ⟨c, hc, run_of_pinned h (mem_calls (by decide)) trivial two_pin,
    run_of_pinned h (mem_calls (by decide)) trivial big_pin⟩

theorem rejects : Target.run code big ≠ some ⟨true, word 256, [], fun _ => 0⟩ := by
  rw [big_target]
  intro h
  have := congrArg (Option.map fun o : Observable => o.success) h
  simp [bigObs] at this

end C1

/-! ## c4: `add(x)` updates two `uint8` fields packed in slot 0 -/

namespace C4

open SolidCore.Refinement.Corpus.C4

def fn : Fn := ⟨Bytecode.C4.Main.addSelector, [(.uint 8)]⟩

def add3 : Call := callAt fn.sel [3] Verify.C4.deployed

/-- A dirty word for a `uint8` parameter. -/
def dirty : Call := callAt fn.sel [256] Verify.C4.deployed

def add3Obs : Observable :=
  ⟨true, word 3, [], fun slot => if slot % 2 ^ 256 = 0 then 3 + (7 ^^^ 3) * 2 ^ 8 else 0⟩

def dirtyObs : Observable := ⟨false, [], [], fun slot => slotValue Verify.C4.deployed slot⟩

theorem add3_pin (obs : Observable) (h : Verify.C4.post add3 obs) : obs = add3Obs := by
  have hw : argWords 1 add3 = [3] := argWords_callAt fn.sel [3] Verify.C4.deployed (by decide)
  simp only [Verify.C4.post, hw] at h
  obtain ⟨⟨hs, ho, hst⟩, hl⟩ := (by simpa using h :
    (obs.success = true ∧ obs.output = word 3 ∧
      ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then 3 + (7 ^^^ 3) * 2 ^ 8 else 0) ∧
    obs.logs = [])
  exact obs_eq hs ho hl hst

theorem dirty_pin (obs : Observable) (h : Verify.C4.post dirty obs) : obs = dirtyObs := by
  have hw : argWords 1 dirty = [256] := argWords_callAt fn.sel [256] Verify.C4.deployed (by decide)
  simp only [Verify.C4.post, hw] at h
  obtain ⟨⟨hs, ho, hst⟩, hl⟩ := (by simpa using h :
    (obs.success = false ∧ obs.output = [] ∧
      ∀ slot, obs.storage slot = slotValue Verify.C4.deployed slot) ∧ obs.logs = [])
  exact obs_eq hs ho hl hst

theorem add3_scope : Verify.C4.scope add3 :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [3] rfl (by decide) _

theorem dirty_scope : Verify.C4.scope dirty :=
  fullScope_callAt (fn := fn) (List.mem_singleton_self _) [256] rfl (by decide) _

/-- solar's bytecode returns `3` and packs `v = 3`, `w = 7 ^ 3` into slot 0 on `add(3)`. -/
theorem add3_target : Target.run code add3 = some add3Obs :=
  run_of_pinned Headline.c4 add3_scope trivial add3_pin

/-- It reverts with empty data and keeps the storage on a dirty word. -/
theorem dirty_target : Target.run code dirty = some dirtyObs :=
  run_of_pinned Headline.c4 dirty_scope trivial dirty_pin

theorem source : ∃ c, contract? = .ok c ∧
    Source.run fuel c add3 = some add3Obs ∧ Source.run fuel c dirty = some dirtyObs := by
  obtain ⟨c, hc, -, h⟩ := Verify.C4.satisfies
  exact ⟨c, hc, run_of_pinned h add3_scope trivial add3_pin,
    run_of_pinned h dirty_scope trivial dirty_pin⟩

/-- It does not leave `w` unchanged. -/
theorem rejects : Target.run code add3 ≠
    some ⟨true, word 3, [], fun slot => if slot % 2 ^ 256 = 0 then 3 + 7 * 2 ^ 8 else 0⟩ := by
  rw [add3_target]
  intro h
  have := congrArg (Option.map fun o => o.storage 0) h
  simp [add3Obs] at this

end C4


/--
info: 'SolidCore.Refinement.NonVacuity.W5.add_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms W5.add_target

/--
info: 'SolidCore.Refinement.NonVacuity.W5.rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms W5.rejects

/--
info: 'SolidCore.Refinement.NonVacuity.C4.dirty_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms C4.dirty_target

/--
info: 'SolidCore.Refinement.NonVacuity.C1.source' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms C1.source

end SolidCore.Refinement.NonVacuity
