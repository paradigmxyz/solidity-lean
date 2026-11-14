import SolidCore.Refinement.Solar.AssembleCallValueZeroSeg

/-!
# The oracle of a run with calls, creations and GAS reads

A segment that cuts at CALL, CREATE2 and GAS reads its answers from two tables: the run's table
(`RunOracle.RunTable`, indexed by the messages a world sent, calls and creations alike, and by its GAS reads)
and the table of its creations (`AssembleCreateSeg.CreateTable`). The oracle of both is
`createOracle (tableOracle base T) A`. These facts say each cut lemma holds under it:

* `apply_call_createOracle`: a call is answered as by `tableOracle base T` (the world with a call has a
  call as its last message), so `AssembleCallValueSeg.callValue_cut` and
  `AssembleCallValueZeroSeg.call0_cut` hold under the combined oracle as stated;
* `AssembleCreateSeg.create2_cut` holds for any base, so for `tableOracle base T` (whose table then needs an
  entry at the creation's message index, which only its transient storage after the creation reads);
* the return data of the last message is kept by GAS reads and logs (`rdRel_read`, `rdRel_log`) after a
  creation, as `RunOracle` keeps it after a call.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateSegOracle

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleCreateSeg

/-- The return data of a world whose last message is no creation is the base oracle's. -/
theorem returndataByte_other {o : Oracle} {A : CreateTable} {w : List Event}
    (h : lastCreate w = false) : returndataByte (createOracle o A) w = returndataByte o w := by
  funext i
  simp [returndataByte, createOracle, h]

/-- **A call is answered as by the base oracle.** -/
theorem apply_call_createOracle (o : Oracle) (A : CreateTable) (call : Call)
    (k : SolarTV.Machine.CallKind) (ops : List Word) (s : State) :
    Effect.apply (createOracle o A) call (.call k) ops s = Effect.apply o call (.call k) ops s := by
  simp only [Effect.apply]
  split
  · rfl
  · cases k <;>
      (simp only [called]
       rw [returndataByte_other (lastCreate_call _ _ _ _ _ _)]
       simp only [callFlag, returndataSize, createOracle, lastCreate_call, Bool.false_eq_true,
         ite_false])

/-- The return data a world whose last message is a creation leaves, after a GAS read. -/
theorem env_read {o : Oracle} {A : CreateTable} {w : List Event} (hl : lastCreate w = true)
    (n name : String) (args : List Word) (hname : name = "returndatasize" ∨ name = "returndata")
    (hargs : name = "returndatasize" → args = []) (hone : name = "returndata" → args.length = 1) :
    (createOracle o A).env name (w ++ [.read n]) args = (createOracle o A).env name w args := by
  rcases hname with rfl | rfl
  · simp [createOracle, hl, hargs rfl, CreateTable.out]
  · match args, hone rfl with
    | [i], _ => simp [createOracle, hl, CreateTable.out]

/-- **A GAS read keeps the return data of a creation.** -/
theorem rdRel_read {o : Oracle} {A : CreateTable} {w : List Event} {out : ByteArray}
    (hl : lastCreate w = true) (n : String) (h : RdRel (createOracle o A) w out) :
    RdRel (createOracle o A) (w ++ [.read n]) out := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [returndataSize]
    rw [env_read hl n _ [] (.inl rfl) (fun _ => rfl) (by simp)]
    exact h.1
  · simp only [returndataByte]
    rw [env_read hl n _ _ (.inr rfl) (by simp) (fun _ => rfl)]
    exact h.2 i hi

/-- The same after a log. -/
theorem env_log {o : Oracle} {A : CreateTable} {w : List Event} (hl : lastCreate w = true)
    (t : List Word) (d : List Memory.Byte) (name : String) (args : List Word)
    (hname : name = "returndatasize" ∨ name = "returndata")
    (hargs : name = "returndatasize" → args = []) (hone : name = "returndata" → args.length = 1) :
    (createOracle o A).env name (w ++ [.log t d]) args = (createOracle o A).env name w args := by
  rcases hname with rfl | rfl
  · simp [createOracle, hl, hargs rfl, CreateTable.out]
  · match args, hone rfl with
    | [i], _ => simp [createOracle, hl, CreateTable.out]

/-- **A log keeps the return data of a creation.** -/
theorem rdRel_log {o : Oracle} {A : CreateTable} {w : List Event} {out : ByteArray}
    (hl : lastCreate w = true) (t : List Word) (d : List Memory.Byte)
    (h : RdRel (createOracle o A) w out) : RdRel (createOracle o A) (w ++ [.log t d]) out := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [returndataSize]
    rw [env_log hl t d _ [] (.inl rfl) (fun _ => rfl) (by simp)]
    exact h.1
  · simp only [returndataByte]
    rw [env_log hl t d _ _ (.inr rfl) (by simp) (fun _ => rfl)]
    exact h.2 i hi

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSegOracle.apply_call_createOracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms apply_call_createOracle

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSegOracle.rdRel_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rdRel_read

end SolidCore.Refinement.Solar.AssembleCreateSegOracle
