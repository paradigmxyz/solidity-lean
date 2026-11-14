import SolidCore.Refinement.Solar.EthLibErr

/-!
# Runs with less gas that revert

EthLib's `reaches_low` transfers a chain of steps monotone in gas, from a frame with `k` more gas,
to the run with less gas only when that run ends with no error: `StepFails` admits REVERT, so a
run that reverts says nothing of the run with more gas. By `step_good` (no step throws a
revert, and only REVERT ends a frame with it) the transfer holds for a run that reverts too:

* `revert_step`: REVERT stops the frame, and with `k` more gas gives the same frame with `k` more
  gas (REVERT keeps its gas left).
* `reaches_lowR`, `SpecG.lowR`: a chain of steps monotone in gas from `l` with `k` more gas, and a
  run of `l` that ends with the revert error: the chain's end is the run's end with `k` more gas.
* `SpecG.lowE`: the same for a run that ends with no error or with the revert error.
-/

namespace EthLib.Execution.Evm.RevertErr

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-- **REVERT keeps its gas left**: it stops the frame, and with `k` more gas it gives the same frame
with `k` more gas. -/
theorem revert_step (hfork : .byzantium ≤ fork) {low b : Evm fork Nat}
    (hlt : low.pc < low.code.size) (hop : Op.ofByte fork low.code[low.pc] = some .revert)
    (h : step fork low = .ok (.next b)) :
    b.running = false ∧ ∀ k, step fork (addGas k low) = .ok (.next (addGas k b)) := by
  have hrun := instruction_revert (Meter := Nat) hfork
  rw [step_of_instruction hlt hop hrun, revertStep_eq] at h
  cases hc : returnStep low with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h
    simp only [Functor.map, Except.map, Except.ok.injEq, StepResult.next.injEq] at h
    subst h
    refine ⟨(haltWithOutput_stops hc).2, fun k => ?_⟩
    rw [step_of_instruction (evm := addGas k low) hlt hop hrun, revertStep_eq]
    obtain ⟨st, sz, rest, hs⟩ : ∃ st sz rest, low.stack.val = st :: sz :: rest := by
      rcases hstk : low.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
      · simp [returnStep, haltWithOutput, popWord, Stack.pop, hstk, bind, Except.bind] at hc
      · simp [returnStep, haltWithOutput, popWord, Stack.pop, hstk, bind, Except.bind, pure,
          Except.pure] at hc
      · exact ⟨x, y, rest, by simp⟩
    rw [returnStep_cons hs] at hc
    rw [returnStep_cons (evm := addGas k low) hs]
    have hf := follows_map_charge (fork := fork) (k := k) (gas := low.gas)
      (cost := (extendMemory low.memory.size [(st, sz)]).cost)
      (F := fun gas => { low with
            stack := ⟨rest, by have := low.stack.property; rw [hs] at this; simp at this; omega⟩
            memory := memoryExtend low.memory (extendMemory low.memory.size [(st, sz)]).expandBy
            gas
            output := memoryReadBytes
              (memoryExtend low.memory (extendMemory low.memory.size [(st, sz)]).expandBy)
              st.toNat sz.toNat
            running := false })
      (fun _ => rfl)
    simp only [GasMeter.charge] at hc hf ⊢
    by_cases hlt' : low.gas < (extendMemory low.memory.size [(st, sz)]).cost
    · simp [hlt', Except.map] at hc
    · have h2 : ¬ low.gas + k < (extendMemory low.memory.size [(st, sz)]).cost := by omega
      simp only [hlt', h2, ↓reduceIte, Except.map, Except.ok.injEq] at hc hf ⊢
      subst hc
      have hg : low.gas + k - (extendMemory low.memory.size [(st, sz)]).cost =
          low.gas - (extendMemory low.memory.size [(st, sz)]).cost + k := by omega
      simp only [addGas]
      simp only [h2, ↓reduceIte, Functor.map, Except.map, hg]

theorem measure_next {low b : Evm fork Nat} (running : low.running = true)
    (h : step fork low = .ok (.next b)) : measure b < measure low :=
  step_decreases fork running h

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- **A chain of steps monotone in gas, and a run with less gas that reverts**: from `low` with
`k` more gas to `z`. When the loop runs `low`, which has no revert error, to a frame `s` with
the revert error, `z` is a frame `m` with `k` more gas, and the loop runs `m` to `s` too. -/
theorem reaches_lowR (hfork : .byzantium ≤ fork) {hi z : Evm fork Nat}
    (hr : Reaches (StepG fork) hi z) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low → low.error ≠ some .revert →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error = some .revert → ∃ m within', z = addGas k m ∧
          runFrame (step fork) (step_decreases fork) bound runChild m within' = .ok s := by
  induction hr with
  | refl =>
    rintro k low rfl - within s hs -
    exact ⟨low, within, rfl, hs⟩
  | @step a b' c hstep hrest ih =>
    rintro k low rfl hlow within s hs hrev
    obtain ⟨hstep, mono⟩ := hstep
    have running : low.running = true := by simpa using hstep.running
    have good := step_good (fork := fork) low
    -- A stopped frame reaches only itself.
    have stopped : ∀ {b' z' : Evm fork Nat}, b'.running = false → Reaches (StepG fork) b' z' →
        z' = b' := by
      intro b' z' hb' hr'
      cases hr' with
      | refl => rfl
      | step h1 _ =>
        have := h1.1.running
        rw [hb'] at this
        cases this
    -- A REVERT that the step from low runs ends the run there.
    have atRevert : ∀ b, step fork low = .ok (.next b) → b.error = some .revert →
        ∃ m within', c = addGas k m ∧
          runFrame (step fork) (step_decreases fork) bound runChild m within' = .ok s := by
      intro b hb hbe
      rcases good.2 b hb hbe with h | ⟨hlt, hop⟩
      · exact absurd h hlow
      obtain ⟨hbr, hk⟩ := revert_step hfork hlt hop hb
      have hn := hk k
      have hb' : _ := hstep
      cases hstep with
      | next _ hn' =>
        rw [hn] at hn'
        cases hn'
        rw [runFrame_of_step_eq_next running hb, runFrame_of_running_eq_false hbr] at hs
        cases hs
        refine ⟨_, Nat.le_trans (gasHeld_le_of_measure_lt (measure_next running hb)) within,
          stopped (by simpa using hbr) hrest, ?_⟩
        exact runFrame_of_running_eq_false hbr
      | halt _ hn' _ =>
        rw [hn] at hn'
        cases hn'
    rcases mono k low rfl with fails | ⟨b, hb, hh⟩
    · rcases fails with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
      · have hne := good.1 e he
        cases ab : e.aborts
        · rw [runFrame_of_step_eq_error running he ab] at hs
          cases hs
          simp only [exceptionalHalt, Option.some.injEq] at hrev
          exact absurd hrev hne
        · rw [runFrame_of_step_eq_abort running he ab] at hs
          cases hs
      · have hsb : s = b := by
          rw [runFrame_of_step_eq_next running hb, runFrame_of_running_eq_false hbr] at hs
          cases hs; rfl
        subst hsb
        exact atRevert s hb hrev
    · by_cases hbe : b.error = some .revert
      · exact atRevert b hb hbe
      rw [runFrame_of_step_eq_next running hb] at hs
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih k b rfl hbe _ hs hrev
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A chain of steps monotone in gas from `low` with `k` more gas to a stopped `z`: when the loop
runs `low` to a frame `s` with the revert error, `z` is `s` with `k` more gas. -/
theorem low_of_reachesR (hfork : .byzantium ≤ fork) {hi z : Evm fork Nat}
    (hr : Reaches (StepG fork) hi z) (hz : z.running = false) (k : Nat) (low : Evm fork Nat)
    (e : hi = addGas k low) (hlow : low.error ≠ some .revert)
    (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat}
    (hs : runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s)
    (hrev : s.error = some .revert) : z = addGas k s := by
  obtain ⟨m, _, rfl, hm⟩ := reaches_lowR hfork hr k low e hlow within hs hrev
  rw [runFrame_of_running_eq_false (by simpa using hz)] at hm
  cases hm
  rfl

/-- **`SpecG.low` for a run that reverts**: a specification over steps monotone in gas, from `l`
with `k` more gas, and a run of `l` (with no revert error) to a frame `s` with the revert error:
`s` with `k` more gas meets the postcondition. -/
theorem SpecG.lowR (hfork : .byzantium ≤ fork) {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    {k : Nat} {l : Evm fork Nat} (hp : P (addGas k l)) (hl : l.error ≠ some .revert)
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hrev : s.error = some .revert) : Q (addGas k s) := by
  obtain ⟨z, hr, hz, hq⟩ := h _ hp
  rw [← low_of_reachesR hfork hr hz k l rfl hl within hs hrev]
  exact hq

/-- **`SpecG.low` for a run that ends with no error or reverts.** -/
theorem SpecG.lowE (hfork : .byzantium ≤ fork) {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    {k : Nat} {l : Evm fork Nat} (hp : P (addGas k l)) (hl : l.error ≠ some .revert)
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none ∨ s.error = some .revert) : Q (addGas k s) := by
  rcases hok with hok | hrev
  · exact SpecG.low h hp within hs hok
  · exact SpecG.lowR hfork h hp hl within hs hrev

end Loop

/-- info: 'EthLib.Execution.Evm.RevertErr.SpecG.lowE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpecG.lowE

end EthLib.Execution.Evm.RevertErr
