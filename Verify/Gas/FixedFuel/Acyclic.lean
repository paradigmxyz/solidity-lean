import SolarTV.EVMIR.Program

/-!
# The fixed fuel of a loop-free EVM IR program

The driver runs the final EVM IR at a fixed fuel (the last stage's fuel) and the gas bound is
the loop checker's at that fuel. This module proves when such a fuel suffices, from the program
alone and under every oracle: if no block jumps dynamically and every block's static targets
have a smaller rank than the block (a block past the program has rank 0), every run ends within
block 0's rank plus one blocks (`ends_of_rank`), and so at every fuel from there on. The rank is
untrusted data: `rankOk` checks it and the kernel evaluates the check.

* `targets b instrs`: the blocks the instructions of block `b` can continue to (`exec`'s
  `.inr`), or `none` when one jump is dynamic (`jumpDyn`, `jumpiDyn`), whose target is a word.
* `exec_mem_targets`: every continuation of `exec` is in `targets`.
* `rankOk p rk`: `rk` ranks every block, and every static target of block `b` ranks below it.
* `ends_of_rank`: `rankOk p rk = true` and `rankFuel p rk ≤ N` give
  `(run o p call N).isSome = true` for every oracle and call.

A program with a loop or a dynamic jump has no rank: its fuel is the fixed-fuel loop stage's
(`Verify.Gas.FixedFuel.Run`), not this one.
-/

namespace Verify.Gas.FixedFuel.Acyclic

open SolarTV SolarTV.Machine SolarTV.EVM.Program

/-- The blocks the instructions of block `b` continue to, or `none` for a dynamic jump. -/
def targets (b : Nat) : List Instr → Option (List Nat)
  | [] => some [b + 1]
  | .jump t :: _ => some [t]
  | .jumpi t :: rest => (targets b rest).map (t :: ·)
  | .jumpTable ts :: _ => some ts
  | .jumpDyn :: _ => none
  | .jumpiDyn :: _ => none
  | .stop :: _ => some []
  | .ret :: _ => some []
  | .revert :: _ => some []
  | .invalid :: _ => some []
  | .op _ :: rest => targets b rest
  | .effect _ _ :: rest => targets b rest
  | .pushLabel _ :: rest => targets b rest

/-- **Every continuation of a block is one of its static targets.** -/
theorem exec_mem_targets (o : Oracle) (call : Call) (b : Nat) :
    ∀ (instrs : List Instr) (stack : EVM.Stack) (s : State) {ts : List Nat} {t : Nat}
      {stack' : EVM.Stack} {s' : State},
      targets b instrs = some ts → exec o call b instrs stack s = .inr (t, stack', s') → t ∈ ts
  | [], _, _, _, _, _, _, ht, he => by
    simp only [targets, Option.some.injEq] at ht
    simp only [exec, Sum.inr.injEq, Prod.mk.injEq] at he
    subst ht; simp [he.1]
  | .op op :: rest, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets] at ht
    simp only [exec] at he
    split at he
    · cases he
    · exact exec_mem_targets o call b rest _ _ ht he
  | .effect e n :: rest, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets] at ht
    rw [exec] at he
    dsimp only at he
    split at he
    · cases he
    · split at he
      · cases he
      · rename_i result s'' _
        cases result <;> dsimp only at he <;> split at he <;>
          first | cases he | exact exec_mem_targets o call b rest _ _ ht he
  | .jump t₀ :: _, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets, Option.some.injEq] at ht
    simp only [exec] at he
    split at he
    · cases he
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at he
      subst ht; simp [he.1]
  | .jumpi t₀ :: rest, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets] at ht
    obtain ⟨ts₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp ht
    simp only [exec] at he
    split at he
    · cases he
    · split at he
      · split at he
        · exact List.mem_cons_of_mem _ (exec_mem_targets o call b rest _ _ h₀ he)
        · simp only [Sum.inr.injEq, Prod.mk.injEq] at he
          exact List.mem_cons.mpr (.inl he.1.symm)
      · cases he
  | .pushLabel l :: rest, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets] at ht
    simp only [exec] at he
    split at he
    · cases he
    · exact exec_mem_targets o call b rest _ _ ht he
  | .jumpDyn :: _, _, _, _, _, _, _, ht, _ => by simp [targets] at ht
  | .jumpiDyn :: _, _, _, _, _, _, _, ht, _ => by simp [targets] at ht
  | .jumpTable ts₀ :: _, stack, s, ts, t, stack', s', ht, he => by
    simp only [targets, Option.some.injEq] at ht
    subst ht
    simp only [exec] at he
    split at he
    · split at he
      · next h =>
        simp only [Sum.inr.injEq, Prod.mk.injEq] at he
        exact he.1 ▸ List.mem_of_getElem? h
      · cases he
    · cases he
  | .stop :: _, _, _, _, _, _, _, _, he => by simp [exec] at he
  | .ret :: _, _, _, _, _, _, _, _, he => by simp [exec] at he
  | .revert :: _, _, _, _, _, _, _, _, he => by simp [exec] at he
  | .invalid :: _, _, _, _, _, _, _, _, he => by simp [exec] at he

/-- The rank of block `t` under `rk`: 0 past the program, where the next step halts. -/
def rankOf (rk : List Nat) (n t : Nat) : Nat := if t < n then rk.getD t 0 else 0

/-- **The rank check**: a rank for every block, and every static target of block `b` ranked
below `b`; a block with a dynamic jump fails it. -/
def rankOk (p : Program) (rk : List Nat) : Bool :=
  rk.length == p.blocks.length &&
    (List.range p.blocks.length).all fun b =>
      match targets b (p.blocks.getD b []) with
      | some ts => ts.all fun t => decide (rankOf rk p.blocks.length t < rk.getD b 0)
      | none => false

/-- The fuel a rank proves: block 0's rank plus one. -/
def rankFuel (p : Program) (rk : List Nat) : Nat := rankOf rk p.blocks.length 0 + 1

theorem iterate_isSome_mono {σ : Type} (step : σ → Option ((Halt × State) ⊕ σ)) {n m : Nat}
    (hnm : n ≤ m) {x : σ} (h : (iterate step n x).isSome = true) :
    (iterate step m x).isSome = true := by
  induction hnm with
  | refl => exact h
  | step _ ih =>
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ih
    rw [iterate_mono step _ x r hr]; rfl

/-- From every block, with fuel its rank plus one, the run ends. -/
theorem ends_from {p : Program} {rk : List Nat} (h : rankOk p rk = true) (o : Oracle)
    (call : Call) :
    ∀ (k b : Nat) (stack : EVM.Stack) (s : State), rankOf rk p.blocks.length b = k →
      (iterate (block o call p) (k + 1) (b, stack, s)).isSome = true := by
  simp only [rankOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨_, hall⟩ := h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro b stack s hk
    rcases hb : p.blocks[b]? with _ | instrs
    · simp [iterate, block, hb]
    · obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hb
      have hget : p.blocks.getD b [] = instrs := by simp [List.getD, hb]
      have hb' := hall b hlt
      rw [hget] at hb'
      split at hb'
      · next ts hts =>
        rw [List.all_eq_true] at hb'
        rcases he : exec o call b instrs stack s with r | ⟨t, stack', s'⟩
        · simp [iterate, block, hb, he]
        · have hmem := exec_mem_targets o call b instrs stack s hts he
          have hr := of_decide_eq_true (hb' t hmem)
          have hkb : rankOf rk p.blocks.length b = rk.getD b 0 := by simp [rankOf, hlt]
          rw [← hkb, hk] at hr
          have hstep : iterate (block o call p) (k + 1) (b, stack, s) =
              iterate (block o call p) k (t, stack', s') := by
            simp [iterate, block, hb, he]
          rw [hstep]
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact iterate_isSome_mono _ (by omega)
            (ih (rankOf rk p.blocks.length t) (by omega) t stack' s' rfl)
      · cases hb'

/-- **The fixed fuel suffices for a ranked program**: under every oracle, every call's run ends
within `rankFuel p rk` blocks, so within every fuel from there on. -/
theorem ends_of_rank {p : Program} {rk : List Nat} (h : rankOk p rk = true) {N : Nat}
    (hN : rankFuel p rk ≤ N) (o : Oracle) (call : Call) : (run o p call N).isSome = true :=
  iterate_isSome_mono _ hN (ends_from h o call _ 0 [] (State.initial call) rfl)

end Verify.Gas.FixedFuel.Acyclic
