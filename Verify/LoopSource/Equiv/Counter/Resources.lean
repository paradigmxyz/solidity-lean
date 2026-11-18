import W1Proofs.Segment
import Verify.Gas.FixedFuel.Gas
import Verify.LoopSource.Equiv.Counter.Expected
import Verify.LoopSource.Equiv.Counter.Closed
import Verify.LoopSource.Equiv.Counter.Gas
import Verify.LoopSource.Equiv.Counter.Proofs.Execution

/-!
# Counter.bump's resources under an iteration bound

`counter_resources`: on every call of `BumpCallBounded K` (`bump(a)` with `a ≤ K`), for `K ≤ Kmax`,
the exact emitted runtime `code` gives the source's result at every gas from
`G K = gasBoundL cert (fixedFuel 2 2 3 K)` on, and `G K < 2 ^ 64`: `Shapes.Resources`, no premise.

The fuel is the fixed-fuel stage's (`Verify/Gas/FixedFuel`, the driver's `fixed_fuel.py` numbers
`E = 2`, `B = 2`, `X = 3`): every call ends within `fixedFuel 2 2 3 K` blocks of the final EVM IR
`evm7` (`ends`). Its entry (blocks 0 and 6) reverts or reaches the loop header, block 8, with the
stack `[0, 0 - a, count, selector]` and no overflow of `count + a`; from the header each
iteration takes two blocks (8, 7) and lowers `0 - h` by one (`header_ends`), and the exit two. The
block facts are `sym_exec` runs of `evm7`. `stage_of_checkL_gas` with the checker's `check_ok`
carries the run to the bytes, and `gasBoundL_fixed` makes the bound the fixed-fuel `fixedGas`.
-/

namespace Verify.LoopSource.Equiv.CounterResources
open SolarTV SolarTV.Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolidCore.Refinement SolidCore.Refinement.Solar SolidCore.Refinement.Generic
open Verify.Gas.FixedFuel

@[reducible] def halts : Option ((Halt × State) ⊕ (Nat × EVM.Stack × State)) → Bool
  | some (.inl _) => true
  | _ => false

theorem ends_of_halts {o : Oracle} {call : Call} {x : Nat × EVM.Stack × State}
    (h : halts (EVM.Program.block o call evm7 x) = true) (k : Nat) : ∃ r, iterate (EVM.Program.block o call evm7) (k + 1) x = some r := by
  cases hs : EVM.Program.block o call evm7 x with
  | none => simp [hs] at h
  | some v =>
    cases v with
    | inl r => exact ⟨r, by simp [iterate, hs]⟩
    | inr _ => simp [hs] at h

/-! ## Blocks of `evm7` -/

set_option maxHeartbeats 4000000 in
theorem b0 (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hs : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xb20eb4c4) :
    EVM.Program.block o call evm7 (0, [], State.initial call) = some (.inr (6, [0xb20eb4c4],
      { memory := Mem.initial, storage := (State.initial call).storage,
        transient := (State.initial call).transient, world := (State.initial call).world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b6_pass (o : Oracle) (call : Call) (s : State) (sel : EvmRules.Word)
    (hz : ¬BitVec.ofNat 256 call.calldata.size < 36)
    (ho : ¬EvmRules.Evm.add (s.storage 0) (calldataWord call 4) < s.storage 0)
    (hl : ¬s.storage 1 < EvmRules.Evm.add (s.storage 0) (calldataWord call 4)) :
    EVM.Program.block o call evm7 (6, [sel], s) = some (.inr (8, [0, EvmRules.Evm.sub 0 (calldataWord call 4), s.storage 0, sel],
      { memory := s.memory, storage := s.storage, transient := s.transient, world := s.world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b6_over (o : Oracle) (call : Call) (s : State) (sel : EvmRules.Word)
    (hz : ¬BitVec.ofNat 256 call.calldata.size < 36)
    (ho : ¬EvmRules.Evm.add (s.storage 0) (calldataWord call 4) < s.storage 0)
    (hl : s.storage 1 < EvmRules.Evm.add (s.storage 0) (calldataWord call 4)) :
    EVM.Program.block o call evm7 (6, [sel], s) = some (.inr (12, [s.storage 0, calldataWord call 4, sel],
      { memory := s.memory, storage := s.storage, transient := s.transient, world := s.world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b6_ovf (o : Oracle) (call : Call) (s : State) (sel : EvmRules.Word)
    (hz : ¬BitVec.ofNat 256 call.calldata.size < 36)
    (ho : EvmRules.Evm.add (s.storage 0) (calldataWord call 4) < s.storage 0) :
    EVM.Program.block o call evm7 (6, [sel], s) = some (.inr (2, [EvmRules.Evm.add (s.storage 0) (calldataWord call 4),
      s.storage 0, calldataWord call 4, sel],
      { memory := s.memory, storage := s.storage, transient := s.transient, world := s.world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b1 (o : Oracle) (call : Call) (a : EvmRules.Word) (s : State) :
    halts (EVM.Program.block o call evm7 (1, [a], s)) = true := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b2 (o : Oracle) (call : Call) (a b c d : EvmRules.Word) (s : State) :
    halts (EVM.Program.block o call evm7 (2, [a, b, c, d], s)) = true := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b12 (o : Oracle) (call : Call) (a b c : EvmRules.Word) (s : State) :
    halts (EVM.Program.block o call evm7 (12, [a, b, c], s)) = true := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b8_loop (o : Oracle) (call : Call) (f h c w : EvmRules.Word) (s : State) (hh : h ≠ 0) :
    EVM.Program.block o call evm7 (8, [f, h, c, w], s) = some (.inr (7, [f, h, c, w], s)) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b7 (o : Oracle) (call : Call) (f h c w : EvmRules.Word) (s : State) (hc : c + 1 ≠ 0) :
    EVM.Program.block o call evm7 (7, [f, h, c, w], s) = some (.inr (8, [1, h + 1, c + 1, w], s)) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b8_exit0 (o : Oracle) (call : Call) (c w : EvmRules.Word) (s : State) :
    EVM.Program.block o call evm7 (8, [0, 0, c, w], s) = some (.inr (9, [0, c, w],
      { memory := s.memory, storage := s.storage, transient := s.transient, world := s.world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b8_exit1 (o : Oracle) (call : Call) (f c w : EvmRules.Word) (s : State) (hf : f ≠ 0) :
    EVM.Program.block o call evm7 (8, [f, 0, c, w], s) = some (.inr (9, [w],
      { memory := s.memory, storage := update s.storage 0 c, transient := s.transient, world := s.world })) := by
  sym_exec

set_option maxHeartbeats 4000000 in
theorem b9 (o : Oracle) (call : Call) (st : EVM.Stack) (s : State) :
    halts (EVM.Program.block o call evm7 (9, st, s)) = true := by
  sym_exec

/-! ## The loop -/

theorem exit_ends (o : Oracle) (call : Call) (f c w : EvmRules.Word) (s : State) :
    ∃ r, iterate (EVM.Program.block o call evm7) 2 (8, [f, 0, c, w], s) = some r := by
  by_cases hf : f = 0
  · subst hf
    rw [iterate_inr (b8_exit0 o call c w s)]
    exact ends_of_halts (b9 o call _ _) 0
  · rw [iterate_inr (b8_exit1 o call f c w s hf)]
    exact ends_of_halts (b9 o call _ _) 0

theorem neg_toNat_succ {h : BitVec 256} {m : Nat} (hm : (0 - h).toNat = m + 1) :
    (0 - (h + 1)).toNat = m := by
  bv_omega

theorem ne_zero_of_neg {h : BitVec 256} {m : Nat} (hm : (0 - h).toNat = m + 1) : h ≠ 0 := by
  bv_omega

theorem succ_ne_zero_of {c : BitVec 256} {m : Nat} (hc : c.toNat + (m + 1) < 2 ^ 256) : c + 1 ≠ 0 := by
  bv_omega

theorem toNat_succ_of {c : BitVec 256} {m : Nat} (hc : c.toNat + (m + 1) < 2 ^ 256) :
    (c + 1).toNat = c.toNat + 1 := by
  bv_omega

/-- **From the header, the loop ends**: `0 - h` iterations of two blocks each, then the exit. -/
theorem header_ends (o : Oracle) (call : Call) :
    ∀ (m : Nat) (f h c w : EvmRules.Word) (s : State), (0 - h).toNat = m → c.toNat + m < 2 ^ 256 →
      ∃ r, iterate (EVM.Program.block o call evm7) (2 * m + 2) (8, [f, h, c, w], s) = some r
  | 0, f, h, c, w, s, hm, _ => by
    have : h = 0 := by bv_omega
    subst this
    exact exit_ends o call f c w s
  | m + 1, f, h, c, w, s, hm, hc => by
    have hh := ne_zero_of_neg hm
    have hc1 := succ_ne_zero_of hc
    have e : 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 := by omega
    rw [e, iterate_inr (b8_loop o call f h c w s hh), iterate_inr (b7 o call f h c w s hc1)]
    exact header_ends o call m 1 (h + 1) (c + 1) w s (neg_toNat_succ hm)
      (by rw [toNat_succ_of hc]; omega)

/-! ## Calls -/

/-- What a call of `bump(a)` gives the machine. -/
theorem bump_facts {σ : List (Nat × Nat)} {a : Nat} (ha : a < 2 ^ 256) :
    BitVec.ofNat 256 (Verify.LoopSource.MirLink.bumpCall σ a).callvalue = 0 ∧
      (Verify.LoopSource.MirLink.bumpCall σ a).calldata.size = 36 ∧
      (calldataWord (Verify.LoopSource.MirLink.bumpCall σ a) 4).toNat = a ∧
      EvmRules.Evm.shr 224 (calldataWord (Verify.LoopSource.MirLink.bumpCall σ a) 0) = 0xb20eb4c4 := by
  have hf := callFacts 0xb20eb4c4 (by decide) [a] (by simpa using ha) σ
  refine ⟨by simp [Verify.LoopSource.MirLink.bumpCall], hf.size, ?_, hf.selector⟩
  have := hf.args 0 (by simp) (by decide)
  simpa [WExpr.eval, Nat.mod_eq_of_lt ha, Verify.LoopSource.MirLink.bumpCall, Contracts.VerifyCounter.Source.bumpSel] using this

theorem b0' (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hs : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xb20eb4c4) :
    EVM.Program.block o call evm7 (0, [], State.initial call) =
      some (.inr (6, [0xb20eb4c4], State.initial call)) :=
  b0 o call hv hs

/-- **Every bounded call ends within the fixed fuel.** -/
theorem ends (o : Oracle) {K : Nat} {call : Call}
    (hv : Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call) :
    ∃ r, iterate (EVM.Program.block o call evm7) (fixedFuel 2 2 3 K) (0, [], State.initial call) = some r := by
  obtain ⟨σ, a, haK, ha, rfl⟩ := hv
  obtain ⟨hcv, hsz, hn, hsel⟩ := bump_facts (σ := σ) ha
  generalize Verify.LoopSource.MirLink.bumpCall σ a = call at hcv hsz hn hsel ⊢
  have hz : ¬BitVec.ofNat 256 call.calldata.size < 36 := by rw [hsz]; decide
  have hF : fixedFuel 2 2 3 K = (2 * K + 2) + 1 + 1 + 1 := by unfold fixedFuel; omega
  rw [hF, iterate_inr (b0' o call hcv hsel)]
  generalize State.initial call = s
  by_cases ho : EvmRules.Evm.add (s.storage 0) (calldataWord call 4) < s.storage 0
  · rw [iterate_inr (b6_ovf o call s _ hz ho)]
    exact ends_of_halts (b2 o call _ _ _ _ _) _
  by_cases hl : s.storage 1 < EvmRules.Evm.add (s.storage 0) (calldataWord call 4)
  · rw [iterate_inr (b6_over o call s _ hz ho hl)]
    exact ends_of_halts (b12 o call _ _ _ _) _
  rw [iterate_inr (b6_pass o call s _ hz ho hl)]
  have hno : (s.storage 0).toNat + a < 2 ^ 256 := by
    simp only [EvmRules.Evm.add] at ho
    rw [← hn]
    bv_omega
  have hm : (0 - EvmRules.Evm.sub 0 (calldataWord call 4)).toNat = a := by
    simp only [EvmRules.Evm.sub]
    rw [← hn]
    bv_omega
  obtain ⟨r, hr⟩ := header_ends o call a 0 _ (s.storage 0) 0xb20eb4c4 _ hm hno
  exact ⟨r, Verify.Gas.FixedFuel.iterate_mono_le (by omega) hr⟩

/-! ## The bound and the resources -/

/-- The largest iteration bound whose fixed gas is below `2 ^ 64`. -/
def Kmax : Nat := 13042098468400

/-- **The gas bound** at iteration bound `K`: the loop checker's bound at the fixed fuel. -/
def G (K : Nat) : Nat := AssembleLoop.gasBoundL SolarTV.Milestone.X.cert (fixedFuel 2 2 3 K)

theorem G_eq (K : Nat) : G K = K * 1414400 + 3536012 := by
  rw [G, gasBoundL_fixed, fixedGas]
  have h1 : perIterGas SolarTV.Milestone.X.cert 2 = 1414400 := by decide
  have h2 : exitGas SolarTV.Milestone.X.cert 2 3 = 3536012 := by decide
  rw [h1, h2]

theorem G_lt {K : Nat} (hK : K ≤ Kmax) : G K < 2 ^ 64 := by
  rw [G_eq]; unfold Kmax at hK; omega

/-- **Counter.bump's resources** under the iteration bound `K ≤ Kmax`, with no premise. -/
theorem counter_resources {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Contracts.VerifyCounter.Source.contract? = .ok c) {K : Nat} (hK : K ≤ Kmax) :
    Shapes.Resources Verify.LoopSource.MirLink.stmtSem c SolarTV.Milestone.X.code
      (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (fun _ => G K) := by
  have src := Verify.LoopSource.Equiv.CounterExpected.counter_stage hc Shapes.oracle
    Shapes.oracle_sourceEnvOk.ask
  have stage : Stage Verify.LoopSource.MirLink.stmtSem (evmirSem Shapes.oracle) c evm7
      (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) :=
    (src.trans ((SolarTV.Milestone.X.counterLoop_mir_to_evmir Shapes.oracle).mono fun _ _ => trivial)).mono
      fun _ h => Verify.LoopSource.Equiv.CounterGas.bounded_sub h
  refine Shapes.resources_of_forward (fun call hv => ?_) stage fun call hv => ⟨G_lt hK, fun gas hg _ obs hrun => ?_⟩
  · obtain ⟨σ, a, -, ha, rfl⟩ := hv
    obtain ⟨T, hT⟩ := Contracts.VerifyCounter.Source.tree_ok
    exact ⟨_, Verify.LoopSource.Generic.runs_of_bodyRuns (by decide)
      (Contracts.VerifyCounter.Source.shape_of hc).2.2 rfl rfl
      (Verify.LoopSource.MirLink.bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) hT σ
      (Verify.LoopSource.MirLink.args_one ha)⟩
  · exact AssembleLoop.stage_of_checkL_gas SolarTV.Milestone.X.check_ok Shapes.oracle (fun _ => Shapes.oracle_ok.1)
      (fun _ => Shapes.oracle_ok.2) call _ (ends Shapes.oracle hv) hg obs hrun

/-- **Counter.bump, certified under the iteration bound**: for every \`K ≤ Kmax\`, the driver's whole
\`Shapes.Certified\` statement of the source and the exact emitted runtime \`code\` on the calls
\`BumpCallBounded K\`, with \`bump\`'s postcondition and the gas bound \`G K\`. No premise. -/
theorem counter_certified_bounded {K : Nat} (hK : K ≤ Kmax) :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      Shapes.Certified Verify.LoopSource.MirLink.stmtSem c SolarTV.Milestone.X.code
        (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (fun _ _ => True)
        Verify.LoopSource.MirLink.BumpPost (fun _ => G K) := by
  obtain ⟨c, hc, half⟩ := Verify.LoopSource.MirLink.source_half_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc
  have heq := Verify.LoopSource.Equiv.CounterClosed.counter_equiv_closed hc
  have hsub := @Verify.LoopSource.Equiv.CounterGas.bounded_sub K
  refine ⟨c, hc, ⟨Verify.LoopSource.Equiv.CounterGas.bounded_inhabited K, fun gas hg call hv => heq gas hg call (hsub hv),
    fun call hv => half.1 call (hsub hv), fun call hv => half.2 call (hsub hv), counter_resources hc hK⟩⟩

end Verify.LoopSource.Equiv.CounterResources

/-- info: 'Verify.LoopSource.Equiv.CounterResources.counter_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterResources.counter_resources

/-- info: 'Verify.LoopSource.Equiv.CounterResources.counter_certified_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterResources.counter_certified_bounded
