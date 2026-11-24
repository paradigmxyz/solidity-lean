import Verify.AssembleLoop.Variant
import Verify.Partial.CounterAny

/-!
# Counter.bump from a loop invariant and a variant, for every argument

`bumpInv call` and `bumpMu a` are a loop invariant and a variant of the final EVM IR `evm7` on
`bump(a)` (`variant`), for every `a < 2 ^ 256`: the entry (block 0) reaches the argument check
(block 6), which reverts (blocks 2 and 12) or reaches the loop header (block 8) with the stack
`[f, h, c, w]` and no overflow of `c + (0 - h)`; from the header each iteration takes two blocks
(8, 7) and lowers `(0 - h).toNat` by one, and the exit ends at block 9. The variant counts the
blocks left: `2 (0 - h).toNat + 2` at the header, `2 a + 4` at the entry. No fuel is unrolled and
no iteration bound is assumed: the block facts are `CounterResources`'s `sym_exec` runs of `evm7`.

`counter_bump_variant`: for every context `ctx.Ok`, storage `σ` and `a < 2 ^ 256`, SolidCore's
runtime code runs `bump(a)` to an observable `obs` with the allowed statuses and `BumpPost`; at
every gas, every result of the exact runtime bytes is `obs` or a failure that changes nothing
(`within_of_variantFrom`); and at every gas from `CounterCtx.G a` on, the bytes give exactly `obs`
(`forward_of_variantFrom`). The gas is an explicit premise: nothing here says the bytes end with
less, and for large `a` the premise is past any real block's gas (`G a ≥ 2 ^ 64` once `a > Kmax`).

The bounded results are corollaries: `ends_of_variant` is `CounterResources.ends`'s statement (the
fixed fuel at `K ≥ a`), and `counter_partial_any_of_variant` is `counter_partial_any`'s statement.
-/

namespace Verify.Partial.CounterVariant
open SolarTV SolarTV.Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterLoad
open Verify.LoopSource.Equiv.CounterResources (halts b0' b6_pass b6_over b6_ovf b2 b12 b8_loop b7
  b8_exit0 b8_exit1 b9 bump_facts neg_toNat_succ succ_ne_zero_of toNat_succ_of)

/-- A configuration of the EVM IR's run: block, stack, machine state. -/
abbrev Cfg := Nat × EVM.Stack × SolarTV.Machine.State

/-- **The loop invariant** of the run of `evm7` on `call`. -/
def bumpInv (call : Call) (x : Cfg) : Prop :=
  x = (0, [], SolarTV.Machine.State.initial call) ∨
  (∃ s, x = (6, [0xb20eb4c4], s)) ∨
  (∃ f h c w s, x = (8, [f, h, c, w], s) ∧ c.toNat + (0 - h).toNat < 2 ^ 256) ∨
  (∃ f h c w s, x = (7, [f, h, c, w], s) ∧ h ≠ 0 ∧ c.toNat + (0 - h).toNat < 2 ^ 256) ∨
  (∃ st s, x = (9, st, s)) ∨
  (∃ a b c d s, x = (2, [a, b, c, d], s)) ∨
  (∃ a b c s, x = (12, [a, b, c], s))

/-- **The variant**: the blocks the run of `bump(a)` has left. -/
def bumpMu (a : Nat) : Cfg → Nat
  | (0, _, _) => 2 * a + 4
  | (6, _, _) => 2 * a + 3
  | (8, [_, h, _, _], _) => 2 * (0 - h).toNat + 2
  | (7, [_, h, _, _], _) => 2 * (0 - h).toNat + 1
  | _ => 0

theorem inl_of_halts {o : Oracle} {call : Call} {x : Cfg}
    (h : halts (EVM.Program.block o call evm7 x) = true) :
    ∃ r, EVM.Program.block o call evm7 x = some (.inl r) := by
  cases hs : EVM.Program.block o call evm7 x with
  | none => simp [hs] at h
  | some v =>
    cases v with
    | inl r => exact ⟨r, rfl⟩
    | inr _ => simp [hs] at h

/-- **The invariant holds and the variant drops at every block**, for every `a < 2 ^ 256`. -/
theorem variant (o : Oracle) (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) :
    AssembleLoop.Variant (EVM.Program.block o (Verify.LoopSource.MirLink.bumpCall σ a) evm7)
      (bumpInv (Verify.LoopSource.MirLink.bumpCall σ a)) (bumpMu a) := by
  obtain ⟨hcv, hsz, hn, hsel⟩ := bump_facts (σ := σ) ha
  generalize Verify.LoopSource.MirLink.bumpCall σ a = call at hcv hsz hn hsel ⊢
  have hz : ¬BitVec.ofNat 256 call.calldata.size < 36 := by rw [hsz]; decide
  have halt : ∀ x, halts (EVM.Program.block o call evm7 x) = true →
      ∃ y, EVM.Program.block o call evm7 x = some y ∧
        ∀ x', y = .inr x' → bumpInv call x' ∧ bumpMu a x' < bumpMu a x := by
    intro x h
    obtain ⟨r, hr⟩ := inl_of_halts h
    exact ⟨_, hr, fun _ h => by cases h⟩
  rintro x (rfl | ⟨s, rfl⟩ | ⟨f, h, c, w, s, rfl, hc⟩ | ⟨f, h, c, w, s, rfl, hh, hc⟩ |
    ⟨st, s, rfl⟩ | ⟨a1, b1, c1, d1, s, rfl⟩ | ⟨a1, b1, c1, s, rfl⟩)
  · -- the entry reaches the argument check
    refine ⟨_, b0' o call hcv hsel, fun x' hx' => ?_⟩
    obtain rfl := Sum.inr.inj hx'
    exact ⟨Or.inr (Or.inl ⟨_, rfl⟩), by show 2 * a + 3 < 2 * a + 4; omega⟩
  · -- the argument check reverts or reaches the header
    by_cases ho : EvmRules.Evm.add (s.storage 0) (calldataWord call 4) < s.storage 0
    · refine ⟨_, b6_ovf o call s _ hz ho, fun x' hx' => ?_⟩
      obtain rfl := Sum.inr.inj hx'
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))))),
        by show 0 < 2 * a + 3; omega⟩
    by_cases hl : s.storage 1 < EvmRules.Evm.add (s.storage 0) (calldataWord call 4)
    · refine ⟨_, b6_over o call s _ hz ho hl, fun x' hx' => ?_⟩
      obtain rfl := Sum.inr.inj hx'
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩))))),
        by show 0 < 2 * a + 3; omega⟩
    · refine ⟨_, b6_pass o call s _ hz ho hl, fun x' hx' => ?_⟩
      obtain rfl := Sum.inr.inj hx'
      have hno : (s.storage 0).toNat + a < 2 ^ 256 := by
        simp only [EvmRules.Evm.add] at ho
        rw [← hn]
        bv_omega
      have hm : (0 - EvmRules.Evm.sub 0 (calldataWord call 4)).toNat = a := by
        simp only [EvmRules.Evm.sub]
        rw [← hn]
        bv_omega
      refine ⟨Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, by rw [hm]; exact hno⟩)), ?_⟩
      show 2 * (0 - EvmRules.Evm.sub 0 (calldataWord call 4)).toNat + 2 < 2 * a + 3
      rw [hm]
      omega
  · -- the header: another iteration, or the exit
    by_cases hh : h = 0
    · subst hh
      by_cases hf : f = 0
      · subst hf
        refine ⟨_, b8_exit0 o call c w s, fun x' hx' => ?_⟩
        obtain rfl := Sum.inr.inj hx'
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))),
          by show 0 < 2 * (0 - (0 : EvmRules.Word)).toNat + 2; omega⟩
      · refine ⟨_, b8_exit1 o call f c w s hf, fun x' hx' => ?_⟩
        obtain rfl := Sum.inr.inj hx'
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))),
          by show 0 < 2 * (0 - (0 : EvmRules.Word)).toNat + 2; omega⟩
    · refine ⟨_, b8_loop o call f h c w s hh, fun x' hx' => ?_⟩
      obtain rfl := Sum.inr.inj hx'
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h, c, w, s, rfl, hh, hc⟩))),
        by show 2 * (0 - h).toNat + 1 < 2 * (0 - h).toNat + 2; omega⟩
  · -- the body: back to the header with one iteration fewer
    obtain ⟨m, hm⟩ : ∃ m, (0 - h).toNat = m + 1 := ⟨(0 - h).toNat - 1, by bv_omega⟩
    have hc' : c.toNat + (m + 1) < 2 ^ 256 := by rw [← hm]; exact hc
    refine ⟨_, b7 o call f h c w s (succ_ne_zero_of hc'), fun x' hx' => ?_⟩
    obtain rfl := Sum.inr.inj hx'
    refine ⟨Or.inr (Or.inr (Or.inl ⟨1, h + 1, c + 1, w, s, rfl, ?_⟩)), ?_⟩
    · rw [toNat_succ_of hc', neg_toNat_succ hm]
      omega
    · show 2 * (0 - (h + 1)).toNat + 2 < 2 * (0 - h).toNat + 1
      rw [neg_toNat_succ hm, hm]
      omega
  · exact halt _ (b9 o call st s)
  · exact halt _ (b2 o call a1 b1 c1 d1 s)
  · exact halt _ (b12 o call a1 b1 c1 s)

theorem inv_entry (call : Call) : bumpInv call (AssembleCtxGas.entry call) := Or.inl rfl

/-- The variant at the entry, plus one, is the block count `CounterCtx.N a = 2 a + 5`. -/
theorem mu_entry (a : Nat) (call : Call) :
    bumpMu a (AssembleCtxGas.entry call) + 1 = Verify.LoopSource.Equiv.CounterCtx.N a := by
  show 2 * a + 4 + 1 = Verify.Gas.FixedFuel.fixedFuel 2 2 3 a
  unfold Verify.Gas.FixedFuel.fixedFuel
  omega

/-- The guarded, normalized final EVM IR runs as `evm7` at every fuel. -/
theorem run_q (o : Oracle) (call : Call) (n : Nat) :
    EVM.Program.run o evm7 call n =
      EVM.Program.run o (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
        (AssembleCtx.norm evm7)) call n :=
  (Verify.LoopSource.Equiv.CounterCtx.run_guard o call n).symm

/-- **Counter.bump for every argument, from the loop invariant and the variant**, with the gas an
explicit premise of the forward part. -/
theorem counter_bump_variant :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
          let call := Verify.LoopSource.MirLink.bumpCall σ a
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
            Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨ SolidCore.Refinement.Shapes.Inert call obs') ∧
            (∀ gas : Nat, Verify.LoopSource.Equiv.CounterCtx.G a ≤ gas →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc⟩ := contract_ok
  refine ⟨c, hc, fun ctx hctx σ a ha => ?_⟩
  dsimp only
  have hAB := Assemble.address_ne_self hctx.1 hctx.2
  set o := SolidCore.Refinement.Shapes.oracleFrom ctx.caller
  have hsrc := Verify.Partial.CounterAny.src_run_rt hc ctx.caller hctx.1 σ ha
  have hev : (evmirSem o).run (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7)) (Verify.LoopSource.MirLink.bumpCall σ a) =
        some (Verify.LoopSource.Equiv.CounterObl.T.eval
          (Verify.LoopSource.Equiv.CounterCtx.ρOf σ a ctx.caller)).obs := by
    show (evmirSem o).run (AssembleCtxGas.guard [] _) _ = _
    rw [Verify.LoopSource.Equiv.CounterCtx.guard_nil, AssembleCtx.sem_norm]
    exact Verify.LoopSource.Equiv.CounterCtx.evmir_run o σ ha ctx.caller
  have hobs : ∀ n r, EVM.Program.run o (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7)) (Verify.LoopSource.MirLink.bumpCall σ a) n =
        some r →
        SolarTV.Machine.observe (Verify.LoopSource.MirLink.bumpCall σ a) r.2 r.1 =
          (Verify.LoopSource.Equiv.CounterObl.T.eval
            (Verify.LoopSource.Equiv.CounterCtx.ρOf σ a ctx.caller)).obs := by
    intro n r h
    have he := SolidCore.Refinement.Shapes.evmir_run_of_iterate h
    rw [hev] at he
    exact (Option.some.inj he).symm
  refine ⟨_, hsrc, ?_, ?_, ?_, ?_⟩
  · intro hs
    exact ⟨eval_store_of_fail _ _ hs, Verify.LoopSource.Equiv.CounterCtx.eval_logs_of_fail _ _ hs⟩
  · exact Verify.LoopSource.Equiv.CounterCtx.tree_post_at ctx.caller
      Verify.LoopSource.Equiv.CounterObl.tree σ ha
  · intro gas obs' hrun
    obtain ⟨r, ⟨n, hr⟩, hw⟩ := AssembleCtxGas.within_of_variantFrom
      Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller hAB o (fun h => absurd h (by decide))
      (by decide) (Verify.LoopSource.MirLink.bumpCall σ a) (run_q o _)
      (InvImage.wf (bumpMu a) Nat.lt_wfRel.wf) (variant o σ ha).wf (inv_entry _)
    rcases hw gas obs' hrun with h | h
    · left
      rw [h, hobs n r hr]
    · right
      exact h
  · intro gas hg
    obtain ⟨r, hr, hrun⟩ := AssembleCtxGas.forward_of_variantFrom
      Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller hAB o (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (Verify.LoopSource.MirLink.bumpCall σ a) (run_q o _)
      (variant o σ ha) (inv_entry _) (gas := gas) (by rw [mu_entry]; exact hg)
    show Final.Target.runWithFrom ctx.caller gas Verify.LoopSource.Equiv.From.CtxGas.code _ = _
    rw [hrun, hobs _ r hr]

/-! ## The bounded results are corollaries -/

/-- **`CounterResources.ends`'s statement, from the variant**: a call of `bump(a)` with `a ≤ K` ends
within the fixed fuel at `K`. -/
theorem ends_of_variant (o : Oracle) {K : Nat} {call : Call}
    (hv : Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call) :
    ∃ r, iterate (EVM.Program.block o call evm7) (Verify.Gas.FixedFuel.fixedFuel 2 2 3 K)
      (0, [], State.initial call) = some r := by
  obtain ⟨σ, a, haK, ha, rfl⟩ := hv
  obtain ⟨r, hr⟩ := AssembleLoop.iterate_of_variant (variant o σ ha) (inv_entry _)
  refine ⟨r, AssembleLoop.iterate_le ?_ hr⟩
  rw [mu_entry]
  unfold Verify.LoopSource.Equiv.CounterCtx.N Verify.Gas.FixedFuel.fixedFuel
  omega

/-- **`counter_partial_any`'s statement, from `counter_bump_variant`.** -/
theorem counter_partial_any_of_variant :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
          let call := Verify.LoopSource.MirLink.bumpCall σ a
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
            Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨
                (gas < Verify.LoopSource.Equiv.CounterCtx.G a ∧
                  SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, Verify.LoopSource.Equiv.CounterCtx.G a ≤ gas → gas < 2 ^ 256 →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc, h⟩ := counter_bump_variant
  refine ⟨c, hc, fun ctx hctx σ a ha => ?_⟩
  have hb := h ctx hctx σ a ha
  dsimp only at hb ⊢
  obtain ⟨obs, h1, h2, h3, h4, h5⟩ := hb
  refine ⟨obs, h1, h2, h3, fun gas obs' hrun => ?_, fun gas hg _ => h5 gas hg⟩
  by_cases hg : Verify.LoopSource.Equiv.CounterCtx.G a ≤ gas
  · left
    rw [h5 gas hg] at hrun
    exact (Option.some.inj hrun).symm
  · rcases h4 gas obs' hrun with e | e
    · exact Or.inl e
    · exact Or.inr ⟨Nat.lt_of_not_le hg, e⟩

end Verify.Partial.CounterVariant

/-- info: 'Verify.Partial.CounterVariant.variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterVariant.variant

/-- info: 'Verify.Partial.CounterVariant.counter_bump_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterVariant.counter_bump_variant

/-- info: 'Verify.Partial.CounterVariant.ends_of_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterVariant.ends_of_variant

/-- info: 'Verify.Partial.CounterVariant.counter_partial_any_of_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterVariant.counter_partial_any_of_variant
