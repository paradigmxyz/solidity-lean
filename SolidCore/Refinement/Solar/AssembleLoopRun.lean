import SolidCore.Refinement.Solar.AssembleLoopSim
import Verify.Final

/-!
# EVM IR to bytecode, for code with loops: every gas

`run_simL` runs EthLib's interpreter as SolarTV runs the program from a block, over steps
monotone in gas, with gas for `22100 * bmax c` per block the run enters: a run of SolarTV that ends
within `fuel` blocks is EthLib's run (its first part), and a run that is still going after `fuel`
blocks has EthLib spend gas with it (its second part, through the measure `meas`: a jump lands on a
labelled block, whose JUMPDEST costs gas, and a fall goes to the next block).

`within_of_checkL`: at every gas, every result of the bytecode is SolarTV's result or a failure
that changes nothing. A run that succeeds at gas `g` is the run from the same frame with `K` more
gas, with exactly `K` more gas left at every step (`Logic.LessGas`); with `K` large, SolarTV ends
within as many blocks as the measure allows, and then EthLib's run with `K` more gas is SolarTV's.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- The measure of a run at block `b` with `g` gas, in units of the layout's length plus two:
twice the gas, and one more at a block with no label; then the blocks to the end of the layout. -/
def meas (p : Assemble.Program) (c : Cert) (g b : Nat) : Nat :=
  2 * ((p.blocks.length + 2) * g) + (if isTarget p c b then 0 else p.blocks.length + 2) +
    (p.blocks.length - b)

/-- Each block a run enters lowers the measure. -/
theorem meas_step {p : Assemble.Program} {c : Cert} {g g' b t : Nat} (hb : b < p.blocks.length)
    (ht : t ≤ p.blocks.length) (hg : g' + (if isTarget p c b then 1 else 0) ≤ g)
    (hj : t = b + 1 ∨ isTarget p c t = true) : meas p c g' t + 1 ≤ meas p c g b := by
  unfold meas
  generalize hW : p.blocks.length + 2 = W at *
  have hL : p.blocks.length + 2 = W := hW
  by_cases htb : isTarget p c b = true
  · simp only [htb, ite_true] at hg ⊢
    have h1 : W * (g' + 1) ≤ W * g := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at h1
    split <;> omega
  · simp only [htb, Bool.false_eq_true, ite_false, Nat.add_zero] at hg ⊢
    have h1 : W * g' ≤ W * g := Nat.mul_le_mul_left _ hg
    rcases hj with rfl | htt
    · split <;> omega
    · simp only [htt, ite_true]
      omega

/-- A triple over steps monotone in gas does not raise the gas. -/
theorem reaches_gas_le {a b : Evm .fusaka Nat} (h : Reaches (StepG .fusaka) a b) : b.gas ≤ a.gas :=
  Reaches.gasHeld_le (fun hs => Step.gasHeld_le hs.1) h

open SolarTV.EVM.Program in
/-- EthLib runs the code from a block's offset as SolarTV runs the program from that block, over
steps monotone in gas, with gas for `fuel` blocks of the run: to SolarTV's result when it ends within
them, and with the measure lowered by `fuel` when it does not. -/
theorem run_simL {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobL p c mx code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      b ≤ p.blocks.length → (b < p.blocks.length → c.need b ≤ S.length ∧ S.length ≤ maxH mx b) →
      SR c (c.entry b) S T →
      EntryL c code call (lowerFrom p c b (p.blocks.drop b)) (fuel * bmax c) pc s M g →
      Rel msg ss0 st ss s →
      (∀ r, SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = some r →
        SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)) ∧
      (SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = none →
        Triple (StepG .fusaka) (At code msg pc T M g st ss .empty)
          (fun z => 2 * ((p.blocks.length + 2) * z.gas) + fuel ≤ meas p c g b))
  | 0, b, S, T, s, pc, M, g, st, ss, _, _, _, _, _ => by
    refine ⟨fun r hr => by simp [SolarTV.Machine.iterate] at hr, fun _ evm hp => ⟨evm, Reaches.refl _, ?_⟩⟩
    obtain ⟨-, -, -, -, -, -, hg, -⟩ := hp
    rw [hg]
    unfold meas
    omega
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hle, hneed, hR, E, R => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
      obtain ⟨hn, hm⟩ := hneed hb
      have hbm := budget_le_bmax c b
      have hfm : (fuel + 1) * bmax c = fuel * bmax c + bmax c := Nat.succ_mul _ _
      obtain ⟨pc1, g1, hlabel, hg1, I1⟩ : ∃ pc1 g1, HoareG .fusaka (At code msg pc T M g st ss .empty)
          (At code msg pc1 T M g1 st ss .empty) ∧ g1 + (if isTarget p c b then 1 else 0) ≤ g ∧
          InvL c code call (lowerInstrs p c b p.blocks[b] ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) (budget c b - labelItems p c b)
            (fuel * bmax c) pc1 S s M g1 := by
        have E' := E
        rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at E'
        have hG := E'.gas
        rw [hfm] at hG
        by_cases ht : isTarget p c b = true
        · have hl : labelItems p c b = 1 := by simp [labelItems, ht]
          rw [hl] at hL ⊢
          simp only [ht, ite_true, List.singleton_append] at E'
          obtain ⟨next, hd, hseg⟩ := E'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          exact ⟨pc + 1, g - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
            ⟨hseg, by omega, by omega, E'.le_top, E'.mem⟩⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
            ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
      have hsim := exec_simL (o := o) G hdata hvalue hstatic hself hcaller ho b hb (fuel * bmax c)
        p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
        (List.nil_prefix) hR I1 R
      simp only [SolarTV.Machine.iterate, block, hblk]
      generalize exec o call b p.blocks[b] S s = x at hsim
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', E', R'⟩ := hsim
        have IH := run_simL G hdata hvalue hstatic hself hcaller ho fuel t S' T' s' pc' M' g' st' ss'
          htle hneedt hR' E' R'
        refine ⟨fun r hr => SpecG.seq (Triple.seq hlabel hh) (IH.1 r hr), fun hr evm hp => ?_⟩
        obtain ⟨e1, r1, he1⟩ := hlabel evm hp
        obtain ⟨mid, r2, hmid⟩ := hh e1 he1
        obtain ⟨z, r3, hz⟩ := IH.2 hr mid hmid
        refine ⟨z, (r1.trans r2).trans r3, ?_⟩
        have hgm := reaches_gas_le r2
        rw [hmid.2.2.2.2.2.2.1, he1.2.2.2.2.2.2.1] at hgm
        have := meas_step (c := c) (g := g) (g' := g') hb htle (by omega) hj
        omega
    · obtain rfl : b = p.blocks.length := by omega
      have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
      simp only [SolarTV.Machine.iterate, block, hblk, ite_true]
      refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
      simp only [Option.some.injEq] at hr
      subst hr
      have hseg := E.seg
      rw [lowerFrom_nil p c (by omega)] at hseg
      have hpc := hseg.nil_end
      exact SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h

end SolidCore.Refinement.Solar.AssembleLoop
