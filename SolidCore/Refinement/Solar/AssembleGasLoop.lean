import SolidCore.Refinement.Solar.AssembleLoopRun
import SolidCore.Refinement.Solar.AssembleGas

/-!
# EVM IR to bytecode from a gas bound on, for code with loops

`within_of_checkL` is the backward direction at every gas. Here is the forward one: when SolarTV's
EVM IR ends within `n` blocks, then at every gas from `22100 * (n * bmax c) + memoryGasCost c.top`
on, the bytecode shows exactly its result, reverts included (`forward_of_checkL`). The block count
`n` is the run's; a ranking of the program's loops bounds it by a function of the call, which
turns this into a gas bound `G call` (`Shapes.Resources`).
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- The gas a run of a program the loop checker accepts needs when it ends within `n` blocks. -/
def gasBoundL (c : Cert) (n : Nat) : Nat := 22100 * (n * bmax c) + memoryGasCost c.top

/-- **The forward assembly theorem for code with loops.** -/
theorem forward_of_checkL {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine run_of_rel_with code call r.2 r.1 gas fun st R => ?_
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; unfold gasBoundL at hg; omega, by simp,
      memRel_initial⟩
  have hsim := run_simL (msg := Final.Target.messageWith gas code call) (ss0 := Substate.empty) G
    rfl (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho rfl rfl he n 0 [] [] _ 0
    .empty gas st Substate.empty (Nat.zero_le _) (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _)
    E0 R
  exact SpecG.toSpec (hsim.1 r hit)

/-- The forward stage at one gas, for the calls whose run ends within `n call` blocks. -/
theorem stage_of_checkL_gas {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (ends : ∃ r, SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) (obs : SolarTV.Observable)
    (hrun : (SolarTV.evmirSem o).run p call = some obs) :
    Final.Target.runWith gas code call = some obs := by
  obtain ⟨r, hit⟩ := ends
  have hres : (SolarTV.evmirSem o).run p call = some (SolarTV.Machine.observe call r.2 r.1) := by
    change (SolarTV.EVM.Program.layer.result o p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨n, hit⟩]
    rfl
  rw [hres] at hrun
  cases hrun
  exact forward_of_checkL hc o ho he call n r hit hg

/--
info: 'SolidCore.Refinement.Solar.AssembleLoop.stage_of_checkL_gas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_checkL_gas

end SolidCore.Refinement.Solar.AssembleLoop
