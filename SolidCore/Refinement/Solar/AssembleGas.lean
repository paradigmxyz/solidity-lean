import SolidCore.Refinement.Solar.AssembleSim
import Verify.Final

/-!
# EVM IR to bytecode from a gas bound on

`stage_of_check_env` is the forward stage of the assembly checker at the gas of
`Target.message`: every observable SolarTV's EVM IR gives, EthLib gives for the bytecode. Its
proof needs only that the message holds the gas the checker's invariant asks for, 22100 per item
of the lowered program plus the memory up to the certificate's top (`gasBound`, at most
10,000,000 by the check). So the same proof gives the stage at every gas from `gasBound` on
(`stage_of_check_gas`): from that gas the bytecode does not run out of gas, it shows exactly the
EVM IR's result, a revert with its data included. This is the resources half of a certificate:
a proved gas bound, a constant of the checked program, not a premise of success.

The bound is coarse (22100 gas, an SSTORE's worst case, for every item) and covers only code the
straight-line checker accepts: no loops, GAS or calls.
-/

namespace SolidCore.Refinement.Solar.Assemble

open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex

/-- The gas a run of a checked program needs at most. -/
def gasBound (p : Program) (c : Cert) : Nat := 22100 * cost p c 0 + memoryGasCost c.top

/-- `run_of_rel` with the message of `gas` gas. -/
theorem run_of_rel_with (code : ByteArray) (call : SolarTV.Call) (s : SolarTV.Machine.State)
    (halt : SolarTV.Machine.Halt) (gas : Nat)
    (h : ∀ st, Rel (Final.Target.messageWith gas code call) Substate.empty st Substate.empty
        (SolarTV.Machine.State.initial call) →
      Spec .fusaka (At code (Final.Target.messageWith gas code call) 0 [] .empty gas st
        Substate.empty .empty) (PostL call (Target.address selfAddress) Substate.empty s halt)) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call s halt) := by
  have key : ∃ evm, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (Target.preState code call) Substate.empty = .ok evm ∧
      MsgOut (SolarTV.Machine.observe call s halt) (Target.address selfAddress) Substate.empty
        s.world evm.1 := by
    by_cases hv : (Final.Target.messageWith gas code call).value = 0
    · exact processMessage_postL _ rfl hv (precompileAddress_message code call) _ _ _ _ _
        (h _ ⟨(rel_initial code call).storage, (rel_initial code call).account,
          (rel_initial code call).logs⟩)
    · obtain ⟨st', hmove⟩ := moveEther_preState_any code call
      have hn : ((Target.preState code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
        rw [getAccount_preState_self]; simp
      have hAB : Target.address selfAddress ≠ Target.address callerAddress := by decide
      have R0 := rel_initial code call
      have R : Rel (Final.Target.messageWith gas code call) Substate.empty st' Substate.empty
          (SolarTV.Machine.State.initial call) :=
        ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
          (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, R0.logs⟩
      exact processMessage_postL_move _ rfl rfl hv (precompileAddress_message code call) _ _ _ _
        st' _ hmove (h st' R)
  obtain ⟨evm, hr, ssF, ⟨L, hL1, hL2⟩, herr, hout, hst⟩ := key
  have hlogs := logs_of_match hL2
  have hL1' : ssF.logs.toList = L := by simpa [Substate.empty] using hL1
  have hfail : (SolarTV.Machine.observe call s halt).success = false →
      (SolarTV.Machine.observe call s halt).logs = [] ∧
      (SolarTV.Machine.observe call s halt).storage = slotValue call.storage := by
    cases halt <;> simp [SolarTV.Machine.observe]
  have hok : (SolarTV.Machine.observe call s halt).success = true →
      (SolarTV.Machine.observe call s halt).logs = SolarTV.Machine.logs s := by
    cases halt <;> simp [SolarTV.Machine.observe]
  simp only [Final.Target.runWith, Final.Target.runMsg, hr]
  generalize SolarTV.Machine.observe call s halt = X at *
  have hsucc : evm.1.error.isNone = X.success := by
    rw [herr]; cases hX : X.success <;> simp [errorOf, hX]
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout hfail hok hst ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc, hout, ?_, ?_⟩
    · rw [hsucc]
      cases hs : success
      · simp [(hfail hs).1]
      · simp only [ite_true]
        rw [(hst hs).1, hL1', hlogs, hok hs]
        rfl
    · funext slot
      rw [hsucc]
      cases hs : success
      · simp [(hfail hs).2]
      · simp only [ite_true]
        exact (hst hs).2 slot

/-- **EVM IR to bytecode from the gas bound on.** For every program and code the checker accepts,
under every oracle whose caller and hash are EthLib's when the program reads them, at every gas
from `gasBound` on: every observable SolarTV's EVM IR gives, EthLib gives for the bytecode with
that gas. -/
theorem stage_of_check_gas {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true)
    (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o) (scope : SolarTV.Call → Prop)
    {gas : Nat} (hg : gasBound p c ≤ gas) :
    SolarTV.Stage (SolarTV.evmirSem o) (Final.ethLibWith gas) p
      (show (Final.ethLibWith gas).Prog from code) scope := by
  obtain ⟨G, hseg, hneed0, hlen, -⟩ := glob_of_check hc
  intro call _ obs hrun
  change (SolarTV.EVM.Program.layer.result o p call).map _ = _ at hrun
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hrun
  obtain ⟨n, hn⟩ := SolarTV.EVM.Program.layer.ends_of_result hr
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have I0 : Inv c code call (lowerFrom p c 0 (p.blocks.drop 0)) (cost p c 0) 0 []
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by simpa using hlen,
      by rw [hm0]; unfold gasBound at hg; omega, by simp, memRel_initial⟩
  exact run_of_rel_with code call r.2 r.1 gas fun st R =>
    run_sim (msg := Final.Target.messageWith gas code call) (ss0 := Substate.empty) G rfl
      (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho n 0 [] [] _ 0 .empty
      gas st Substate.empty r (Nat.zero_le _) (by simp [hneed0]) (SR.nil c _) I0 R hn

/-- The bound is at most 10,000,000, the gas of `Target.message`, for every checked program. -/
theorem gasBound_le {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true) :
    gasBound p c ≤ 10000000 :=
  (glob_of_check hc).2.2.2.2

/--
info: 'SolidCore.Refinement.Solar.Assemble.stage_of_check_gas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_check_gas

end SolidCore.Refinement.Solar.Assemble
