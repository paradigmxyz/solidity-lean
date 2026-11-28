import SolidCore.Refinement.Solar.AssembleRec
import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# EVM IR to bytecode at every gas, for code with recursion

`forward_of_checkF` (AssembleRec.lean) is the forward direction: from the checker's gas bound for
the run's blocks on, the bytecode ends as the final EVM IR does. Here is the backward one, at every
gas: every result the bytecode gives on a call is the result SolarTV's EVM IR semantics gives, or a
failure that leaves the storage and logs as they were (`within_of_checkF`). Below the bound a run
may run out of gas; that is such a failure (`Shapes.Inert`).

It is `AssembleLoop.within_of_checkL` with `run_simF` in place of `run_simL`: the simulation runs
for as many blocks as the gas could pay for (each block the bytecode runs costs gas, `meas`), so a
run of the EVM IR that has not ended by then contradicts the bytecode's end. The heads' bound
(`HeadsOk`) is the same hypothesis the forward theorem takes, for every call in scope.
-/

namespace SolidCore.Refinement.Solar.AssembleRec

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Final SolidCore.Refinement.Evm.Symex

/-- **EVM IR to bytecode at every gas, for code with recursion.** For every program and code the
checker with frames accepts, under every oracle whose caller and hash are EthLib's when the program
reads them and whose reads of the block and the transaction are EthLib's when the program reads them,
on every call in scope whose run keeps the heads' bound, at every gas: every result the bytecode gives
is the result SolarTV's EVM IR semantics gives, or a failure that leaves the storage and logs
nothing. -/
theorem within_of_checkF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    {F : Frames} (hc : checkF p code c mx hd F = true) (o : SolarTV.Machine.Oracle)
    (ho : c.env = true → OracleOk o) (scope : SolarTV.Call → Prop)
    (heads : ∀ call, scope call → HeadsOk o call p mx hd) (gas : Nat)
    (he : c.reads = true → EnvOk o := by intro h; exact absurd h (by decide)) :
    Within (SolarTV.evmirSem o) (ethLibWith gas) p code scope := by
  obtain ⟨G, hseg, hneed0, hf0⟩ := globF_of_checkF hc
  intro call hscope obs hrun
  change Target.runWith gas code call = some obs at hrun
  cases hs : obs.success
  · exact Or.inr ⟨rfl, Target.runWith_failure hrun hs⟩
  left
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hs
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  set msg := Final.Target.messageWith gas code call with hmsg
  have hcode : msg.code = code := rfl
  have hgas : msg.gas = gas := rfl
  have R := rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  generalize hW : p.blocks.length + 2 = W
  generalize hn : 2 * (W * gas) + W + p.blocks.length + 1 = n
  generalize hK : 22100 * (n * bmax c) + memoryGasCost c.top = K
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty (gas + K) :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; omega, by simp, memRel_initial⟩
  -- The configurations the run reaches from the call's first one, at whose heads the bound holds.
  let reach : Nat × List Word × SolarTV.Machine.State → Prop := fun x =>
    ∃ k, SolarTV.CutPoint.steps (SolarTV.EVM.Program.block o call p) k
      (0, [], SolarTV.Machine.State.initial call) = some (.inr x)
  have hclosed : ∀ x y, reach x → SolarTV.EVM.Program.block o call p x = some (.inr y) → reach y :=
    fun _ _ ⟨k, hk⟩ hs => ⟨k + 1, steps_snoc k hk hs⟩
  have hhead : ∀ x, reach x → x.1 < p.blocks.length → hd.contains x.1 = true →
      x.2.1.length ≤ maxH mx x.1 := fun x ⟨k, hk⟩ => heads call hscope k x hk
  have hsim := run_simF (msg := msg) (ss0 := ss') G rfl (by simp [msg, Final.Target.messageWith,
    Target.message]) rfl rfl rfl ho rfl rfl he reach hclosed hhead n 0 [] [] _ 0 .empty (gas + K)
    st' ss' ⟨0, rfl⟩ (Nat.zero_le _) (fun _ => ⟨by simp [hneed0], fun _ => by simp⟩) (SR.nil c _)
    (fun _ hf => absurd hf (by rw [hf0]; decide)) E0 R
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas K
  cases hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) with
  | none =>
    exfalso
    obtain ⟨z, hz, hmeas⟩ := hsim.2 hit _ hp
    obtain ⟨m, -, rfl, -⟩ := reaches_low hz K _ rfl within hrf hok
    have h1 : W * K ≤ W * (m.gas + K) := Nat.mul_le_mul_left _ (by simp)
    simp only [gas_addGas] at hmeas h1
    unfold meas at hmeas
    rw [hW] at hmeas
    have h2 : W * (gas + K) = W * gas + W * K := Nat.mul_add _ _ _
    split at hmeas <;> omega
  | some r =>
    rcases r with ⟨halt, sF⟩
    have hres : (SolarTV.evmirSem o).run p call = some (SolarTV.Machine.observe call sF halt) := by
      change (SolarTV.EVM.Program.layer.result o p call).map _ = _
      rw [SolarTV.EVM.Program.layer.result_of_ends ⟨n, hit⟩]
      rfl
    rw [hres]
    obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ :=
      SpecG.low (hsim.1 _ hit) hp within hrf hok
    have hss' : ss'.logs.toList = [] := by
      by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
      · rw [(hmove htr).2]
        simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
      · rw [(hcases htr).2]
        simp [Substate.empty]
    have hlogs := logs_of_match hL2
    have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
    have herr' : evm.error = errorOf (SolarTV.Machine.observe call sF halt) := herr
    have hout' : evm.output.toList.map (·.toNat) = (SolarTV.Machine.observe call sF halt).output := hout
    have hst' : (SolarTV.Machine.observe call sF halt).success = true →
        evm.substate.logs = ssF.logs ∧ ∀ slot,
          (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
            (SolarTV.Machine.observe call sF halt).storage slot :=
      fun h => ⟨hlogsF, hst h⟩
    have hok2 : (SolarTV.Machine.observe call sF halt).success = true →
        (SolarTV.Machine.observe call sF halt).logs = SolarTV.Machine.logs sF := by
      cases halt <;> simp [SolarTV.Machine.observe]
    clear herr hout hst hres hsim hit
    generalize SolarTV.Machine.observe call sF halt = X at *
    have hsucc : evm.error.isNone = X.success := by
      rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
    symm
    congr 1
    cases X with
    | mk success output logs storage =>
      simp only at hsucc hout' hok2 hst' ⊢
      obtain rfl : success = true := by rw [← hsucc, hok]; rfl
      rw [SolarTV.Observable.mk.injEq]
      refine ⟨hsucc, hout', ?_, funext fun slot => ?_⟩
      · simp only [hsucc, ↓reduceIte]
        rw [(hst' rfl).1, hL1', hlogs, hok2 rfl]
        rfl
      · simp only [hsucc, ↓reduceIte]
        exact (hst' rfl).2 slot

/--
info: 'SolidCore.Refinement.Solar.AssembleRec.within_of_checkF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms within_of_checkF

end SolidCore.Refinement.Solar.AssembleRec
