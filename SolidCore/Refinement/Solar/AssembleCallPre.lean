import SolidCore.Refinement.Solar.AssembleCall
import SolidCore.Refinement.Solar.AssembleCallWorld

/-!
# STATICCALL to ECRECOVER: EthLib's precompile and SolidCore's answer

The source semantics answers a static call with no value to a precompile address itself
(SourceOracleSat's failResp, by Precompile.execute?), while EthLib runs its own
precompile. This file connects the two for ECRECOVER (address 1):

* processMessage_ecrecover, meets_ecrecover: EthLib's runner of messages, on a message to
  ECRECOVER with at least 3000 gas (its price), ends with no error, with
  Precompiles.Ecrecover.compute of the call data as output, and with the substate it was sent
  with (so no log). Proved from EthLib's processMessage.
* EcrecoverAgree, the **named hypothesis**: SolidCore's Crypto.ecrecoverBytes and EthLib's
  Ecrecover.compute give the same bytes on every input. They are two independent implementations of
  secp256k1 recovery (with two Keccak implementations), checked against each other only by the test
  vectors of PrecompileParity, not proved equal here.
* ecrecover_answer: under EcrecoverAgree, SolidCore's answer to the call is the callee frame's flag
  and output, the premise a STATICCALL cut to ECRECOVER needs in place of the run's table.

AssembleCallCut.staticcall_cut uses these for a STATICCALL to address 1: there the source's answer, not
the run's table, gives the flag and return data, and the callee frame matches it.
-/

namespace SolidCore.Refinement.Solar.AssembleCallPre

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State

/-- ECRECOVER at a frame with the gas for it: the frame ends with no new error, the precompile's
output, and the substate and state it had. -/
theorem runPrecompile_ecrecover {evm after : Evm .fusaka Nat} (hg : 3000 ≤ evm.gas)
    (h : runPrecompile .fusaka 1 evm = some after) :
    after.error = evm.error ∧ after.output = Precompiles.Ecrecover.compute evm.message.data ∧
      after.substate = evm.substate ∧ after.state = evm.state := by
  unfold runPrecompile at h
  have hrun : Precompiles.run .fusaka 1 evm.message.data (GasMeter.gasLeft evm.gas) =
      some (.ok (Precompiles.Ecrecover.compute evm.message.data)) := by
    simp only [Precompiles.run, show Precompiles.isPrecompile Fork.fusaka 1 = true by decide,
      Bool.not_true, Bool.false_eq_true, ite_false, Precompiles.Ecrecover.ecrecover]
    have : ¬ GasMeter.gasLeft evm.gas < Precompiles.Ecrecover.GAS_ECRECOVER := by
      show ¬ evm.gas < 3000
      omega
    rw [ite_cond_eq_false _ _ (eq_false this)]
    rfl
  rw [hrun] at h
  simp only at h
  have hp : Precompiles.price .fusaka 1 evm.message.data = some 3000 := by
    simp [Precompiles.price, show Precompiles.isPrecompile Fork.fusaka 1 = true by decide,
      Precompiles.Ecrecover.GAS_ECRECOVER]
  rw [hp] at h
  simp only [Option.getD_some] at h
  split at h
  · rename_i heq
    have : ¬ evm.gas < 3000 := by omega
    simp only [GasMeter.charge, this, ite_false] at heq
    cases heq
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_, rfl, rfl⟩
    dsimp only

/-- ECRECOVER at a frame with the gas for it runs. -/
theorem runPrecompile_ecrecover_isSome {evm : Evm .fusaka Nat} (hg : 3000 ≤ evm.gas) :
    (runPrecompile .fusaka 1 evm).isSome = true := by
  unfold runPrecompile
  have hrun : Precompiles.run .fusaka 1 evm.message.data (GasMeter.gasLeft evm.gas) =
      some (.ok (Precompiles.Ecrecover.compute evm.message.data)) := by
    simp only [Precompiles.run, show Precompiles.isPrecompile Fork.fusaka 1 = true by decide,
      Bool.not_true, Bool.false_eq_true, ite_false, Precompiles.Ecrecover.ecrecover]
    have : ¬ GasMeter.gasLeft evm.gas < Precompiles.Ecrecover.GAS_ECRECOVER := by
      show ¬ evm.gas < 3000
      omega
    rw [ite_cond_eq_false _ _ (eq_false this)]
    rfl
  rw [hrun]
  simp only
  split <;> rfl

/-- **A message to ECRECOVER with the gas for it succeeds with EthLib's output**, keeping the
substate it was sent with. -/
theorem processMessage_ecrecover {m : Message .fusaka} {state : TransactionState} {substate : Substate}
    {ended : { evm : Evm .fusaka Nat // GasMeter.gasHeld evm.gas ≤ m.gas }}
    (hpa : precompileAddress .fusaka m = some 1) (hdis : m.disablePrecompiles = false)
    (hval : m.value = 0) (hg : 3000 ≤ m.gas)
    (h : processMessage .fusaka m state substate = .ok ended) :
    ended.val.error = none ∧ ended.val.output = Precompiles.Ecrecover.compute m.data ∧
      ended.val.substate = substate := by
  rw [processMessage] at h
  obtain ⟨ended0, hdo, rolled⟩ := EthLib.Base.map_ok_iff.mp h
  have ht : ¬ (m.shouldTransferValue = true ∧ m.value ≠ 0) := by simp [hval]
  simp only [ht, ite_false, hpa, hdis, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
    at hdo
  split at hdo
  · rename_i after heq
    rw [if_neg ht] at heq
    cases hdo
    subst rolled
    obtain ⟨e1, e2, e3, -⟩ := runPrecompile_ecrecover (by simp only [startFrame]; exact hg) heq
    simp only [startFrame] at e1 e2 e3
    have herr : after.error = none := e1
    refine ⟨?_, ?_, ?_⟩
    · unfold rollbackOnError
      split
      · rename_i hx; rw [herr] at hx; cases hx
      · exact herr
    · unfold rollbackOnError
      split
      · rename_i hx; rw [herr] at hx; cases hx
      · exact e2
    · unfold rollbackOnError
      split
      · rename_i hx; rw [herr] at hx; cases hx
      · exact e3
  · rename_i heq
    rw [if_neg ht] at heq
    have := runPrecompile_ecrecover_isSome (evm := startFrame m (startState .fusaka m state) substate
      (GasMeter.start m.gas m.reservoir)) (by simp only [startFrame]; exact hg)
    rw [heq] at this
    cases this

/-- A message the runner sends to ECRECOVER with its price in gas: a call (it has a target) whose
code address is ECRECOVER's, with precompiles enabled, no value and at least 3000 gas. -/
def EcrecoverMsg (m : Message .fusaka) : Prop :=
  m.target.isSome = true ∧ precompileAddress .fusaka m = some 1 ∧ m.disablePrecompiles = false ∧
    m.value = 0 ∧ 3000 ≤ m.gas

/-- What ECRECOVER's frame ends with: no error, EthLib's output, the substate it was sent with. -/
def EcrecoverRuns (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  EcrecoverMsg m → child.error = none ∧ child.output = Precompiles.Ecrecover.compute m.data ∧
    child.substate = caller.substate.child

/-- **The interpreter's runner of messages runs ECRECOVER** on every message with its price. -/
theorem meets_ecrecover (bound : Nat) :
    Meets (bound := bound) EcrecoverRuns (processRunner .fusaka (Meter := Nat) bound) := by
  refine ⟨fun caller m lt ended h hm => ?_, (meets_process .fusaka bound).aborts⟩
  obtain ⟨htg, hpa, hdis, hval, hg⟩ := hm
  unfold processRunner at h
  split at h
  · exact processMessage_ecrecover hpa hdis hval hg h
  · rename_i hnone
    rw [hnone] at htg
    cases htg

/-- **Named hypothesis**: SolidCore's ECRECOVER (Crypto.ecrecoverBytes on the normalized input)
and EthLib's (Precompiles.Ecrecover.compute) give the same bytes on every call data. -/
def EcrecoverAgree : Prop :=
  ∀ d : ByteArray, SolidCore.Solidity.Source.bytesToByteArray
      (SolidCore.Solidity.Shared.Crypto.ecrecoverBytes
        (SolidCore.Solidity.Shared.Precompile.normalizeBytes (SolidCore.Solidity.Source.byteArrayToBytes d))) =
    Precompiles.Ecrecover.compute d

/-- SolidCore answers a static call with no value to address 1 as ECRECOVER, with success. -/
theorem failResp_ecrecover (input : List Nat) :
    failResp .staticcall 1 0 input = (true, SolidCore.Solidity.Source.bytesToByteArray
      (SolidCore.Solidity.Shared.Crypto.ecrecoverBytes
        (SolidCore.Solidity.Shared.Precompile.normalizeBytes input))) := by
  have hk : SolidCore.Solidity.Shared.Precompile.kindOfAddress? 1 =
      some SolidCore.Solidity.Shared.Precompile.Kind.ecrecover := by decide
  simp [failResp, hk, SolidCore.Solidity.Shared.Precompile.execute?]

/-- **SolidCore's answer to a STATICCALL to ECRECOVER is the callee frame's flag and output**, under
the named hypothesis EcrecoverAgree, for every frame the runner ends a priced ECRECOVER message
with. -/
theorem ecrecover_answer (hagree : EcrecoverAgree) {caller child : Evm .fusaka Nat}
    {m : Message .fusaka} (hruns : EcrecoverRuns caller m child) (hm : EcrecoverMsg m) :
    failResp .staticcall 1 0 (SolidCore.Solidity.Source.byteArrayToBytes m.data) =
      (child.error.isNone, child.output) := by
  obtain ⟨he, ho, -⟩ := hruns hm
  rw [failResp_ecrecover, hagree, he, ho]
  rfl

/-- info: 'SolidCore.Refinement.Solar.AssembleCallPre.meets_ecrecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_ecrecover

/-- info: 'SolidCore.Refinement.Solar.AssembleCallPre.ecrecover_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ecrecover_answer

end SolidCore.Refinement.Solar.AssembleCallPre
