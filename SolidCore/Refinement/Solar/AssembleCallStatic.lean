import EthLib.Execution.Proofs.Evm.Call.StepRules
import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# EIP-214 from EthLib: a static message that succeeds ends with no log

EthLib proves that a static message keeps the state (processMessage_sameOutside_static), but its
static steps (EthLib.Execution.Evm.StaticStep) say nothing of the logs of the substate. This file
proves the logs half, by the same classification of instructions and the same induction on the
gas of messages (EthLib.Execution.Evm.processMessage_rel):

* LStep: a step that keeps the message and the logs. Every instruction of a static frame that
  gives the next frame is one (lStep_instruction_of_isStatic): LOG fails there, SSTORE, TSTORE
  and SELFDESTRUCT halt or fail, every other instruction keeps the substate's logs.
* A call from a static frame sends a static message, and the caller resumes with its own logs
  when the child ends with no log (lResult_step).
* processMessage_logs_static: before Glamsterdam (no transfer logs, EIP-7708), a static message
  that ends with no error ends with the logs it started with, however deep its calls. A message
  starts from Substate.child, which has no log, so the frame ends with no log.
* meets_staticNoLogs: the interpreter's runner of messages meets that, the hypothesis that
  AssembleCallCut.StaticNoLogs names.
-/

namespace EthLib.Execution.Evm.StaticLogs

open EthLib
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type}

/-- A step that keeps the message and the logs of the substate. -/
structure LStep (before after : Evm fork Meter) : Prop where
  message : after.message = before.message
  logs : after.substate.logs = before.substate.logs

namespace LStep

theorem refl (evm : Evm fork Meter) : LStep evm evm := ⟨rfl, rfl⟩

theorem trans {a b c : Evm fork Meter} (hab : LStep a b) (hbc : LStep b c) : LStep a c :=
  ⟨hbc.message.trans hab.message, hbc.logs.trans hab.logs⟩

theorem of_sameContext {a b : Evm fork Meter} (h : SameContext a b) : LStep a b :=
  ⟨h.message, by rw [h.substate]⟩

theorem withMemory (evm : Evm fork Meter) (memory : ByteArray) : LStep evm { evm with memory } :=
  ⟨rfl, rfl⟩

theorem advance {a b : Evm fork Meter} (h : LStep a b) (n : Nat := 1) :
    LStep a (Evm.advance b n) :=
  ⟨h.message, h.logs⟩

end LStep

theorem lStep_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    LStep evm (recordAccountRead evm address) := ⟨rfl, rfl⟩

theorem lStep_recordStorageRead (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    LStep evm (recordStorageRead evm address key) := ⟨rfl, rfl⟩

variable [GasMeter Meter]

omit [GasMeter Meter] in
theorem lStep_accessAddress (evm : Evm fork Meter) (address : Address) :
    LStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  exact ⟨by rw [h], by rw [h]⟩

omit [GasMeter Meter] in
theorem lStep_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    LStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  exact ⟨by rw [h], by rw [h]⟩

theorem lStep_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    LStep evm (exceptionalHalt evm e) := ⟨rfl, rfl⟩

/-! ## The instructions that give the next frame (after EthLib's Instructions/Static.lean) -/

/-- BALANCE is a static step. -/
theorem lStep_balanceStep {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    LStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : LStep e1 e2 := by
    have := lStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((LStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (LStep.of_sameContext (chargeGas_sameContext h3))).trans
    (lStep_recordAccountRead _ _)).trans
    (LStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODESIZE is a static step. -/
theorem lStep_extcodesizeStep {evm after : Evm fork Meter}
    (h : extcodesizeStep evm = .ok after) : LStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : LStep e1 e2 := by
    have := lStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((LStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (LStep.of_sameContext (chargeGas_sameContext h3))).trans
    (lStep_recordAccountRead _ _)).trans
    (LStep.of_sameContext (pushWord_sameContext h5)) |>.advance

/-- EXTCODEHASH is a static step. -/
theorem lStep_extcodehashStep {evm after : Evm fork Meter}
    (h : extcodehashStep evm = .ok after) : LStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : LStep e1 e2 := by
    have := lStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((LStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (LStep.of_sameContext (chargeGas_sameContext h3))).trans
    (lStep_recordAccountRead _ _)).trans
    (LStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODECOPY is a static step. -/
theorem lStep_extcodecopyStep {evm after : Evm fork Meter}
    (h : extcodecopyStep evm = .ok after) : LStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : LStep e4 e5 := by
    have := lStep_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((LStep.of_sameContext (popWord_sameContext h1)).trans
    (LStep.of_sameContext (popWord_sameContext h2))).trans
    (LStep.of_sameContext (popWord_sameContext h3))).trans
    (LStep.of_sameContext (popWord_sameContext h4))).trans ha).trans
    (LStep.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
    (lStep_recordAccountRead _ _)).trans (LStep.withMemory _ _) |>.advance

/-- Each instruction that reads another account is a static step. -/
theorem lStep_accountStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact lStep_balanceStep h
  case extcodesize => subst hstep; exact lStep_extcodesizeStep h
  case extcodecopy => subst hstep; exact lStep_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (lStep_recordAccountRead _ _).trans
        (LStep.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact lStep_extcodehashStep h
    · cases hstep

/-- SLOAD is a static step. -/
theorem lStep_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    LStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : LStep e1 e2 := by
    have := lStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((LStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (LStep.of_sameContext (chargeGas_sameContext h3))).trans
    (lStep_recordStorageRead _ _ _)).trans
    (LStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- SSTORE in a static frame is a static step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem lStep_sstoreStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : sstoreStep evm = .ok after) :
    LStep evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (LStep.of_sameContext (popWord_sameContext h1)).trans
    (LStep.of_sameContext (popWord_sameContext h2))
  have m2 : e2.message = evm.message :=
    (popWord_sameContext h2).message.trans (popWord_sameContext h1).message
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
      rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      rw [hpair] at hacc
      simp only [hpair] at h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.message = evm.message := by
        obtain ⟨_, -, h5⟩ := Base.bind_ok_iff.mp h5
        cases h5
        rw [(chargeGas_sameContext h4).message]
        cases hacc
        exact m2
      simp [m5, static, throw, throwThe, MonadExceptOf.throw] at h
    · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      have ha : LStep e2 e3 := by
        have := lStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
        rwa [hpair] at this
      exact ((c2.trans ha).trans (lStep_recordStorageRead _ _ _)).trans
        (lStep_exceptionalHalt _ _)

/-- Each instruction that uses storage is a static step in a static frame. -/
theorem lStep_storageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact lStep_sloadStep h
  case sstore => subst hstep; exact lStep_sstoreStep_of_isStatic static h

/-- SELFDESTRUCT in a static frame is a static step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem lStep_selfdestructStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : selfdestructStep fork evm = .ok after) :
    LStep evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : LStep e1 e2 := by
    have := lStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c := ((LStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (lStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeStateGas_sameContext h4).message, (chargeGas_sameContext h3).message]
      exact c.message
    unfold finishSelfdestruct at h
    simp [m4, static] at h
  · exact c.trans (lStep_exceptionalHalt _ _)

/-- Each instruction of transient storage is a static step in a static frame. -/
theorem lStep_transientStorageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload => exact LStep.of_sameContext (tloadStep_sameContext h)
  case tstore => exact absurd h (tstoreStep_ne_ok_of_isStatic static)

/-- RETURN and REVERT are static steps. -/
theorem lStep_returnOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact LStep.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep; exact LStep.of_sameContext (revertStep_sameContext h)
    · cases hstep

/-- The instruction of SELFDESTRUCT is a static step in a static frame. -/
theorem lStep_selfdestructOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact lStep_selfdestructStep_of_isStatic static h

/-- The instructions of LOG are static steps in a static frame, as none completes. -/
theorem lStep_logOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : LStep evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact absurd h (logStep_ne_ok_of_isStatic static)

/-- Each instruction that gives the next frame is a static step in a static frame. -/
theorem lStep_instruction_of_isStatic {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (static : evm.message.isStatic = true)
    (h : run evm = .ok after) : LStep evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact LStep.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact LStep.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact LStep.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact LStep.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact lStep_storageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hrun
  · exact lStep_transientStorageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hf
  · exact lStep_logOpStep_of_isStatic hf static h
  · exact lStep_selfdestructOpStep_of_isStatic hf static h

omit [GasMeter Meter] in
/-- The pops of the operands of a call are a static step.

A call that sends no value pops none. -/
theorem lStep_popCallOperands {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    LStep evm after ∧ (kind.sendsValue = false → call.value = 0) := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : LStep e2 e3 ∧ (kind.sendsValue = false → v = 0) := by
    unfold popCallValue at h3
    split at h3
    · exact ⟨LStep.of_sameContext (popWord_sameContext h3), fun h => by simp_all⟩
    · cases h3
      exact ⟨LStep.refl _, fun _ => rfl⟩
  refine ⟨?_, p3.2⟩
  exact (((((((LStep.of_sameContext (popWord_sameContext h1)).trans
    (LStep.of_sameContext (popWord_sameContext h2))).trans p3.1).trans
    (LStep.of_sameContext (popWord_sameContext h4))).trans
    (LStep.of_sameContext (popWord_sameContext h5))).trans
    (LStep.of_sameContext (popWord_sameContext h6))).trans
    (LStep.of_sameContext (popWord_sameContext h7)))

/-- The access to a delegate is a static step. -/
theorem lStep_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    LStep evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (lStep_accessAddress _ _).trans (lStep_recordAccountRead _ _)
  · cases h
    exact LStep.refl _

/-- The payment of a call is a static step. -/
theorem lStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    LStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((LStep.of_sameContext (chargeGas_sameContext h1)).trans
      (LStep.of_sameContext (chargeStateGas_sameContext h2))).trans
      (LStep.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact LStep.of_sameContext (chargeGas_sameContext h1)

/-- A call that runs no message is a static step. -/
theorem lStep_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : LStep evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨rfl, rfl⟩


/-! ## The steps that send a message -/

/-- What a step of a static frame gives: a step that keeps the message and the logs, or a static
message from such a step, after which the caller keeps its logs when the child ends with none. -/
def LChild (evm caller : Evm fork Meter) (message : Message fork)
    (resume : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  LStep evm caller ∧ message.isStatic = true ∧
    ∀ child after, resume child = .ok after → (child.error = none → child.substate.logs = #[]) →
      LStep evm after

def LResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => LStep evm after
  | .child caller message resume => LChild evm caller message resume

omit [GasMeter Meter] in
theorem LResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : LStep evm evm') (r : LResult evm' result) : LResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, m, k⟩ := r
    exact ⟨h.trans c, m, fun child after hres hl => h.trans (k child after hres hl)⟩

/-- A caller that resumes after a child that ends with no log keeps its message and logs. -/
theorem lStep_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (hl : child.error = none → child.substate.logs = #[]) : LStep caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  refine ⟨?_, ?_⟩
  · show e.message = caller.message
    rw [hp.message]; split <;> simp [message_incorporateChild, refillStateGas]
  · show e.substate.logs = caller.substate.logs
    rw [hp.substate]
    by_cases he : child.error = none
    · simp [incorporateChild, he, hl he]
    · have hn : child.error.isNone = false := by
        cases hc : child.error with
        | none => exact absurd hc he
        | some _ => rfl
      simp [incorporateChild, hn, refillStateGas]

theorem lResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (hmsg : message.isStatic = true)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    LResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact (⟨rfl, rfl⟩ : LStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans
        (lStep_skipCall hs)
  · cases h
    refine ⟨⟨rfl, rfl⟩, hmsg, ?_⟩
    intro child after hres hl
    have pre : LStep evm { evm with returnData := .empty } := ⟨rfl, rfl⟩
    exact pre.trans (lStep_resumeCall hres hl)

theorem lResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    LResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : LStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨rfl, rfl⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have refill : LStep (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget)
          (refillStateGas (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) := ⟨rfl, rfl⟩
      exact (pre.trans refill).trans (lStep_skipCall hs)
  · refine LResult.lift pre (lResult_genericCall ?_ h)
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inr static

theorem lResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (static : evm.message.isStatic = true)
    (h : callStep kind evm = .ok result) : LResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := (lStep_popCallOperands h1).1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : LStep e1 e2 := by
    have := lStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : LStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (lStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : LStep evm e4 := s3.trans (lStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have s5 : LStep evm e5 := s4.trans (lStep_payCall h5)
      exact LResult.lift s5 (lResult_finishCall (by rw [s5.message]; exact static) h)
    · exact s4.trans (lStep_exceptionalHalt _ _)
  · exact s3.trans (lStep_exceptionalHalt _ _)

theorem lResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (static : evm.message.isStatic = true) (h : run evm = .ok result) : LResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact lResult_callStep static h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact lResult_callStep static h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact absurd h (createStep_ne_ok_of_isStatic static))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact absurd h (createStep_ne_ok_of_isStatic static)
         · cases hrun)

/-- **A step of a static frame keeps the message and the logs**, or sends a static message
after which the caller keeps its logs when the child ends with none. -/
theorem lResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true) (h : step fork evm = .ok result) :
    LResult evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact lStep_instruction_of_isStatic hop static hr
      · split at h
        · rename_i hcall
          exact lResult_messageInstruction hcall static h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact LStep.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## Messages -/

theorem lStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : LStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact lStep_exceptionalHalt _ _
  · split at h
    · cases h
      exact lStep_exceptionalHalt _ _
    · cases h
      exact ⟨rfl, rfl⟩

/-- The deposit of code keeps the substate, and leaves no error only after a frame with none. -/
theorem depositCode_facts {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.substate = evm.substate ∧ (after.error = none → evm.error = none) := by
  unfold depositCode at h
  split at h
  · cases h
    exact ⟨rfl, id⟩
  · dsimp only at h
    split at h
    · cases h
      exact ⟨rfl, fun h' => by simp at h'⟩
    · split at h
      · cases h
        exact ⟨rfl, fun h' => by simp at h'⟩
      · split at h
        · split at h <;> cases h <;> first | exact ⟨rfl, id⟩ | exact ⟨rfl, fun h' => by simp at h'⟩
        · split at h
          · cases h
            exact ⟨rfl, fun h' => by simp at h'⟩
          · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
            cases h
            exact ⟨rfl, id⟩

/-- What a static message that ends with no error keeps: its starting logs. -/
def LogsKept (message : Message fork) (_state : TransactionState) (substate : Substate)
    (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  message.isStatic = true → ended.error = none → ended.substate.logs = substate.logs

/-- **Before Glamsterdam, every static call and creation that ends with no error ends with the
logs it started from**, however deep its calls: the induction on the gas of messages. -/
theorem logsKept_process [LawfulGasMeter Meter] (hfork : fork < .glamsterdam) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        LogsKept message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        LogsKept message state substate meter ended.val) := by
  refine processMessage_rel (R := fun a b => a.message.isStatic = true → LStep a b)
    (Inv := fun evm => evm.message.isStatic = true) (M := LogsKept)
    (fun evm _ => LStep.refl evm)
    (fun {a b c} hab hbc ha => (hab ha).trans (hbc (by rw [(hab ha).message]; exact ha)))
    (fun {a b} ha r => by rw [(r ha).message]; exact ha)
    (fun evm e _ _ => lStep_exceptionalHalt evm e)
    ?steps (fun evm _ _ => ⟨rfl, rfl⟩)
    (fun {address evm after} h _ _ => lStep_runPrecompile h)
    ?call ?create n
  case steps =>
    intro evm result hinv hstep
    have r := lResult_step hinv hstep
    cases result with
    | next after => exact fun _ => r
    | child caller message resume =>
      obtain ⟨c, hm, k⟩ := r
      refine ⟨fun _ => c, fun child after hres hc _ => k child after hres ?_⟩
      intro he
      have := hc hm he
      rw [this]
      rfl
  case call =>
    intro message state entry substate entrySubstate meter ended hE hR hs he
    have hst : (startFrame message entry entrySubstate meter).message.isStatic = true := hs
    have l := hR hst hst
    have hsub : (rollbackOnError state ended).substate = ended.substate := by
      unfold rollbackOnError; split <;> rfl
    rw [hsub, l.logs]
    show entrySubstate.logs = substate.logs
    rcases hE with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · rfl
    · have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hfork
      simp only [pushTransferLog, this, false_and, ↓reduceIte]
  case create =>
    intro message state prepared substate meter evm after _ hM hd hs he
    obtain ⟨hsub, herr⟩ := depositCode_facts hd
    rw [hsub]
    exact hM hs (herr he)

/-- **EIP-214 for EthLib's runner of messages**: before Glamsterdam, a static message that the
runner ends with no error ends with no log. -/
theorem meets_staticNoLogs [LawfulGasMeter Meter] (hfork : fork < .glamsterdam) (bound : Nat) :
    Logic.Meets (bound := bound)
      (fun _ m child => m.isStatic = true → child.error = none → child.substate.logs.toList = [])
      (Logic.processRunner fork (Meter := Meter) bound) := by
  refine ⟨fun caller m lt ended h hs he => ?_, (Logic.meets_process fork bound).aborts⟩
  unfold Logic.processRunner at h
  split at h
  · have := (logsKept_process hfork m.gas).1 m _ _ _ _ rfl ended h hs he
    rw [this]
    rfl
  · have := (logsKept_process hfork m.gas).2 m _ _ _ _ rfl ended h hs he
    rw [this]
    rfl

/-- info: 'EthLib.Execution.Evm.StaticLogs.meets_staticNoLogs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_staticNoLogs

end EthLib.Execution.Evm.StaticLogs
