import EthLib.Execution.Proofs.Evm.Call.StepRules
import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# No step throws a revert, and only REVERT ends a frame with it

EthLib's steps that are monotone in gas (`EthLib.Execution.Evm.Logic.GasMono`) count a revert as a
failure, so a run with less gas that reverts says nothing of the run with more gas. This file
classifies every step of the one-counter meter (`Nat`) by the error it carries:

* `Good p evm r`: the result `r` throws no revert, and each frame it gives (through `p`) has
  the revert error only when `evm` had it (`KR`). It composes through `bind`, so each
  instruction is checked from its parts (`popWord`, `pushWord`, the charges, `keepReads`, the
  reads of the state), by the tactic `good`.
* `good_instruction`: every instruction of the ten groups that give the next frame throws no
  revert, and every one but REVERT keeps it out of its frame. `good_message`: the same for the
  calls and the creations, whose result is the next frame or the caller of a message.
* `step_good`: a step throws no revert, and a step that gives a frame with the revert error
  started from one, or ran REVERT.
-/

namespace EthLib.Execution.Evm.RevertErr

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork}

/-- The frame `b` has the revert error only when `a` had it. -/
def KR (a b : Evm fork Nat) : Prop := b.error = some .revert → a.error = some .revert

theorem KR.refl (a : Evm fork Nat) : KR a a := id

theorem KR.trans {a b c : Evm fork Nat} (h1 : KR a b) (h2 : KR b c) : KR a c := fun h => h1 (h2 h)

theorem KR.of_eq {a b : Evm fork Nat} (h : b.error = a.error) : KR a b := fun h' => h ▸ h'

/-- A result that throws no revert, whose frames carry the revert error only if `evm` did. -/
def Good {α : Type} (p : α → Evm fork Nat) (evm : Evm fork Nat) (r : Except EvmError α) : Prop :=
  (∀ e, r = .error e → e ≠ .revert) ∧ ∀ a, r = .ok a → KR evm (p a)

theorem Good.bind {α β : Type} {p : α → Evm fork Nat} {q : β → Evm fork Nat} {evm : Evm fork Nat}
    {x : Except EvmError α} {f : α → Except EvmError β} (hx : Good p evm x)
    (hf : ∀ a, Good q (p a) (f a)) : Good q evm (x >>= f) := by
  refine ⟨fun e h => ?_, fun b h => ?_⟩
  · cases hxa : x with
    | error e' => rw [hxa] at h; cases h; exact hx.1 _ hxa
    | ok a => rw [hxa] at h; exact (hf a).1 e h
  · cases hxa : x with
    | error e' => rw [hxa] at h; cases h
    | ok a => rw [hxa] at h; exact (hx.2 a hxa).trans ((hf a).2 b h)

/-- A bind whose first part gives no frame: the rest runs from the same frame. -/
theorem Good.bindc {α β : Type} {q : β → Evm fork Nat} {evm : Evm fork Nat}
    {x : Except EvmError α} {f : α → Except EvmError β} (hx : Good (fun _ => evm) evm x)
    (hf : ∀ a, Good q evm (f a)) : Good q evm (x >>= f) :=
  Good.bind hx hf

theorem Good.pure_kr {α : Type} {p : α → Evm fork Nat} {evm : Evm fork Nat} {a : α}
    (h : KR evm (p a)) : Good p evm (pure a : Except EvmError α) :=
  ⟨(fun _ h' => by cases h'), (fun _ h' => by cases h'; exact h)⟩

theorem Good.ok_kr {α : Type} {p : α → Evm fork Nat} {evm : Evm fork Nat} {a : α}
    (h : KR evm (p a)) : Good p evm (.ok a : Except EvmError α) := Good.pure_kr h

theorem Good.err {α : Type} {p : α → Evm fork Nat} {evm : Evm fork Nat} {e : EvmError}
    (h : e ≠ .revert) : Good p evm (.error e : Except EvmError α) :=
  ⟨(fun _ h' => by cases h'; exact h), (fun _ h' => by cases h')⟩

theorem Good.throw_ {α : Type} {p : α → Evm fork Nat} {evm : Evm fork Nat} {e : EvmError}
    (h : e ≠ .revert) : Good p evm (throw e : Except EvmError α) := Good.err h

/-- The frame of a step's result: the next frame, or the caller of a message. -/
def frameOf : StepResult fork Nat → Evm fork Nat
  | .next b => b
  | .child c _ _ => c

theorem Good.map_next {evm : Evm fork Nat} {x : Except EvmError (Evm fork Nat)}
    (h : Good id evm x) : Good frameOf evm (StepResult.next <$> x) := by
  refine ⟨fun e h' => ?_, fun b h' => ?_⟩
  · cases hx : x with
    | error e' => rw [hx] at h'; cases h'; exact h.1 _ hx
    | ok a => rw [hx] at h'; cases h'
  · cases hx : x with
    | error e' => rw [hx] at h'; cases h'
    | ok a => rw [hx] at h'; cases h'; exact h.2 a hx

theorem Good.mapError {α ε : Type} {evm : Evm fork Nat} (f : ε → EvmError)
    (hf : ∀ s, f s ≠ .revert) (x : Except ε α) : Good (fun _ => evm) evm (x.mapError f) := by
  cases x with
  | error s => exact Good.err (hf s)
  | ok a => exact Good.ok_kr (KR.refl _)

@[simp] theorem error_accessAddress (e : Evm fork Nat) (a : Address) :
    (accessAddress e a).2.error = e.error := by
  unfold accessAddress; split <;> rfl

@[simp] theorem error_accessStorageKey (e : Evm fork Nat) (a : Address) (k : EthLib.Base.Bytes32) :
    (accessStorageKey e a k).2.error = e.error := by
  unfold accessStorageKey; split <;> rfl

/-! ## The parts of the instructions -/

theorem good_popWord {evm e : Evm fork Nat} (h : KR evm e) : Good Prod.snd evm (popWord e) := by
  unfold popWord
  refine Good.bindc ?_ fun a => ?_
  · unfold Stack.pop
    split
    · exact Good.err (by decide)
    · exact Good.ok_kr (KR.refl _)
  · rcases a with ⟨x, s⟩
    exact Good.pure_kr h

theorem good_pushWord {evm e : Evm fork Nat} (h : KR evm e) (x : U256) :
    Good id evm (pushWord e x) := by
  unfold pushWord
  refine Good.bindc ?_ fun a => Good.pure_kr h
  unfold Stack.push
  split
  · exact Good.err (by decide)
  · exact Good.ok_kr (KR.refl _)

theorem good_chargeGas {evm e : Evm fork Nat} (h : KR evm e) (c : Nat) :
    Good id evm (chargeGas e c) := by
  unfold chargeGas
  refine Good.bindc ?_ fun a => Good.pure_kr h
  simp only [GasMeter.charge]
  split
  · exact Good.err (by decide)
  · exact Good.ok_kr (KR.refl _)

theorem good_chargeStateGas {evm e : Evm fork Nat} (h : KR evm e) (c : Nat) :
    Good id evm (chargeStateGas e c) := by
  unfold chargeStateGas
  refine Good.bindc ?_ fun a => Good.pure_kr h
  simp only [GasMeter.chargeState]
  split
  · exact Good.err (by decide)
  · exact Good.ok_kr (KR.refl _)

theorem good_chargeGasAndMemory {evm e : Evm fork Nat} (h : KR evm e) (c : Nat)
    (rs : List (U256 × U256)) : Good id evm (chargeGasAndMemory e c rs) := by
  unfold chargeGasAndMemory
  exact Good.bind (good_chargeGas h _) fun a => Good.pure_kr (KR.refl _)

theorem good_checkGas (evm e : Evm fork Nat) (c : Nat) :
    Good (fun _ => evm) evm (checkGas e c) := by
  unfold checkGas
  split
  · exact Good.throw_ (by decide)
  · exact Good.pure_kr (KR.refl _)

theorem good_accountCode (evm e : Evm fork Nat) (a : Address) :
    Good (fun _ => evm) evm (accountCode e a) := by
  unfold accountCode
  exact Good.mapError _ (by intro _ h; cases h) _

theorem good_creationAddress (evm : Evm fork Nat) (sender : Address) (nonce : Nat)
    (salt : Option U256) (initCode : ByteArray) :
    Good (fun _ => evm) evm (creationAddress sender nonce salt initCode) := by
  unfold creationAddress
  split
  · exact Good.ok_kr (KR.refl _)
  · exact Good.mapError _ (by intro _ h; cases h) _

/-- The rest of an instruction that keeps its reads: an error that does not abort becomes an
exceptional halt with that error, which is no revert. -/
theorem good_keepReads {α : Type} {p : α → Evm fork Nat} {halted : Evm fork Nat → α}
    (hp : ∀ x, p (halted x) = x) {evm e : Evm fork Nat} {rest : Except EvmError α}
    (h : Good p evm rest) : Good p evm (keepReads e halted rest) := by
  unfold keepReads
  cases hr : rest with
  | error err =>
    have hne := h.1 err hr
    simp only
    split
    · exact Good.err hne
    · refine Good.ok_kr fun hh => ?_
      rw [hp] at hh
      simp only [exceptionalHalt, Option.some.injEq] at hh
      exact absurd hh hne
  | ok a => exact Good.ok_kr (h.2 a hr)

/-- The frame relation in the goals the tactic leaves: the frame is built from the other with
the same error. -/
macro "kr" : tactic => `(tactic| first
  | exact KR.refl _
  | assumption
  | (apply KR.of_eq; simp [advance, recordAccountRead, recordStorageRead, refillStateGas,
      frameOf]; done)
  | (apply KR.of_eq; rfl)
  | (refine KR.trans (by assumption) ?_; apply KR.of_eq; simp [advance, recordAccountRead,
      recordStorageRead, refillStateGas, frameOf]; done)
  | (refine KR.trans (by assumption) ?_; apply KR.of_eq; rfl))

/-- After a split of a pair that is no part of a bind, name its frame by the expression. -/
macro "pair_subst" : tactic =>
  `(tactic| (rename_i hpair; have h2 := congrArg Prod.snd hpair; dsimp only at h2; subst h2))

syntax "good_step" : tactic
macro_rules
  | `(tactic| good_step) => `(tactic| first
    | exact Good.err (by decide)
    | exact Good.throw_ (by decide)
    | exact Good.pure_kr (by kr)
    | exact Good.ok_kr (by kr)
    | (refine Good.bind (good_popWord (by kr)) ?_; rintro ⟨_, _⟩; dsimp only)
    | (refine Good.bind (good_pushWord (by kr) _) ?_; intro _)
    | (refine Good.bind (good_chargeGas (by kr) _) ?_; intro _)
    | (refine Good.bind (good_chargeStateGas (by kr) _) ?_; intro _)
    | (refine Good.bind (good_chargeGasAndMemory (by kr) _ _) ?_; intro _)
    | (refine Good.bindc (good_checkGas _ _ _) ?_; intro _)
    | (refine Good.bindc (good_accountCode _ _ _) ?_; intro _)
    | (refine Good.bindc (good_creationAddress _ _ _ _ _) ?_; intro _)
    | (refine Good.bindc (Good.mapError _ (by intro _ h; cases h) _) ?_; intro _)
    | (refine good_keepReads (fun _ => rfl) ?_)
    | (refine Good.map_next ?_)
    | (split <;> try pair_subst)
    | (refine Good.bindc ?_ (fun _ => ?_))
    | (dsimp only))

/-- Check a do-block part by part. -/
macro "good" : tactic => `(tactic| repeat' good_step)

/-! ## The instructions -/

theorem good_haltWithOutput {evm e : Evm fork Nat} (h : KR evm e) :
    Good id evm (haltWithOutput e) := by
  unfold haltWithOutput; good

theorem good_readFrame {evm e : Evm fork Nat} (h : KR evm e) (c : Nat) (v : Evm fork Nat → U256) :
    Good id evm (readFrame c v e) := by
  unfold readFrame; good

theorem good_popTopics {evm : Evm fork Nat} : ∀ (n : Nat) {e : Evm fork Nat}, KR evm e →
    Good Prod.snd evm (popTopics e n)
  | 0, e, h => by unfold popTopics; exact Good.ok_kr h
  | n + 1, e, h => by
    unfold popTopics
    refine Good.bind (good_popWord h) ?_
    rintro ⟨_, e1⟩
    refine Good.bind (good_popTopics n (KR.refl e1)) ?_
    rintro ⟨_, e2⟩
    exact Good.pure_kr (KR.refl _)

theorem good_stackOnly {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : stackOnlyStep fork op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals first
    | (cases hf; done)
    | (simp only [binaryOp, unaryOp, ternaryOp, expStep, keccak256Step, popStep, pushN, dupN,
        swapN, dupnStep, swapnStep, exchangeStep]; good)

theorem good_controlFlow {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : controlFlowStep op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  all_goals first
    | exact good_readFrame (KR.refl _) _ _
    | (simp only [stopStep, jumpStep, jumpiStep, jumpdestStep]; good)

theorem good_memoryData {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : memoryDataStep op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  all_goals first
    | exact good_readFrame (KR.refl _) _ _
    | (simp only [mloadStep, mstoreStep, mstore8Step, mcopyStep, calldataloadStep, copyToMemory,
        returndatacopyStep]; good)

theorem good_environment {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : environmentStep fork op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals first
    | (cases hf; done)
    | exact good_readFrame (KR.refl _) _ _
    | (simp only [blockhashStep, blobhashStep]; good)

theorem good_account {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : accountStep fork op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals first
    | (cases hf; done)
    | exact good_readFrame (KR.of_eq rfl) _ _
    | (simp only [balanceStep, extcodesizeStep, extcodecopyStep, extcodehashStep]; good)

theorem good_storage {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : storageStep op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  all_goals (simp only [sloadStep, sstoreStep]; good)

theorem good_transient {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : transientStorageStep fork op = some run) (evm : Evm fork Nat) :
    Good id evm (run evm) := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
    simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  all_goals (simp only [tloadStep, tstoreStep]; good)

theorem good_log {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : logOpStep op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
  subst hf
  unfold logStep
  refine Good.bind (good_popWord (KR.refl _)) ?_
  rintro ⟨_, e1⟩
  refine Good.bind (good_popWord (KR.refl _)) ?_
  rintro ⟨_, e2⟩
  refine Good.bind (good_popTopics _ (KR.refl _)) ?_
  rintro ⟨_, e3⟩
  dsimp only
  good

theorem good_finishSelfdestruct {evm e : Evm fork Nat} (h : KR evm e) (b : Address) (r : Nat) :
    Good id evm (finishSelfdestruct fork b r e) := by
  unfold finishSelfdestruct; good

theorem good_selfdestruct {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : selfdestructOpStep fork op = some run) (evm : Evm fork Nat) : Good id evm (run evm) := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
  subst hf
  unfold selfdestructStep
  good
  all_goals exact good_finishSelfdestruct (by kr) _ _

theorem good_returnOp {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hf : returnOpStep fork op = some run) (evm : Evm fork Nat) :
    (∀ e, run evm = .error e → e ≠ .revert) ∧ (op ≠ .revert → ∀ b, run evm = .ok b → KR evm b) := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
  · subst hf
    have g := good_haltWithOutput (evm := evm) (e := evm) (KR.refl _)
    exact ⟨g.1, fun _ => g.2⟩
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      refine ⟨fun e h => ?_, fun hne => absurd rfl hne⟩
      rw [revertStep_eq] at h
      cases hr : returnStep evm with
      | error e' =>
        rw [hr] at h; cases h
        exact (good_haltWithOutput (KR.refl evm)).1 _ hr
      | ok c => rw [hr] at h; cases h
    · cases hf

/-- **Every instruction that gives the next frame throws no revert**, and every one but REVERT
gives a frame with the revert error only from one. -/
theorem good_instruction {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hrun : instruction fork op = some run) (evm : Evm fork Nat) :
    (∀ e, run evm = .error e → e ≠ .revert) ∧ (op ≠ .revert → ∀ b, run evm = .ok b → KR evm b) := by
  have lift : Good id evm (run evm) →
      (∀ e, run evm = .error e → e ≠ .revert) ∧ (op ≠ .revert → ∀ b, run evm = .ok b → KR evm b) :=
    fun h => ⟨h.1, fun _ => h.2⟩
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_stackOnly hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_controlFlow hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_memoryData hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact good_returnOp hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_environment hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_account hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_storage hf evm)
  rcases orElse_eq_some hrun with hf | hrun
  · exact lift (good_transient hf evm)
  rcases orElse_eq_some hrun with hf | hf
  · exact lift (good_log hf evm)
  · exact lift (good_selfdestruct hf evm)

/-! ## The calls and the creations -/

theorem good_skipCall {evm e : Evm fork Nat} (h : KR evm e) (g r : Nat) :
    Good id evm (skipCall e g r) := by
  unfold skipCall; good

theorem good_popCallOperands {evm e : Evm fork Nat} (h : KR evm e) (kind : CallKind) :
    Good Prod.snd evm (popCallOperands kind e) := by
  unfold popCallOperands
  refine Good.bind (good_popWord h) ?_
  rintro ⟨_, e1⟩
  refine Good.bind (good_popWord (KR.refl _)) ?_
  rintro ⟨_, e2⟩
  refine Good.bind (p := Prod.snd) ?_ ?_
  · unfold popCallValue
    split
    · exact good_popWord (KR.refl _)
    · exact Good.ok_kr (KR.refl _)
  rintro ⟨_, e3⟩
  dsimp only
  good

theorem good_popSalt {evm e : Evm fork Nat} (h : KR evm e) (create2 : Bool) :
    Good Prod.snd evm (popSalt create2 e) := by
  unfold popSalt
  split
  · good
  · exact Good.ok_kr h

theorem good_accessDelegation {evm e : Evm fork Nat} (h : KR evm e) (a : Address) (k : Nat) :
    Good Prod.snd evm (accessDelegation e a k) := by
  unfold accessDelegation
  good

theorem good_payCall {evm e : Evm fork Nat} (h : KR evm e) (kind : CallKind) (call : CallOperands)
    (m x n : Nat) : Good Prod.snd evm (payCall kind call m x n e) := by
  unfold payCall; good

theorem good_genericCall {evm e : Evm fork Nat} (h : KR evm e) (message : Message fork) (n : Nat)
    (o s : U256) : Good frameOf evm (genericCall e message n o s) := by
  unfold genericCall
  dsimp only
  split
  · exact Good.map_next (good_skipCall (by kr) _ _)
  · exact Good.ok_kr (by kr)

theorem good_finishCall {evm e : Evm fork Nat} (h : KR evm e) (kind : CallKind)
    (call : CallOperands) (callee : Callee) (s n x : Nat) :
    Good frameOf evm (finishCall kind call callee s n x e) := by
  unfold finishCall
  split
  · exact Good.err (by decide)
  · dsimp only
    split
    · exact Good.map_next (good_skipCall (by kr) _ _)
    · exact good_genericCall (by kr) _ _ _ _

/-- The parts of the calls and the creations, for `good_call`. -/
syntax "good_call_step" : tactic
macro_rules
  | `(tactic| good_call_step) => `(tactic| first
    | (refine Good.bind (good_popCallOperands (by kr) _) ?_; rintro ⟨_, _⟩; dsimp only)
    | (refine Good.bind (good_popSalt (by kr) _) ?_; rintro ⟨_, _⟩; dsimp only)
    | (refine Good.bind (good_accessDelegation (by kr) _ _) ?_; rintro ⟨_, _⟩; dsimp only)
    | (refine Good.bind (good_payCall (by kr) _ _ _ _ _) ?_; rintro ⟨_, _⟩; dsimp only)
    | exact good_finishCall (by kr) _ _ _ _ _ _
    | exact good_genericCall (by kr) _ _ _ _
    | exact Good.map_next (good_skipCall (by kr) _ _))

macro "good_call" : tactic => `(tactic| repeat' (first | good_call_step | good_step))

theorem good_callStep {evm : Evm fork Nat} (kind : CallKind) :
    Good frameOf evm (callStep kind evm) := by
  unfold callStep; good_call

theorem good_launchCreate {evm e : Evm fork Nat} (h : KR evm e) (v : U256) (code : ByteArray)
    (salt : Option U256) : Good frameOf evm (launchCreate e v code salt) := by
  unfold launchCreate; good_call

theorem good_createStep {evm : Evm fork Nat} (create2 : Bool) :
    Good frameOf evm (createStep create2 evm) := by
  unfold createStep genericCreate; good_call
  all_goals exact good_launchCreate (by kr) _ _ _

/-- **Every call and creation throws no revert**, and its next frame, or the caller of its
message, has the revert error only from one. -/
theorem good_message {op : Op} {run : Evm fork Nat → Except EvmError (StepResult fork Nat)}
    (hrun : messageInstruction fork op = some run) (evm : Evm fork Nat) :
    Good frameOf evm (run evm) := by
  unfold messageInstruction at hrun
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
      (try subst hf)
    all_goals first | (cases hf; done) | exact good_callStep _
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
      (try subst hf)
    all_goals first | (cases hf; done) | exact good_createStep _

/-! ## The step -/

/-- **No step throws a revert, and only REVERT ends a frame with it**: a step of a frame throws no
revert, and a step that gives a frame with the revert error starts from a frame with it, or runs
REVERT. -/
theorem step_good (low : Evm fork Nat) :
    (∀ e, step fork low = .error e → e ≠ .revert) ∧
    ∀ b, step fork low = .ok (.next b) → b.error = some .revert →
      low.error = some .revert ∨
        ∃ h : low.pc < low.code.size, Op.ofByte fork low.code[low.pc] = some .revert := by
  unfold step
  split
  · rename_i hlt
    dsimp only
    split
    · exact ⟨(fun e h => by cases h; intro h'; cases h'), (fun b h => by cases h)⟩
    · rename_i op hop
      split
      · rename_i run hrun
        have g := good_instruction hrun low
        refine ⟨fun e h => ?_, fun b h hb => ?_⟩
        · cases hr : run low with
          | error e' => rw [hr] at h; cases h; exact g.1 _ hr
          | ok c => rw [hr] at h; cases h
        · cases hr : run low with
          | error e' => rw [hr] at h; cases h
          | ok c =>
            rw [hr] at h
            cases h
            by_cases hrev : op = .revert
            · subst hrev; exact .inr ⟨hlt, hop⟩
            · exact .inl (g.2 hrev _ hr hb)
      · split
        · rename_i run hm
          have g := good_message hm low
          exact ⟨g.1, fun b h hb => .inl (g.2 _ h hb)⟩
        · exact ⟨(fun e h => by cases h; intro h'; cases h'), (fun b h => by cases h)⟩
  · refine ⟨(fun e h => by cases h), (fun b h hb => ?_)⟩
    simp only [stopStep, Functor.map, Except.map, Except.ok.injEq, StepResult.next.injEq] at h
    subst h
    exact .inl hb

/-- info: 'EthLib.Execution.Evm.RevertErr.step_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_good

end EthLib.Execution.Evm.RevertErr
