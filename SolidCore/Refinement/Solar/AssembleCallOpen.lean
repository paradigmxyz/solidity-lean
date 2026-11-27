import SolidCore.Refinement.Solar.AssembleCallIn
import Verify.ShapeOpen
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# STATICCALLs to the bytecode in an open world

`AssembleCallIn` runs the bytecode in EthLib's closed state (`Target.preState`: the contract and
its caller only), where every callee that is not a precompile has no code. Here the bytecode runs
in `Shapes.Target.preStateIn env`: any other accounts, with any code, storage, balance and nonce
(`TargetEnv.WF`: distinct addresses below `2 ^ 160`, neither the contract nor its caller). So the
callee of each STATICCALL is arbitrary code, and its answers (success flag, return data) are
whatever EthLib computes for that code, however deep its own calls go.

* `preStateIn` facts: the contract's storage and account and the caller's account are those of
  `Target.preState` (the environment only inserts other addresses).
* `WithinIn env A p gas code scope`: every result of the bytecode in `env` at `gas` is the
  program's, or a failure that changes nothing.
* `within_of_advancesQ_in`: `AssembleCallSeg.within_of_advancesQ` from `preStateIn env`.
* `runs_of_checkXB_open`, `assembly_of_checkXB_norm_open`: the checker with contexts' theorems
  in every well-formed environment, under `AssembleCallPre.EcrecoverAgree` and `CalleesRunOpen`
  (`AssembleCallIn.CalleesRunIn` of the run in `env`), both in the statement. The oracle answers the
  run's static calls from its table and agrees with an open world (`CallsAgree`).
* `runs_of_checkXB_tab`, `assembly_of_checkXB_norm_tab`: the same, with the table read from
  EthLib (`TabP (CalleeEntry gas)`: every output is a callee frame's, of fewer than `2 ^ 256`
  bytes), so the open world fits (`Fits`) and is a run's world (`RunWorld`).
* `open_equiv_run`: the composition with a source stage asked only of fitting open worlds.
-/

namespace SolidCore.Refinement.Solar.AssembleCallOpen

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallWorld
open SolidCore.Refinement.Solar.AssembleCallCut SolidCore.Refinement.Solar.AssembleDyn
open SolidCore.Refinement.Solar.AssembleCallSeg SolidCore.Refinement.Solar.AssembleCtx
open SolidCore.Refinement.Solar.AssembleCallIn
open SolidCore.Refinement.Shapes (TargetEnv EnvAccount)
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State

/-! ## The environment's state -/

/-- One account of the environment added to a state, as `preStateIn` adds it. -/
def addAccount (s : EthLib.Execution.State.State) (a : EnvAccount) : EthLib.Execution.State.State :=
  let h := EthLib.Cryptography.Hash.Keccak.keccak256 a.code
  { accounts := s.accounts.insert (Refinement.Target.address a.addr)
      { nonce := a.nonce, balance := BitVec.ofNat 256 a.balance, codeHash := h },
    storage := s.storage.insert (Refinement.Target.address a.addr)
      (a.storage.foldl (fun m kv =>
        m.insert (Refinement.Target.storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅),
    code := s.code.insert h a.code }

/-- Adding accounts at other addresses keeps the account and the storage at `X`. -/
theorem foldl_addAccount_keep (X : Address) :
    ∀ (env : TargetEnv) (s : EthLib.Execution.State.State), (∀ a ∈ env, Refinement.Target.address a.addr ≠ X) →
      (env.foldl addAccount s).accounts[X]? = s.accounts[X]? ∧
        (env.foldl addAccount s).storage[X]? = s.storage[X]?
  | [], _, _ => ⟨rfl, rfl⟩
  | a :: env, s, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_addAccount_keep X env (addAccount s a)
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have hne : compare (Refinement.Target.address a.addr) X ≠ .eq := by
      rw [ne_eq, Std.compare_eq_iff_eq]; exact h a List.mem_cons_self
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · simp only [addAccount]
      rw [Std.ExtTreeMap.getElem?_insert]
      simp [hne]
    · simp only [addAccount]
      rw [Std.ExtTreeMap.getElem?_insert]
      simp [hne]

/-- `preStateIn` is `preState`'s state with the environment's accounts added. -/
theorem preStateIn_eq (env : TargetEnv) (code : ByteArray) (call : Call) :
    Shapes.Target.preStateIn env code call = TransactionState.ofBlock
      { preState := env.foldl addAccount (Target.preState code call).parent.preState,
        accountWrites := ∅, storageWrites := ∅, codeWrites := ∅, storageClears := ∅ } := rfl

theorem addr_ne {env : TargetEnv} (hwf : env.WF) {X : Nat} (hX : X < 2 ^ 160)
    (hne : ∀ a ∈ env, a.addr ≠ X) : ∀ a ∈ env, Refinement.Target.address a.addr ≠ Refinement.Target.address X :=
  fun a ha h => hne a ha (by
    have := congrArg (fun x : Address => x.toU256.toNat) h
    rwa [address_toNat (hwf.2 a ha).1, address_toNat hX] at this)

/-- The contract's storage in the environment is its storage before the call. -/
theorem getStorage_preStateIn_self {env : TargetEnv} (hwf : env.WF) (code : ByteArray) (call : Call)
    (key : Bytes32) :
    (Shapes.Target.preStateIn env code call).getStorage (Target.address selfAddress) key =
      (Target.preState code call).getStorage (Target.address selfAddress) key := by
  have hk := (foldl_addAccount_keep (Target.address selfAddress) env
    (Target.preState code call).parent.preState
    (addr_ne hwf (by decide) fun a ha => (hwf.2 a ha).2.1)).2
  rw [preStateIn_eq]
  simp only [TransactionState.getStorage, TransactionState.ofBlock, StorageMap.slot, State.getStorage] at hk ⊢
  rw [hk]
  rfl

/-- The contract's account and the caller's in the environment are those before the call. -/
theorem getAccountOptional_preStateIn {env : TargetEnv} (hwf : env.WF) (code : ByteArray)
    (call : Call) {X : Nat} (hX : X < 2 ^ 160) (hne : ∀ a ∈ env, a.addr ≠ X) :
    (Shapes.Target.preStateIn env code call).getAccountOptional (Target.address X) =
      (Target.preState code call).getAccountOptional (Target.address X) := by
  have hk := (foldl_addAccount_keep (Target.address X) env
    (Target.preState code call).parent.preState (addr_ne hwf hX hne)).1
  rw [preStateIn_eq]
  simp only [TransactionState.getAccountOptional, TransactionState.ofBlock, State.getAccountOptional] at hk ⊢
  rw [hk]
  rfl

/-! ## The bytecode in the environment -/

/-- EthLib on runtime bytecode with `gas` gas, in the environment `env`. -/
def ethLibIn (env : TargetEnv) (gas : Nat) : Sem :=
  { Prog := ByteArray, run := Shapes.Target.runWithIn env gas }

/-- A failed run in the environment leaves the storage as it was and logs nothing. -/
theorem runWithIn_failure {env : TargetEnv} {gas : Nat} {code : ByteArray} {call : Call}
    {obs : Observable} (h : Shapes.Target.runWithIn env gas code call = some obs)
    (hf : obs.success = false) : obs.storage = slotValue call.storage ∧ obs.logs = [] := by
  unfold Shapes.Target.runWithIn at h
  split at h
  · cases h
  · cases h
    simp only at hf
    simp [hf]

/-- The relation at the start of the frame, from the environment's state. -/
theorem rel_initial_in {env : TargetEnv} (hwf : env.WF) (code : ByteArray) (call : Call) :
    Rel (Target.message code call) Substate.empty (Shapes.Target.preStateIn env code call)
      Substate.empty (SolarTV.Machine.State.initial call) := by
  have R0 := rel_initial code call
  refine ⟨fun k => ?_, ?_, R0.logs⟩
  · rw [show (Target.message code call).currentTarget = Target.address selfAddress from rfl,
      getStorage_preStateIn_self hwf]
    exact R0.storage k
  · rw [show (Target.message code call).currentTarget = Target.address selfAddress from rfl,
      getAccountOptional_preStateIn hwf code call (by decide) (fun a ha => (hwf.2 a ha).2.1)]
    exact R0.account

theorem getAccount_preStateIn_self {env : TargetEnv} (hwf : env.WF) (code : ByteArray) (call : Call) :
    (Shapes.Target.preStateIn env code call).getAccount (Target.address selfAddress) =
      (Target.preState code call).getAccount (Target.address selfAddress) := by
  simp only [TransactionState.getAccount]
  rw [getAccountOptional_preStateIn hwf code call (by decide) (fun a ha => (hwf.2 a ha).2.1)]

/-- `AssembleLoopWithin.rel_start` from the environment's state. -/
theorem rel_start_in {env : TargetEnv} (hwf : env.WF) (code : ByteArray) (call : SolarTV.Call)
    (gas : Nat) {st' : TransactionState} (ss' : Substate)
    (h : ¬ ((Final.Target.messageWith gas code call).shouldTransferValue = true ∧
        (Final.Target.messageWith gas code call).value ≠ 0) → st' = Shapes.Target.preStateIn env code call)
    (hm : ((Final.Target.messageWith gas code call).shouldTransferValue = true ∧
        (Final.Target.messageWith gas code call).value ≠ 0) →
      (Shapes.Target.preStateIn env code call).moveEther .fusaka
        (Final.Target.messageWith gas code call).caller
        (Final.Target.messageWith gas code call).currentTarget
        (Final.Target.messageWith gas code call).value = .ok st') :
    Rel (Final.Target.messageWith gas code call) ss' st' ss' (SolarTV.Machine.State.initial call) := by
  have R0 := rel_initial_in hwf code call
  by_cases htr : (Final.Target.messageWith gas code call).shouldTransferValue = true ∧
      (Final.Target.messageWith gas code call).value ≠ 0
  · have hmove := hm htr
    have hn : ((Shapes.Target.preStateIn env code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
      rw [getAccount_preStateIn_self hwf, getAccount_preState_self]; simp
    have hAB : Target.address selfAddress ≠ Target.address callerAddress := by decide
    exact ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
      (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, ⟨[], by simp, .nil⟩⟩
  · obtain rfl := h htr
    exact ⟨R0.storage, R0.account, ⟨[], by simp, .nil⟩⟩

/-- Every log matched to SolarTV's world is the frame's own. -/
theorem address_of_match {a : Address} {w : List SolarTV.Machine.Event}
    {L : List EthLib.Execution.Blocks.Log} (h : List.Forall₂ (LogMatch a) w L) :
    ∀ l ∈ L, l.address = a := by
  induction h with
  | nil => intro _ h; cases h
  | @cons e l _ _ hl _ ih =>
    intro l' hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · cases e <;> simp only [LogMatch] at hl
      exact hl.1
    · exact ih l' hl'

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **`AssembleCallSeg.within_of_advancesQ` in the environment `env`**: the same block simulation
makes every result of the bytecode run from `preStateIn env` the EVM IR's under the oracle of the
run's table, or a failure that changes nothing, and every output of that table meets `F` when each
block keeps it (`AdvancesQT`). -/
theorem within_of_advancesQT_in {env : TargetEnv} (hwf : env.WF) {p : Assemble.Program}
    {code : ByteArray} {call : Call} {gas : Nat}
    {F : Bool → ByteArray → Prop}
    (O : RunTable → Oracle) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (hP : Meets P (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas))
    (hQ : ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
        (Shapes.Target.preStateIn env code call) Substate.empty = .ok r → r.1.error = none →
      Q _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas) r.1)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesQT (fun o => block o call p) O F P Q (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, TabP F T ∧ Within (evmirSem (O T)) (ethLibIn env gas) p code (· = call) := by
  by_cases hs : ∃ obs, Shapes.Target.runWithIn env gas code call = some obs ∧ obs.success = true
  swap
  · refine ⟨{}, TabP.empty F, fun call' hc obs hrun => Or.inr ?_⟩
    subst hc
    have hf : obs.success = false := by
      cases h : obs.success
      · rfl
      · exact absurd ⟨obs, hrun, h⟩ hs
    exact ⟨hf, runWithIn_failure hrun hf⟩
  obtain ⟨obs, hrun, hsucc⟩ := hs
  suffices H : ∃ T, TabP F T ∧ (evmirSem (O T)).run p call = some obs by
    obtain ⟨T, hTP, hT⟩ := H
    refine ⟨T, hTP, fun call' hc obs' hrun' => Or.inl ?_⟩
    subst hc
    change Shapes.Target.runWithIn env gas code call' = some obs' at hrun'
    rw [hrun] at hrun'
    cases hrun'
    exact hT
  unfold Shapes.Target.runWithIn at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hsucc
  obtain ⟨st', ss', within, hcases, hmove, hrf⟩ :=
    AssembleRun.processMessage_ok' (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  have R := rel_start_in hwf code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hTP, hit, hpost⟩ := run_of_advancesQT (fun o => block o call p) O (adv ss')
    hP _ {} _ _ within evm (start st' ss' R) (Nat.lt_succ_self _) hrf hok (hQ _ hpm hok)
  obtain ⟨k, hk⟩ := hit T (RunTable.Le.refl T)
  refine ⟨T, hTP, ?_⟩
  have hres : (evmirSem (O T)).run p call = some (observe call sF halt) := by
    change (SolarTV.EVM.Program.layer.result (O T) p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨k, hk⟩]
    rfl
  rw [hres]
  set msg := Final.Target.messageWith gas code call with hmsg
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := hpost
  have hss' : ss'.logs.toList = [] := by
    by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
    · rw [(hmove htr).2]
      simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
    · rw [(hcases htr).2]
      simp [Substate.empty]
  have hlogs := logs_of_match hL2
  have hown : L.filter (fun log => log.address == Target.address selfAddress) = L := by
    rw [List.filter_eq_self]
    intro l hl
    have := address_of_match hL2 l hl
    simp [this, msg, Final.Target.messageWith, Target.message]
  have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
  have herr' : evm.error = errorOf (observe call sF halt) := herr
  have hout' : evm.output.toList.map (·.toNat) = (observe call sF halt).output := hout
  have hst' : (observe call sF halt).success = true →
      evm.substate.logs = ssF.logs ∧ ∀ slot,
        (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
          (observe call sF halt).storage slot :=
    fun h => ⟨hlogsF, hst h⟩
  have hfail : (observe call sF halt).success = false →
      (observe call sF halt).logs = [] ∧
      (observe call sF halt).storage = slotValue call.storage := by
    cases halt <;> simp [observe]
  have hok2 : (observe call sF halt).success = true →
      (observe call sF halt).logs = logs sF := by
    cases halt <;> simp [observe]
  clear herr hout hst hres hit hk
  generalize observe call sF halt = X at *
  have hsucc' : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  symm
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc' hout' hfail hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc', hout', ?_, ?_⟩
    · rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hown, hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        exact (hst' hs).2 slot

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **`AssembleCallSeg.within_of_advancesQ` in the environment `env`**: `within_of_advancesQT_in`
with no property of the table's entries. -/
theorem within_of_advancesQ_in {env : TargetEnv} (hwf : env.WF) {p : Assemble.Program}
    {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (hP : Meets P (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas))
    (hQ : ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
        (Shapes.Target.preStateIn env code call) Substate.empty = .ok r → r.1.error = none →
      Q _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas) r.1)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesQ (fun o => block o call p) O P Q (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, Within (evmirSem (O T)) (ethLibIn env gas) p code (· = call) := by
  obtain ⟨T, -, hT⟩ := within_of_advancesQT_in hwf (F := fun _ _ => True) O P Q
    (fun ss0 T x e => E ss0 T x e ∧ TabP (fun _ _ => True) T) meas hP hQ
    (fun st' ss' R => ⟨start st' ss' R, TabP.true _⟩)
    (fun ss0 T x evm hE => AdvancesQ.toQT _ _ (adv ss0 T x evm hE.1))
  exact ⟨T, hT⟩

/-! ## The checker with contexts in the environment -/

/-- **Named hypothesis on a run in the environment**: when it succeeds, each of its STATICCALLs
calls code, or ECRECOVER as `AssembleCallSeg.PreRun` asks. -/
def CalleesRunOpen (env : TargetEnv) (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (Shapes.Target.preStateIn env code call) Substate.empty = .ok r → r.1.error = none →
    CalleesOkR code (Final.Target.messageWith gas code call) StaticOkEIn gas
      (processRunner .fusaka (Meter := Nat) gas) r.1

/-- The runner's callee frames as the open route reads them: `StaticOkEIn`, and the frame is the
one EthLib's runner of messages gives for that message from that caller. -/
def RanIn (gas : Nat) (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) :
    Prop :=
  StaticOkEIn caller m child ∧
    ∃ lt e, processRunner .fusaka (Meter := Nat) gas caller m lt = .ok e ∧ e.val = child

theorem meets_ranIn (gas : Nat) :
    Meets (bound := gas) (RanIn gas) (processRunner .fusaka (Meter := Nat) gas) :=
  ⟨fun a b c d e => ⟨(staticOkEIn gas).ok a b c d e, c, d, e, rfl⟩, (staticOkEIn gas).aborts⟩

/-- **An entry of a run's table, read from EthLib**: the success flag and output of a frame
EthLib's runner of messages gives for a static message, and an output of fewer than `2 ^ 256`
bytes. -/
def CalleeEntry (gas : Nat) (ok : Bool) (out : ByteArray) : Prop :=
  out.size < 2 ^ 256 ∧ ∃ (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat),
    ∃ lt e, processRunner .fusaka (Meter := Nat) gas caller m lt = .ok e ∧ e.val = child ∧
    m.isStatic = true ∧ ok = child.error.isNone ∧ out = child.output

theorem calleeEntry_of (gas : Nat) : ∀ c m ch, RanIn gas c m ch → m.isStatic = true →
    m.data.size < 2 ^ 256 → CalleeEntry gas ch.error.isNone ch.output :=
  fun c m ch ⟨hS, lt, e, he, hv⟩ hs hd => ⟨hS.1.2.2 hd, c, m, ch, lt, e, he, hv, hs, rfl, rfl⟩

/-- **EVM IR to bytecode, run by run, in the environment `env`**, for code with STATICCALLs, with
the run's table read from EthLib: each of its outputs, with its flag, is a callee frame's
(`CalleeEntry`). -/
theorem runs_of_checkXB_tab {env : TargetEnv} (hwf : env.WF) {p : Assemble.Program}
    {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call)
    (hagree : AssembleCallPre.EcrecoverAgree) (hQ : CalleesRunOpen env gas code call) :
    ∃ T, TabP (CalleeEntry gas) T ∧
      Within (evmirSem (OS codes T)) (ethLibIn env gas) p code (· = call) := by
  obtain ⟨G, hseg, hcount, hneed0⟩ := globXB_of_checkXB hc
  refine within_of_advancesQT_in hwf (F := CalleeEntry gas) (OS codes) (RanIn gas)
    (CalleesOk code (Final.Target.messageWith gas code call) (RanIn gas))
    (fun ss0 T x e => EntXS codes p cx code (Final.Target.messageWith gas code call) ss0 T x e ∧
      TabP (CalleeEntry gas) T)
    (fun y e => AssembleLoop.meas p cx.base e.gas y.1) (meets_ranIn gas)
    (fun r hr he => by
      intro e within pc asked addr inOff inSize outOff outSize S M g st ss rd hat hlt hb hrun
      exact (hQ r hr he hat hlt hb hrun).imp id fun ⟨a, b, c, d⟩ =>
        ⟨a, hagree, fun c' m' ch' h' => b c' m' ch' h'.1, c, d⟩)
    (fun st' ss' R => ⟨?_, TabP.empty _⟩)
    (fun ss0 T x evm hE => advances_checkXS_tab G codes rfl
      (by simp [Final.Target.messageWith, SolidCore.Refinement.Target.message]) rfl rfl rfl rfl rfl
      hgas (by show 0 + 1 ≤ 1024; decide) T x evm hE.1 hE.2 (fun _ _ _ h => h.1.1) (calleeEntry_of gas))
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hseg0 : Seg (bytesOf code) (certAt cx (p.blocks.length + 1) 0 0).offset 0
      (lowerFrom p (certAt cx (p.blocks.length + 1) 0 0) 0 (p.blocks.drop 0)) code.size := by
    rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  refine ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame,
    ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hn0, hneed0], by simp⟩,
    SR.nil _ _, hseg0, by simp, memRel_initial, R, ?_⟩, rfl, ⟨rfl, rfl, rfl⟩,
    fun T'' _ => rdRel_nil codes T'', ?_⟩, fun _ => ⟨0, hcount,
    hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
    by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- **EVM IR to bytecode, run by run, in the environment `env`**, for code with STATICCALLs, with no
hypothesis on the runner. -/
theorem runs_of_checkXB_open {env : TargetEnv} (hwf : env.WF) {p : Assemble.Program}
    {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call)
    (hagree : AssembleCallPre.EcrecoverAgree) (hQ : CalleesRunOpen env gas code call) :
    ∃ T, Within (evmirSem (OS codes T)) (ethLibIn env gas) p code (· = call) := by
  obtain ⟨T, -, hT⟩ := runs_of_checkXB_tab hwf hc codes gas hgas call hagree hQ
  exact ⟨T, hT⟩

/-- **The assembly premise in every environment, for code with STATICCALLs**: below `2 ^ 256`
gas, in every well-formed environment (any other accounts, with any code), for every call in scope
whose run meets `CalleesRunOpen`, under `EcrecoverAgree`, an oracle and an
open world that agree, under which the EVM IR gives the bytecode's result in that environment or a
failure that changes nothing. -/
theorem assembly_of_checkXB_norm_open {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB (norm p) code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hagree : AssembleCallPre.EcrecoverAgree) :
    ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, scope call →
      CalleesRunOpen env gas code call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk cx.base o ∧ Within (evmirSem o) (ethLibIn env gas) p code (· = call) := by
  intro env hwf gas hgas call _ hQ
  obtain ⟨T, hT⟩ := runs_of_checkXB_open hwf hc codes gas hgas call hagree hQ
  exact ⟨OS codes T, tabWorld T.oks T.outs codes, (OS_agree codes T).1, (OS_agree codes T).2,
    OS_ok codes cx.base T, within_norm hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.assembly_of_checkXB_norm_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkXB_norm_open

/-! ## The worlds of the open route -/

open SolidCore.Solidity.Source EvmCompiler.Simulation in
/-- **What the source stage may assume of a world**: the other accounts' code is at addresses below
`2 ^ 160`, and a static call to code (no precompile, no value) is answered with fewer than `2 ^ 256`
bytes of return data. Only calls to code: an open world answers a precompile call as SolidCore does
(`World.Open.precompiles`), and IDENTITY returns its input, so no open world bounds every answer. -/
def Fits (W : World) : Prop :=
  (∀ p ∈ W.codes.getD [], p.1 < 2 ^ 160) ∧
    ∀ h world request a, W.ans h (.external world (.call request)) = some a →
      toCode (machineKind request.kind) (addressToWord request.codeAddress)
        (u256ToWord request.transferValue) = true →
      a.returnData.size < 2 ^ 256

/-- **A world of callee outputs**: a world whose every output, with its flag, is SOME callee frame's
that EthLib's runner gave at the bound `gas` (`CalleeEntry`); the caller, message and
table are existential, so this does not tie the answers to a particular run's callee. -/
def RunWorld (gas : Nat) (W : World) : Prop :=
  ∃ (T : RunTable) (codes : SolidCore.Solidity.Shared.Account.BytesMap),
    W = tabWorld T.oks T.outs codes ∧ TabP (CalleeEntry gas) T

open SolidCore.Solidity.Source EvmCompiler.Simulation in
/-- The world of a table of callee frames fits. -/
theorem tabWorld_fits {gas : Nat} {T : RunTable} {codes : SolidCore.Solidity.Shared.Account.BytesMap}
    (hcodes : ∀ p ∈ codes, p.1 < 2 ^ 160) (hT : TabP (CalleeEntry gas) T) :
    Fits (tabWorld T.oks T.outs codes) := by
  refine ⟨fun p hp => hcodes p (by simpa [tabWorld] using hp), fun h world request a ha hto => ?_⟩
  change some (tabCall T.oks T.outs (sourceCalls h).length world request) = some a at ha
  obtain rfl := Option.some.inj ha
  simp only [tabCall, hto, ite_true, tabHit]
  by_cases hn : (sourceCalls h).length < T.outs.length
  · exact (hT _ hn).1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]

/-- **The assembly premise in every environment, with the world read from EthLib**:
`assembly_of_checkXB_norm_open`'s statement whose open world also fits (`Fits`) and is a run's world
(`RunWorld`): each static call to code is answered with the flag and output of a callee frame of
EthLib's runner. -/
theorem assembly_of_checkXB_norm_tab {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB (norm p) code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (hcodes : ∀ q ∈ codes, q.1 < 2 ^ 160) (scope : Call → Prop)
    (hagree : AssembleCallPre.EcrecoverAgree) :
    ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, scope call →
      CalleesRunOpen env gas code call → ∃ (o : Oracle) (W : World), W.Open ∧ Fits W ∧
      RunWorld gas W ∧ CallsAgree o W ∧ CertOk cx.base o ∧
      Within (evmirSem o) (ethLibIn env gas) p code (· = call) := by
  intro env hwf gas hgas call _ hQ
  obtain ⟨T, hTP, hT⟩ := runs_of_checkXB_tab hwf hc codes gas hgas call hagree hQ
  exact ⟨OS codes T, tabWorld T.oks T.outs codes, (OS_agree codes T).1, tabWorld_fits hcodes hTP,
    ⟨T, codes, rfl, hTP⟩, (OS_agree codes T).2, OS_ok codes cx.base T, within_norm hT⟩

/-! ## The composition in every environment -/

/-- **Source to bytecode in every environment, from its parts**: a SolidCore source total in every
open world, a source stage into the first lowered MIR under every oracle that agrees with an open
world (`CallsAgree`), the backend stages under every oracle, and the bytes edge in every
well-formed environment (`assembly_of_checkXB_norm_open`'s shape) give: in every environment, at
every gas below `2 ^ 256`, every result of the exact bytecode on a valid call whose run meets
`RunOk` is SolidCore's result in some open world (the callee's answers are that world's), or a
failure that changes nothing. -/
theorem open_equiv_of_parts {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mirSem : Oracle → Sem} {m : ∀ o, (mirSem o).Prog} {q : Assemble.Program} {code : ByteArray}
    {Valid : Call → Prop} {RunOk : TargetEnv → Nat → Call → Prop}
    (total : ∀ W : World, W.Open → ∀ call, Valid call → (Source.runIn W fuel c call).isSome)
    (source : ∀ o W, W.Open → CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (m o) Valid)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (m o) q Valid)
    (bytes : ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call →
      RunOk env gas call → ∃ (o : Oracle) (W : World), W.Open ∧ CallsAgree o W ∧
        Within (evmirSem o) (ethLibIn env gas) q code (· = call)) :
    ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → RunOk env gas call →
      ∀ obs, Shapes.Target.runWithIn env gas code call = some obs →
        (∃ W : World, W.Open ∧ Source.runIn W fuel c call = some obs) ∨ Shapes.Inert call obs := by
  intro env hwf gas hgas call hv hok obs hrun
  obtain ⟨o, W, hW, hA, hwi⟩ := bytes env hwf gas hgas call hv hok
  rcases hwi call rfl obs hrun with h | h
  · left
    obtain ⟨obs0, h0⟩ := Option.isSome_iff_exists.mp (total W hW call hv)
    have hq := ((source o W hW hA).trans (backend o)) call hv obs0 h0
    rw [hq] at h
    cases h
    exact ⟨W, hW, h0⟩
  · exact Or.inr h

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.open_equiv_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms open_equiv_of_parts


/-- **Source to bytecode in every environment, with the world read from EthLib**: as
`open_equiv_of_parts`, with the source's totality and stage asked only of open worlds that fit
(`Fits`, which the size of an answer needs: SolidCore decodes a call's return data at its full
length, the EVM IR at its length modulo `2 ^ 256`), and the bytes edge giving a fitting run's world
(`RunWorld`). Every result of the exact bytecode on a valid call whose run meets `RunOk` is SolidCore's
result in a world that fits and whose answers are callee frames of EthLib's runner, or a failure
that changes nothing. -/
theorem open_equiv_run {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mirSem : Oracle → Sem} {m : ∀ o, (mirSem o).Prog} {q : Assemble.Program} {code : ByteArray}
    {Valid : Call → Prop} {RunOk : TargetEnv → Nat → Call → Prop}
    (total : ∀ W : World, W.Open → Fits W → ∀ call, Valid call → (Source.runIn W fuel c call).isSome)
    (source : ∀ o W, W.Open → Fits W → CallsAgree o W →
      Stage (solidCoreIn W fuel) (mirSem o) c (m o) Valid)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (m o) q Valid)
    (bytes : ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call →
      RunOk env gas call → ∃ (o : Oracle) (W : World), W.Open ∧ Fits W ∧ RunWorld gas W ∧
        CallsAgree o W ∧ Within (evmirSem o) (ethLibIn env gas) q code (· = call)) :
    ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → RunOk env gas call →
      ∀ obs, Shapes.Target.runWithIn env gas code call = some obs →
        (∃ W : World, W.Open ∧ Fits W ∧ RunWorld gas W ∧ Source.runIn W fuel c call = some obs) ∨
          Shapes.Inert call obs := by
  intro env hwf gas hgas call hv hok obs hrun
  obtain ⟨o, W, hW, hF, hR, hA, hwi⟩ := bytes env hwf gas hgas call hv hok
  rcases hwi call rfl obs hrun with h | h
  · left
    obtain ⟨obs0, h0⟩ := Option.isSome_iff_exists.mp (total W hW hF call hv)
    have hq := ((source o W hW hF hA).trans (backend o)) call hv obs0 h0
    rw [hq] at h
    cases h
    exact ⟨W, hW, hF, hR, h0⟩
  · exact Or.inr h

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.within_of_advancesQT_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_advancesQT_in

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.within_of_advancesQ_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_advancesQ_in

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.meets_ranIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_ranIn

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.calleeEntry_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calleeEntry_of

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.runs_of_checkXB_tab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runs_of_checkXB_tab

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.runs_of_checkXB_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runs_of_checkXB_open

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.tabWorld_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tabWorld_fits

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.assembly_of_checkXB_norm_tab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkXB_norm_tab

/-- info: 'SolidCore.Refinement.Solar.AssembleCallOpen.open_equiv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms open_equiv_run

end SolidCore.Refinement.Solar.AssembleCallOpen
