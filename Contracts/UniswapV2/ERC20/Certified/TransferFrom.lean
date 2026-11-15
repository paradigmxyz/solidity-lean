import Contracts.UniswapV2.ERC20.Certified.Transfer

-- Untrusted proof script: the kernel checks it.

/-!
# UniswapV2ERC20.transfer certified from every caller

`Transfer.certified` states `Shapes.Certified` at the interface's one caller 0x2000, and
`Transfer.certified_any_caller` adds the bytes' resources from any caller. This module states the
whole certified statement **for every caller** `a` (below `2 ^ 160`, not the contract itself,
`a = to` included), over SolidCore's run of the call sent by `a` (`solidCoreFrom a`) and EthLib's
run of the exact bytes from `a` (`Final.Target.runWithFrom a`):

* `CertifiedAt a`: `Shapes.Certified`'s four obligations with the caller `a` on both sides
  (equivalence at every gas below `2 ^ 256`, termination with an allowed status, the specification,
  resources from the bound on). `certifiedAt_callerAddress`: at 0x2000 with an inhabited
  precondition it is `Shapes.Certified` itself.
* `SeqPostAt a`, `TargetPostAt a`, `ScopeAt a`, `ValidInAt a`: the slice's `SeqPost`,
  `TargetPost`, `Scope`, `ValidIn` with the caller `a` (`targetPostAt_callerWord`: at
  0x2000 they are the slice's, by `rfl`).
* `symTree` (`symErase_eq`, `kernel_rfl`): SolidCore's checked `transfer` erased with
  `msg.sender` symbolic (`Generic.eraseFnSym`), by parts; `seq_from`: its result from caller
  `a` is `SeqPostAt a`'s, with no hash premise.
* `within_of_checkXLFrom`: the checker with contexts and gas, at every gas, from any account:
  a result of the bytes is the final EVM IR's or a failure with no effect.
* `certified_from`: **the statement**. `validInAt_inhabited`: for every caller whose own
  footprint premise holds (`ScopedSep (transferFootprint 1 a a)`: Keccak-256 of `(a, 1)` is at
  least `2 ^ 128`) the valid calls are inhabited, by the self-transfer; at 0x2000 it holds by the
  kernel (`validInAt_callerWord_inhabited`).

Valid calls still ask the storage to write the constructor's slot (`Generic.Covers deployed`),
as every generic-stage statement does.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Generic SolidCore.Refinement.Shapes SolidCore.Spec SolidCore.Refinement.Solar
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx SolidCore.Refinement.Solar.AssembleCtxGas
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey upd be32 transferLog errorData
  addMsg subMsg Allowed wsub modW ite01_modW lt_wsub_iff add_mod_lt_iff wsub_of_le bytes_err
  errorData_add_lt errorData_sub_lt bytes_word errBytes c1 balKey_mod balKey_mod' slotValue_mod
  transferTopic balanceSlot fuel)

/-! ## The bytes against the final EVM IR at every gas, from any account -/

/-- A failed run from any account leaves the storage as it was and logs nothing. -/
theorem runWithFrom_failure {a gas : Nat} {code : ByteArray} {call : Call} {obs : Observable}
    (h : Final.Target.runWithFrom a gas code call = some obs) (hf : obs.success = false) :
    obs.storage = slotValue call.storage ∧ obs.logs = [] := by
  unfold Final.Target.runWithFrom at h
  split at h
  · cases h
  · cases h
    simp only at hf
    simp [hf]

/-- The frame of a call from the account `a` with `gas` gas, from a state related to the call's
storage. -/
theorem rel_startFrom (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) (gas : Nat) {st' : State.TransactionState}
    (ss' : Substate)
    (h : ¬ ((Target.messageFromWith a gas code call).shouldTransferValue = true ∧
        (Target.messageFromWith a gas code call).value ≠ 0) → st' = Target.preStateFrom a code call)
    (hm : ((Target.messageFromWith a gas code call).shouldTransferValue = true ∧
        (Target.messageFromWith a gas code call).value ≠ 0) →
      (Target.preStateFrom a code call).moveEther .fusaka (Target.messageFromWith a gas code call).caller
        (Target.messageFromWith a gas code call).currentTarget
        (Target.messageFromWith a gas code call).value = .ok st') :
    Rel (Target.messageFromWith a gas code call) ss' st' ss' (SolarTV.Machine.State.initial call) := by
  have R0 := rel_initialFrom a gas hAB code call
  by_cases htr : (Target.messageFromWith a gas code call).shouldTransferValue = true ∧
      (Target.messageFromWith a gas code call).value ≠ 0
  · have hmove := hm htr
    have hn : ((Target.preStateFrom a code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
      rw [getAccount_preStateFrom_self a hAB]; simp
    exact ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
      (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, ⟨[], by simp, .nil⟩⟩
  · obtain rfl := h htr
    exact ⟨R0.storage, R0.account, ⟨[], by simp, .nil⟩⟩

open SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at every gas, from any account** `a` but the contract's: the
`within_of_checkXL` argument with `Target.messageFromWith a` and `Target.preStateFrom a`. -/
theorem within_of_checkXLFrom {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXL F p code cx = true) (a : Nat)
    (hAB : Target.address selfAddress ≠ Target.address a) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → AssembleLoop.OracleOkAt a o)
    (he : cx.base.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r) (gas : Nat) (obs : Observable)
    (hrun : Final.Target.runWithFrom a gas code call = some obs) :
    obs = SolarTV.Machine.observe call r.2 r.1 ∨
      (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) := by
  obtain ⟨G, hseg, hcount, hneed0, hF0⟩ := globXL_of_checkXL hc
  cases hs : obs.success
  · exact Or.inr ⟨rfl, runWithFrom_failure hrun hs⟩
  left
  unfold Final.Target.runWithFrom at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hs
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Target.messageFromWith a gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_messageFromWith a gas code call) hpm hok
  simp only at hrf
  set msg := Target.messageFromWith a gas code call with hmsg
  have hcode : msg.code = code := rfl
  have R := rel_startFrom a hAB code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hsim := run_simXL (msg := msg) (ss0 := ss') (a := a) G rfl (by simp [msg, Target.messageFromWith])
    rfl rfl rfl ho rfl (fun h => (he h).2) (fun h => (he h).1) n 0 [] [] _ 0 .empty
    (gas + gasBoundL cx.base n) st' ss'
    ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame, Nat.zero_le _,
      fun _ => ⟨by simp [hn0, hneed0], by simp⟩, SR.nil _ _,
      ⟨by rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]; exact hseg,
        by
          rw [hm0]
          show 22100 * (n * bmax cx.base) + (memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0) ≤ _
          have : memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0 ≤ memoryGasCost cx.base.top := by
            rw [hsame.2.2]; exact Nat.sub_le _ _
          unfold gasBoundL; omega,
        by simp, memRel_initial⟩,
      fun _ => ⟨0, hcount, hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
        by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩ R r hit
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas (gasBoundL cx.base n)
  rcases r with ⟨halt, sF⟩
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := SpecG.low hsim hp within hrf hok
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
  clear herr hout hst hsim hit
  generalize SolarTV.Machine.observe call sF halt = X at *
  have hsucc : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout' hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc, hout', ?_, ?_⟩
    · rw [hsucc]
      cases hs : success
      · simp [hok, hs] at hsucc
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc]
      cases hs : success
      · simp [hok, hs] at hsucc
      · simp only [ite_true]
        exact (hst' hs).2 slot

/-! ## The specification, with the caller a parameter -/

/-- The debited state: the caller `a`'s balance less `v`. -/
def debitAt (a : Nat) (s : Nat → Nat) (v : Nat) : Nat → Nat := upd s (balKey a) (s (balKey a) - v)

/-- The source's storage updates from the caller `a`, in order: the debit, then the credit of `to`
reading the debited state. -/
def seqStoreAt (a : Nat) (s : Nat → Nat) (dst v : Nat) : Nat → Nat :=
  upd (debitAt a s v) (balKey dst) (debitAt a s v (balKey dst) + v)

/-- **What the source does** on `transfer(to, v)` sent by `a` from `σ` (the slice's `SeqPost` with
the caller `a`). -/
def SeqPostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (obs.success = true ↔
      (v ≤ slotValue σ (balKey a) ∧ debitAt a (slotValue σ) v (balKey dst) + v < 2 ^ 256)) ∧
    (obs.success = true → obs.storage = seqStoreAt a (slotValue σ) dst v ∧
      obs.logs = [transferLog a dst v] ∧ obs.output = be32 1) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey a) then addMsg else subMsg))

/-- **The scoped premise of a call sent by `a`**: Keccak-256 separated on the preimages of `a`'s and
the recipient's `balanceOf` slots, and nothing else. -/
def ScopeAt (a : Nat) (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    ScopedSep (transferFootprint balanceSlot a dst)

/-- **The target's postcondition for the caller `a`** (the slice's `TargetPost` with the caller
`a`): `a ≠ to` succeeds iff `s[a] ≥ v` and `s[to] + v < 2 ^ 256`, then debits and credits; `a = to`
succeeds iff `s[a] ≥ v` and leaves the storage as it was; a success logs `Transfer(a, to, v)`,
returns `true` and changes no slot outside the footprint; a failure reverts with the source's
revert data, no log, no change. -/
def TargetPostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (a ≠ dst →
      (obs.success = true ↔
        v ≤ slotValue σ (balKey a) ∧ slotValue σ (balKey dst) + v < 2 ^ 256) ∧
      (obs.success = true → obs.storage (balKey a) = slotValue σ (balKey a) - v ∧
        obs.storage (balKey dst) = slotValue σ (balKey dst) + v)) ∧
    (a = dst →
      (obs.success = true ↔ v ≤ slotValue σ (balKey a)) ∧
      (obs.success = true → obs.storage = slotValue σ)) ∧
    (obs.success = true → obs.logs = [transferLog a dst v] ∧ obs.output = be32 1 ∧
      ∀ n, n % 2 ^ 256 ≠ balKey a → n % 2 ^ 256 ≠ balKey dst → obs.storage n = slotValue σ n) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey a) then addMsg else subMsg))

/-- **The valid calls sent by `a` with their premise.** -/
def ValidInAt (a : Nat) (call : Call) : Prop := Valid Slice.Gen.deployed call ∧ ScopeAt a call

/-- At the interface's caller the definitions are the slice's. -/
theorem seqPostAt_callerWord : SeqPostAt Generic.callerWord = Slice.SeqPost := rfl
theorem targetPostAt_callerWord : TargetPostAt Generic.callerWord = Slice.TargetPost := rfl
theorem validInAt_callerWord : ValidInAt Generic.callerWord = Slice.ValidIn := rfl
theorem callerAddress_eq_callerWord : callerAddress = Generic.callerWord := rfl

/-! ## SolidCore's transfer with a symbolic caller, by parts -/

/-- The caller's `balanceOf` slot word. -/
abbrev hC : WExpr := .hash .caller (.lit 1)
/-- The recipient's `balanceOf` slot word. -/
abbrev hT : WExpr := .hash (.arg 0) (.lit 1)
/-- The debited balance (wrapping subtraction). -/
abbrev eSub : WExpr := .bin .sub (.sinit hC) (.arg 1)
/-- The recipient's balance in the debited state. -/
abbrev eSel : WExpr := .sel (.bin .eq hT hC) eSub (.sinit hT)
/-- The credited balance (wrapping addition). -/
abbrev eAdd : WExpr := .bin .add eSel (.arg 1)
/-- SafeMath's `sub` test. -/
abbrev c2 : WExpr := .un .iszero (.bin .lt (.sinit hC) eSub)
/-- SafeMath's `add` test. -/
abbrev c3 : WExpr := .un .iszero (.bin .lt eAdd eSel)

/-- The success leaf: return `true`, the credit then the debit, `Transfer(caller, to, v)`. -/
def okLeaf : Tree :=
  .halt true (wordOBytes (.lit 1)) [(hT, eAdd), (hC, eSub)]
    [{ topics := [.lit transferTopic, .caller, .arg 0], data := wordOBytes (.arg 1) }]

/-- The erased tree of `transfer` with `msg.sender` symbolic. -/
def symTree : Tree :=
  .ite c1 (.halt false [] [] [])
    (.ite c2 (.ite c3 okLeaf (.halt false (errBytes addMsg) [] [])) (.halt false (errBytes subMsg) [] []))

/-- How SolidCore dispatches `transfer` and the stage erases it with a symbolic caller. -/
def symErase? : Option (Option (Nat × Option Tree)) :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => some ((c.core.findFunctionBySelector? 2835717307).map fun f =>
      (f.params.length, eraseFnSym (envOf c.core) fuel f))
  | .error _ => none

-- The erasure with a symbolic caller, by parts: the kernel's evaluation from the source text up.
kernel_rfl symErase_eq symErase? (some (some (2, some symTree))) using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-! ## Evaluating the parts at the caller `a` -/

set_option simprocs false

/-- The words `transfer(to, v)` sent by `a` reads from the storage `s`. -/
abbrev val (a : Nat) (s : Nat → Nat) (dst v : Nat) : Val := ⟨[dst, v], s, solHash, a⟩

/-- The tree's result on `transfer(to, v)` sent by `a` from `s`. -/
abbrev res (a : Nat) (s : Nat → Nat) (dst v : Nat) : Res := symTree.eval (val a s dst v)

section
variable {a : Nat} {s : Nat → Nat} {dst v : Nat}

theorem ev_caller (ha : a < 2 ^ 160) : WExpr.caller.eval (val a s dst v) = a := by
  simp only [WExpr.eval, Generic.wordSize]; exact modW (by omega)

theorem ev_hC (ha : a < 2 ^ 160) : hC.eval (val a s dst v) = balKey a := by
  simp only [hC, WExpr.eval.eq_8, Generic.wordSize, ev_caller ha]
  simp only [WExpr.eval, Generic.wordSize, modW (show 1 < 2 ^ 256 by decide)]
  exact modW (solHash_lt _ _)

theorem ev_arg0 (hto : dst < 2 ^ 160) : (WExpr.arg 0).eval (val a s dst v) = dst := by
  simp only [WExpr.eval, Generic.wordSize, List.getD_cons_zero]; exact modW (by omega)

theorem ev_arg1 (hv : v < 2 ^ 256) : (WExpr.arg 1).eval (val a s dst v) = v := by
  simp only [WExpr.eval, Generic.wordSize, List.getD_cons_succ, List.getD_cons_zero]; exact modW hv

theorem ev_hT (hto : dst < 2 ^ 160) : hT.eval (val a s dst v) = balKey dst := by
  simp only [hT, WExpr.eval.eq_8, Generic.wordSize, ev_arg0 hto]
  simp only [WExpr.eval, Generic.wordSize, modW (show 1 < 2 ^ 256 by decide)]
  exact modW (solHash_lt _ _)

variable (ha : a < 2 ^ 160) (hs : ∀ k, s k < 2 ^ 256) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256)
include ha hs hto hv

theorem ev_a : (WExpr.sinit hC).eval (val a s dst v) = s (balKey a) := by
  simp only [WExpr.eval.eq_6, Generic.wordSize, ev_hC ha]; exact modW (hs _)

theorem ev_b : (WExpr.sinit hT).eval (val a s dst v) = s (balKey dst) := by
  simp only [WExpr.eval.eq_6, Generic.wordSize, ev_hT hto]; exact modW (hs _)

theorem ev_sub : eSub.eval (val a s dst v) = wsub (s (balKey a)) v := by
  simp only [eSub, eval_bin, ev_a ha hs hto hv, ev_arg1 hv, BinOp.eval, wsub, Generic.wordSize, Nat.mod_mod]

theorem ev_sel : eSel.eval (val a s dst v) =
    if balKey dst = balKey a then wsub (s (balKey a)) v else s (balKey dst) := by
  simp only [eSel, WExpr.eval.eq_7, eval_bin, Generic.wordSize, ev_hT hto, ev_hC ha, BinOp.eval, ite01_modW,
    ev_sub ha hs hto hv, ev_b ha hs hto hv]
  by_cases h : balKey dst = balKey a <;> simp [h]

theorem ev_c1 : c1.eval (val a s dst v) = 0 := by
  simp only [c1, eval_bin, ev_arg0 hto, eval_lit, Generic.wordSize, modW (show 1461501637330902918203684832716283019655932542975 < 2 ^ 256 by decide),
    BinOp.eval, ite01_modW, Generic.wordSize]
  split_ifs <;> omega

theorem ev_c2 : c2.eval (val a s dst v) = if v ≤ s (balKey a) then 1 else 0 := by
  simp only [c2, WExpr.eval.eq_4, eval_bin, ev_a ha hs hto hv, ev_sub ha hs hto hv, BinOp.eval, UnOp.eval,
    ite01_modW, lt_wsub_iff (hs _) hv, Generic.wordSize]
  split_ifs <;> omega

theorem ev_sel_debit (hle : v ≤ s (balKey a)) :
    eSel.eval (val a s dst v) = debitAt a s v (balKey dst) := by
  rw [ev_sel ha hs hto hv, wsub_of_le (hs _) hle]
  simp only [debitAt, upd, balKey_mod]

theorem ev_c3 (hle : v ≤ s (balKey a)) :
    c3.eval (val a s dst v) = if debitAt a s v (balKey dst) + v < 2 ^ 256 then 1 else 0 := by
  have hd : debitAt a s v (balKey dst) < 2 ^ 256 := by
    rw [← ev_sel_debit ha hs hto hv hle]; exact WExpr.eval_lt _ _
  simp only [c3, eAdd, WExpr.eval.eq_4, eval_bin, ev_sel_debit ha hs hto hv hle, ev_arg1 hv, BinOp.eval,
    UnOp.eval, ite01_modW, Generic.wordSize, Nat.mod_mod, add_mod_lt_iff hd hv]
  split_ifs <;> omega

/-- The caller's balance does not cover `v`: SafeMath's `sub` reverts. -/
theorem res_sub (hle : ¬ v ≤ s (balKey a)) : res a s dst v = Slice.failRes s subMsg := by
  simp only [res, symTree, Tree.eval, ev_c1 ha hs hto hv, ev_c2 ha hs hto hv, if_neg hle, if_true,
    eq_self_iff_true, Bool.false_eq_true, if_false, Slice.failRes]
  rw [bytes_err _ _ errorData_sub_lt]

/-- The credit overflows: SafeMath's `add` reverts. -/
theorem res_add (hle : v ≤ s (balKey a)) (hov : ¬ debitAt a s v (balKey dst) + v < 2 ^ 256) :
    res a s dst v = Slice.failRes s addMsg := by
  simp only [res, symTree, Tree.eval, ev_c1 ha hs hto hv, ev_c2 ha hs hto hv, ev_c3 ha hs hto hv hle, if_pos hle,
    if_neg hov, one_ne_zero, if_true, eq_self_iff_true, Bool.false_eq_true, if_false, Slice.failRes]
  rw [bytes_err _ _ errorData_add_lt]

/-- The result of a success sent by `a`. -/
def okRes (a : Nat) (s : Nat → Nat) (dst v : Nat) : Res :=
  { success := true, output := be32 1, logs := [transferLog a dst v], store := seqStoreAt a s dst v }

/-- Otherwise the call succeeds: the debit, then the credit, the log and `true`. -/
theorem res_ok (hle : v ≤ s (balKey a)) (hov : debitAt a s v (balKey dst) + v < 2 ^ 256) :
    res a s dst v = okRes a s dst v := by
  simp only [res, symTree, Tree.eval, ev_c1 ha hs hto hv, ev_c2 ha hs hto hv, ev_c3 ha hs hto hv hle, if_pos hle,
    if_pos hov, one_ne_zero, if_true, eq_self_iff_true, if_false, okLeaf, okRes]
  congr 1
  case e_logs =>
    simp only [Log.eval, List.map_cons, List.map_nil, bytes_word, ev_arg1 hv, ev_arg0 hto, ev_caller ha, eval_lit,
      Slice.transferLog, Slice.transferTopic, Generic.wordSize,
      modW (show 100389287136786176327247604509743168900146139575972864366142685224231313322991 < 2 ^ 256 by decide)]
  case e_store =>
    funext n
    simp only [Writes.store, ev_hT hto, ev_hC ha, seqStoreAt, upd, Generic.wordSize]
    rw [show eAdd.eval (val a s dst v) = debitAt a s v (balKey dst) + v by
      simp only [eAdd, eval_bin, ev_sel_debit ha hs hto hv hle, ev_arg1 hv, BinOp.eval, Generic.wordSize,
        Nat.mod_mod]
      exact Nat.mod_eq_of_lt hov]
    rw [ev_sub ha hs hto hv, wsub_of_le (hs _) hle]
    by_cases h1 : n % 2 ^ 256 = balKey dst
    · rw [if_pos h1.symm, if_pos h1]
    · rw [if_neg (Ne.symm h1), if_neg h1]
      simp only [debitAt, upd]
      by_cases h2 : n % 2 ^ 256 = balKey a
      · rw [if_pos h2.symm, if_pos h2]
      · rw [if_neg (Ne.symm h2), if_neg h2]
  all_goals rw [bytes_word, eval_lit, Generic.wordSize, modW (show 1 < 2 ^ 256 by decide)]
end

/-- **The symbolic tree is `SeqPostAt a`'s source**, from any storage of words. -/
theorem tree_seq (a : Nat) (ha : a < 2 ^ 160) (s : Nat → Nat) (hs : ∀ k, s k < 2 ^ 256) (dst v : Nat)
    (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256) :
    ((res a s dst v).success = true ↔
      (v ≤ s (balKey a) ∧ debitAt a s v (balKey dst) + v < 2 ^ 256)) ∧
    ((res a s dst v).success = true → (res a s dst v).store = seqStoreAt a s dst v ∧
      (res a s dst v).logs = [transferLog a dst v] ∧ (res a s dst v).output = be32 1) ∧
    ((res a s dst v).success = false → (res a s dst v).store = s ∧ (res a s dst v).logs = [] ∧
      (res a s dst v).output = errorData (if v ≤ s (balKey a) then addMsg else subMsg)) := by
  by_cases hle : v ≤ s (balKey a)
  · by_cases hov : debitAt a s v (balKey dst) + v < 2 ^ 256
    · rw [res_ok ha hs hto hv hle hov]; simp [okRes, hle, hov]
    · rw [res_add ha hs hto hv hle hov]; simp [Slice.failRes, hle, hov]
  · rw [res_sub ha hs hto hv hle]; simp [Slice.failRes, hle]

set_option simprocs true

/-! ## SolidCore's runs from the caller `a` -/

/-- **SolidCore's run of a valid call sent by `a` is the symbolic tree's result at `a`.** -/
theorem run_tree {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {a : Nat} (ha : a < 2 ^ 160)
    {σ : List (Nat × Nat)} {dst v : Nat}
    (hcov : Generic.Covers Slice.Gen.deployed σ) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256) :
    (solidCoreFrom a fuel).run c (transferCall σ dst v) = some (res a (slotValue σ) dst v).obs := by
  obtain ⟨⟨d, hd⟩, -⟩ := Slice.facts hc
  have hmap := symErase_eq
  simp only [symErase?, hc, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact source_run_from a ha hd hcov (by decide) hf hT [dst, v] (by simp [hlen]) (by simp; omega)

/-- **`SeqPostAt a` of every SolidCore run of a valid call sent by `a`**: no premise. -/
theorem meets_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160) :
    Meets (solidCoreFrom a fuel) c (Valid Slice.Gen.deployed) (SeqPostAt a) := by
  rintro _ ⟨σ, dst, v, hcov, hto, hv, rfl⟩ obs hrun
  rw [run_tree hc ha hcov hto hv, Option.some.injEq] at hrun
  subst hrun
  intro σ' dst' v' heq hto' hv'
  obtain ⟨rfl, rfl, rfl⟩ := Slice.transferCall_inj (by omega) hv (by omega) hv' heq
  exact tree_seq a ha (slotValue σ) (fun k => Generic.slotValue_lt σ k) dst v hto hv

/-- **The target's postcondition for the caller `a` from the source's, under the call's scope.** -/
theorem targetPostAt_of_seq {a : Nat} (ha : a < 2 ^ 160) {call : Call} {obs : Observable}
    (h : SeqPostAt a call obs) (hs : ScopeAt a call) : TargetPostAt a call obs := by
  intro σ dst v hc hto hv
  obtain ⟨hsucc, hok, hfail⟩ := h σ dst v hc hto hv
  have hsep := hs σ dst v hc hto hv
  have hlt : ∀ x, balKey x < 2 ^ 256 := fun x => solHash_lt x balanceSlot
  have hdeb_ne : a ≠ dst → debitAt a (slotValue σ) v (balKey dst) = slotValue σ (balKey dst) := by
    intro hne
    have hk : balKey a ≠ balKey dst :=
      (transfer_slots hsep (by decide) (by omega) (by omega)).1 hne
    simp only [debitAt, upd, Nat.mod_eq_of_lt (hlt dst)]
    rw [if_neg (Ne.symm hk)]
  refine ⟨fun hne => ?_, fun heq => ?_, fun hsc => ?_, hfail⟩
  · have hk : balKey a ≠ balKey dst :=
      (transfer_slots hsep (by decide) (by omega) (by omega)).1 hne
    have hd := hdeb_ne hne
    refine ⟨by rw [hsucc, hd], fun hsc => ?_⟩
    obtain ⟨hst, -, -⟩ := hok hsc
    rw [hst]
    constructor
    · simp [seqStoreAt, upd, debitAt, balKey_mod', hk, Ne.symm hk]
    · simp only [seqStoreAt, upd, balKey_mod, ↓reduceIte]
      rw [hd]
  · subst heq
    have hd : debitAt a (slotValue σ) v (balKey a) = slotValue σ (balKey a) - v := by
      simp [debitAt, upd, balKey_mod']
    refine ⟨?_, fun hsc => ?_⟩
    · rw [hsucc, hd]
      have hlt' : slotValue σ (balKey a) < 2 ^ 256 := Generic.slotValue_lt σ _
      exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
    · obtain ⟨hst, -, -⟩ := hok hsc
      have hle := (hsucc.mp hsc).1
      rw [hst]
      funext n
      by_cases h1 : n % 2 ^ 256 = balKey a
      · simp only [seqStoreAt, upd, h1, ↓reduceIte]
        rw [hd, ← Slice.slotValue_mod σ n, h1]
        omega
      · simp only [seqStoreAt, debitAt, upd, if_neg h1]
  · obtain ⟨hst, hlog, hout⟩ := hok hsc
    refine ⟨hlog, hout, fun n h1 h2 => ?_⟩
    rw [hst]
    simp only [seqStoreAt, debitAt, upd, if_neg h1, if_neg h2]

/-- **`TargetPostAt a` of every SolidCore run of a valid call sent by `a` whose premise holds.** -/
theorem meets_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160) :
    Meets (solidCoreFrom a fuel) c (ValidInAt a) (TargetPostAt a) :=
  fun call h obs hrun => targetPostAt_of_seq ha (meets_seq hc a ha call h.1 obs hrun) h.2

/-- **SolidCore halts on every valid call sent by `a`**, with an allowed status. -/
theorem terminates {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160) :
    Terminates (solidCoreFrom a fuel) c (ValidInAt a) Allowed := by
  rintro _ ⟨⟨σ, dst, v, hcov, hto, hv, rfl⟩, -⟩
  refine ⟨_, run_tree hc ha hcov hto hv, ?_⟩
  have hs := fun k => Generic.slotValue_lt σ k
  by_cases hle : v ≤ slotValue σ (balKey a)
  · by_cases hov : debitAt a (slotValue σ) v (balKey dst) + v < 2 ^ 256
    · rw [res_ok ha hs hto hv hle hov]; exact Or.inl rfl
    · rw [res_add ha hs hto hv hle hov]; exact Or.inr (Or.inr rfl)
  · rw [res_sub ha hs hto hv hle]; exact Or.inr (Or.inl rfl)

/-! ## The bytes from the caller `a` -/

open SolarTV.Export.UniswapV2ERC20 in
/-- **Equivalence from the caller `a`, at every gas**: every result of the exact bytes run from `a` on
a valid call is SolidCore's result of the call sent by `a`, or a failure with no effect. -/
theorem equiv_from {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160)
    (hne : a ≠ selfAddress) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, Valid Slice.Gen.deployed call → ∀ obs,
      Final.Target.runWithFrom a gas Certified.code call = some obs →
        (solidCoreFrom a fuel).run c call = some obs ∨ Inert call obs := by
  intro gas _ call hv obs hrun
  have hv' := Certified.valid_sub call hv
  have hsel := Certified.selector_of call hv'
  have hdep := SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy.deploy_eq
  simp only [SourceMir.deploy?, hc] at hdep
  obtain ⟨_, hdd⟩ := Wide.deployedAt_of hdep
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (CtxGas.guard_ends (Shapes.oracleFrom a) call hsel)
  obtain ⟨obs0, h0⟩ := Option.isSome_iff_exists.mp
    (Generic.definedFrom a ha hdd (SourceMirFrom.checkFrom_ok hc) call hv')
  have hm := SourceMirFrom.transfer_stage_from a ha (Shapes.oracleFrom a) (Certified.fromOk_oracleFrom ha)
    hc call hv' obs0 h0
  have h4 := AnyCaller.stages_from a call (AnyCaller.transfer_scope hsel) obs0 hm
  have hq := evmir_run_of_iterate ((CtxGas.guard_run (Shapes.oracleFrom a) call hsel).trans hr)
  rw [AssembleCtx.sem_norm] at hq
  have heq : obs0 = Machine.observe call r.2 r.1 := by
    have h4' : (evmirSem (Shapes.oracleFrom a)).run CtxGas.prog call = some obs0 := h4
    rw [h4'] at hq
    exact Option.some.inj hq
  rcases within_of_checkXLFrom CtxGas.check_ok a (address_ne_self ha hne) (Shapes.oracleFrom a)
      (fun _ => Shapes.oracleFrom_ok ha) (fun h => absurd h (by simp [CtxGas.reads_false])) call CtxGas.N r hr
      gas obs hrun with e | e
  · exact Or.inl (by rw [e, ← heq]; exact h0)
  · exact Or.inr e

/-! ## The statement -/

/-- **`Shapes.Certified`'s obligations with the caller `a` on both sides**: equivalence at every gas
of EthLib's run of `code` from `a` with SolidCore's run of the call sent by `a` (or a failure with
no effect), termination with an allowed status, the specification of every source result, and the
source's result exactly from `G` gas on. -/
structure CertifiedAt (a fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (code : ByteArray)
    (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop) (G : Nat) : Prop where
  equiv : ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs,
    Final.Target.runWithFrom a gas code call = some obs →
      (solidCoreFrom a fuel).run c call = some obs ∨ Inert call obs
  terminates : Terminates (solidCoreFrom a fuel) c Valid Allowed
  meets : Meets (solidCoreFrom a fuel) c Valid Post
  resources : ∀ call, Valid call → G < 2 ^ 64 ∧
    ∀ gas, G ≤ gas → gas < 2 ^ 256 → Final.Target.runWithFrom a gas code call = (solidCoreFrom a fuel).run c call

/-- At 0x2000, with an inhabited precondition, `CertifiedAt` is `Shapes.Certified`. -/
theorem CertifiedAt.certified {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {V : Call → Prop} {A P : Call → Observable → Prop} {G : Nat}
    (h : CertifiedAt callerAddress fuel c code V A P G) (inh : ∃ call, V call) :
    Certified (solidCore fuel) c code V A P (fun _ => G) where
  inhabited := inh
  equiv := fun gas hg call hv obs hrun => by
    rw [← Final.Target.runWithFrom_callerAddress] at hrun
    exact h.equiv gas hg call hv obs hrun
  terminates := h.terminates
  meets := h.meets
  resources := fun call hv => by
    refine ⟨(h.resources call hv).1, fun gas h1 h2 => ?_⟩
    rw [← Final.Target.runWithFrom_callerAddress]
    exact (h.resources call hv).2 gas h1 h2

/-- **UniswapV2ERC20.transfer is certified from every caller**: for every account `a < 2 ^ 160` other
than the contract, on every call of `transfer(dst, v)` sent by `a` (`dst = a` included) with
well-formed calldata, no value and any storage writing the constructor's slot, whose scoped hash
premise `ScopedSep (transferFootprint 1 a dst)` holds, the exact runtime bytes run from `a` behave as
SolidCore's checked source run by `a` (at every gas, and exactly from 8199112 gas on), which ends
with an allowed status and meets the target's postcondition for `a`. -/
theorem certified_from : ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      CertifiedAt a fuel c Certified.code (ValidInAt a) Allowed (TargetPostAt a) 8199112 := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  refine ⟨c, hc, fun a ha hne => ⟨fun gas hg call hv => equiv_from hc a ha hne gas hg call hv.1,
    terminates hc a ha, meets_target hc a ha, fun call hv => ?_⟩⟩
  have h := Certified.resources_any_caller hc a ha hne call (Certified.valid_sub call hv.1)
  rw [SolarTV.Export.UniswapV2ERC20.CtxGas.G_eq] at h
  exact h

/-- The valid calls sent by `a` are inhabited whenever `a`'s own footprint premise holds (the
self-transfer of 0). -/
theorem validInAt_inhabited (a : Nat) (ha : a < 2 ^ 160)
    (h : ScopedSep (transferFootprint balanceSlot a a)) : ∃ call, ValidInAt a call :=
  ⟨transferCall Slice.σ0 a 0, ⟨Slice.σ0, a, 0, Slice.covers_σ0, ha, by decide, rfl⟩,
    fun σ dst v heq hto hv => by
      obtain ⟨-, rfl, -⟩ := Slice.transferCall_inj (by omega) (by decide) (by omega) hv heq
      exact h⟩

/-- At 0x2000 they are inhabited, by the kernel's Keccak-256. -/
theorem validInAt_callerWord_inhabited : ∃ call, ValidInAt Generic.callerWord call :=
  Slice.valid_inhabited

/-- **The instance at 0x2000 is the fixed-caller statement**: `certified_from` at `callerAddress`
gives `Shapes.Certified` with the slice's `ValidIn` and `TargetPost`. -/
theorem certified_at_callerAddress : ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
    Certified (solidCore fuel) c Certified.code Slice.ValidIn Allowed Slice.TargetPost (fun _ => 8199112) := by
  obtain ⟨c, hc, h⟩ := certified_from
  exact ⟨c, hc, (h callerAddress (by decide) (by decide)).certified validInAt_callerWord_inhabited⟩

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom.certified_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_from

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom.certified_at_callerAddress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_at_callerAddress

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom.within_of_checkXLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_checkXLFrom

end SolidCore.Spec.UniswapV2.ERC20.CertifiedFrom
