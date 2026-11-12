import SolidCore.Refinement.Solar.Counter.Assembly
import SolidCore.Refinement.Evm.WideStorageAt
import SolidCore.Refinement.Solar.Counter.LoweringAt

/-!
# counter: solar's final EVM IR to its bytecode on EthLib, from any storage

The assembly stage of Counter (Assembly.lean) on `scopeAt` (SpecAt.lean): every call of
`inc(d)` with no value from any storage `σ`, whose slot 0 holds any word `x`, so both the write
of `x + d` and the Panic(0x11) revert on overflow are reached.

* `target_run_at`: EthLib runs `code` on every such call to `expectedAt σ d`, every opcode
  stepped by EthLib's program logic from pc 0 with 10M gas (`counter_one_at`): SLOAD reads
  `σ`'s slot 0 from the call's state (`getStorage_preState_toBeBytes`), the overflow branch is
  decided by whether `x + d` fits, SSTORE writes `x + d` over `σ` at its price, and the final
  storage is read slot by slot (`storage_after_at`); `run_of_postS_at` turns the frame into
  `Target.run`.
* `evmir_run_at`: SolarTV's EVM IR semantics runs `evm5` on the same calls to `expectedAt σ d`,
  from the source stage's MIR run from `σ` (`mir_run_at`) and the backend stages, which hold on
  every call.
* `stageAt`: the stage, under every oracle, from the generic theorem for every program and code
  the checker accepts (`Assemble.stage_of_check`, AssembleSim.lean) at the same `check_ok` as
  `stage`: it is `stageAnyStorage` (Assembly.lean), whose scope is `scopeAt` unfolded.
  `stageAt_run` proves the same stage from `evmir_run_at` and `target_run_at`, as a cross-check.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide

section TargetAt

open EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

open EthLib.Execution.State in
/-- The storage after SLOAD's and SSTORE's reads and the write of `v` to slot 0, from the
storage of any call: `v` in slot 0, the call's word in every other slot. -/
theorem storage_after_at (code : ByteArray) (c : Call) (k1 k2 : Bytes32) (v : U256) (slot : Nat) :
    ((writeOf (((Target.preState code c).recordStorageRead (Target.address selfAddress) k1).recordStorageRead
      (Target.address selfAddress) k2) (Target.address selfAddress) (U256.toBeBytes (BitVec.ofNat 256 0)) v).getStorage
        (Target.address selfAddress) (Target.storageKey slot)).toNat =
      if slot % 2 ^ 256 = 0 then v.toNat else slotValue c.storage slot := by
  rw [getStorage_writeOf_any, getStorage_recordStorageRead, getStorage_recordStorageRead]
  by_cases hz : slot % 2 ^ 256 = 0
  · have hk : Target.storageKey slot = U256.toBeBytes (BitVec.ofNat 256 0) :=
      (storageKey_eq_toBeBytes slot _).2 (by simpa using hz)
    simp only [hk, and_self, ↓reduceIte, hz]
  · have hk : Target.storageKey slot ≠ U256.toBeBytes (BitVec.ofNat 256 0) := fun h =>
      hz (by simpa using (storageKey_eq_toBeBytes slot _).1 h)
    simp only [hk, and_false, ↓reduceIte, hz]
    exact getStorage_preState code c slot

/-- A word read from storage plus `d`, when the sum fits, as a number. -/
theorem toNat_ofNat_add {x : Nat} {d : U256} (h : x + d.toNat < 2 ^ 256) :
    (BitVec.ofNat 256 x + d).toNat = x + d.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x) (by omega),
    Nat.mod_eq_of_lt h]

open Lean.Parser.Tactic in
/-- Steps one opcode of a path of `inc` from any storage: SLOAD of the call's storage (a cold
key: no key is warm at the frame's start), SSTORE after it, STOP with the storage after the
read and the write (`hval`: the stored sum as a number), REVERT with Panic(0x11), and every other
opcode as `wide_one_s`. -/
syntax "counter_one_at" " [" simpLemma,* "]" " [" simpLemma,* "]" ident ident ident ident : tactic

macro_rules
  | `(tactic| counter_one_at [$ls,*] [$ns,*] $hf $hstat $htgt $hval) => `(tactic| ((try unfold Spec) <;> first
      | (refine' Triple.seq (sload (cold := true) (by decide) ?lt ?op ?cold ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case cold => simp [Substate.empty]
         case gas => simp only [ite_true]; omega) <;>
        (try simp only [$htgt:ident, getStorage_preState_toBeBytes, BitVec.toNat_ofNat,
          Nat.zero_mod, Bool.true_eq, ↓reduceIte, Nat.reduceSub]) <;> evm_tidy
      | (refine' Triple.seq (sstore (by decide) (by decide) ?lt ?op $hstat rfl ?stip ?gas
          (setStorage_ok _ _ ?acc)) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case stip => simp only [CALL_STIPEND]; omega
         case gas => exact Nat.le_trans (sstoreCost_le _ _ _ _) (by omega)
         case acc => simp only [getAccountOptional_recordStorageRead, $htgt:ident]
                     exact account_preState _ _) <;> evm_tidy
      | (refine stop_postS ?lt ?op ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case succ => rfl
         case out => rfl
         case store => intro slot; rw [$htgt:ident, storage_after_at, $hval:ident]; rfl)
      | (refine revert_postS (by decide) ?lt ?op ?gas rfl ?out rfl
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case out => simp only [Verify.panic, Verify.word]; decide +kernel)
      | wide_one_s [$ls,*] [$ns,*] $hf $hstat $htgt))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- EthLib runs solar's bytecode on every call of `inc(d)` from any storage `σ` to the
observable `expectedAt σ d`: when `x + d` fits, with `x` the word SLOAD reads from `σ`'s slot 0,
the write of `x + d` over `σ`; otherwise the revert with Panic(0x11), every opcode stepped by
EthLib's program logic from pc 0 with 10M gas and the overflow branch decided by the sum. -/
theorem target_run_at (d : U256) (σ : List (Nat × Nat)) :
    Target.run code { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) := by
  refine run_of_postS_at code incSelector [d] σ _ (by unfold expectedAt; split <;> rfl) ?_ ?_
  · intro h slot
    unfold expectedAt at h ⊢
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at h
      cases h
    · rfl
  intro msg hv hd hstat htgt
  simp only [callAt]
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  have hlt := slotValue_lt σ 0
  have hw := d.isLt
  simp only [incSelector] at hd
  by_cases hof : slotValue σ 0 + d.toNat < 2 ^ 256
  · have he : expectedAt σ d = ⟨true, [], [], fun slot =>
        if slot % 2 ^ 256 = 0 then slotValue σ 0 + d.toNat else slotValue σ slot⟩ := by
      simp only [expectedAt, hof, ↓reduceIte]
    have hval := toNat_ofNat_add hof
    rw [he]
    repeat counter_one_at [code, runtimeNat, runtimeSize, incSelector] [hd, hv] hfork hstat htgt hval
  · have he : expectedAt σ d = ⟨false, Verify.panic 0x11, [], slotValue σ⟩ := by
      simp only [expectedAt, hof, ↓reduceIte]
    rw [he]
    repeat counter_one_at [code, runtimeNat, runtimeSize, incSelector] [hd, hv] hfork hstat htgt hfork

end TargetAt

/-- SolarTV's EVM IR semantics runs Counter's final EVM IR on every call of `inc(d)` from any
storage `σ`, under every oracle, to `expectedAt σ d`: the source stage's MIR run from `σ`
(`mir_run_at`) through the backend stages, which hold on every call. -/
theorem evmir_run_at (o : SolarTV.Machine.Oracle) (d : U256) (σ : List (Nat × Nat)) :
    (SolarTV.evmirSem o).run SolarTV.Export.Counter.evm5
        { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) :=
  SolarTV.Milestone.Counter.counter_mir_to_evmir o _ trivial _ (mir_run_at o d σ)

/-- **The assembly stage of Counter from any storage**: EVM IR to bytecode on EthLib, on every
call of `scopeAt`, under every oracle. It is the generic theorem at `check_ok`
(`stageAnyStorage`), since every call of `scopeAt` has no value. -/
theorem stageAt (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scopeAt :=
  stageAnyStorage o

/-- The same stage from any storage proved directly, by running both sides to the same observable
(`evmir_run_at` and `target_run_at`), as a cross-check of `stageAt`. -/
theorem stageAt_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scopeAt := by
  intro call hc obs hrun
  obtain ⟨d, σ, rfl⟩ := scopeAt_callOf hc
  rw [evmir_run_at o d σ] at hrun
  cases hrun
  exact target_run_at d σ

/-- info: 'SolidCore.Refinement.Solar.Counter.stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAt

/-- info: 'SolidCore.Refinement.Solar.Counter.stageAt_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAt_run

/-- info: 'SolidCore.Refinement.Solar.Counter.target_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_run_at

end SolidCore.Refinement.Solar.Counter
