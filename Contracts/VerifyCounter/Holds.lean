import Contracts.VerifyCounter.Mir
import Contracts.Counter.Verify
import SolidCore.Refinement.Generic.Stage
import SolidCore.Refinement.Evm.WideStorage

/-!
# solar-verify's spec of Counter holds of solar's first lowered MIR, and of the final EVM IR

`holds_stage0`: `Final.Holds` of `VerifyCounter.spec` (`Contracts/Counter/Verify.lean`, the
NatSpec of solar's `crates/verify/examples/Counter.sol`: the getters, `increment`, `bump`'s loop
and `max`, the invariant `count <= limit`, nothing payable) for `stage0`, solar's first lowered
MIR of that contract, on every call of the spec: every function, every clean argument word, any
value, any storage meeting the invariant and the precondition, under every oracle. It reads the
per-function theorems of `Mir.lean` and `Bump.lean` through the call's ABI encoding.

`holds_of_certified`: the same of every program whose ends stage0 matches with agreeing ends
(`Certified … p stage0`), such as the final EVM IR through solar-tv's backend stages read
backwards (`verify_counter_certified_back`).
-/

namespace SolidCore.Refinement.Solar.VerifyCounter.Mir

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final EthLib.Base
open SolarTV.Milestone.VerifyCounter.Bump SolidCore.Refinement.Solar.VerifyCounter
open SolarTV.Export.Counter (stage0)

/-! ## Return data -/

theorem byte_toNat (v : EvmRules.Word) (i : Nat) (hi : i < 32) :
    (SolarTV.Memory.byte v i).toNat = v.toNat / 256 ^ (31 - i) % 256 := by
  unfold SolarTV.Memory.byte
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bytes_toNat (len n : Nat) :
    (List.range len).map (fun i => (n / 256 ^ (len - 1 - i)) % 256) =
      (natToBytes len n).map (·.toNat) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    rw [natToBytes_succ, List.map_append, ← ih, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · simp

/-- The word a store at 0 wrote, read back as its 32 bytes: its ABI word. -/
theorem read_store0 (m : Mem) (v : EvmRules.Word) :
    ((m.store 0 v).read 0 32).map BitVec.toNat = SolidCore.Verify.word v.toNat := by
  have e : ((m.store 0 v).expand 0 32).read 0 32 = (m.store 0 v).read 0 32 := by
    unfold Mem.expand; split <;> rfl
  rw [← e, SolidCore.Verify.word, ← bytes_toNat]
  simp only [Mem.read, Mem.expand, Mem.store, List.map_map]
  simp only [show (32 = 0) = False from by decide, ite_false]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, Nat.zero_add, Nat.zero_le, true_and, hi, ite_true, Nat.sub_zero]
  rw [byte_toNat v i hi]

/-! ## The call's words -/

theorem selector_of {sel : Nat} (hsel : sel < 2 ^ 32) {args : List Nat}
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (v : Nat) (σ : List (Nat × Nat)) :
    EvmRules.Evm.shr 224 (calldataWord { calldata := Abi.calldata sel args, callvalue := v, storage := σ } 0) =
      BitVec.ofNat 256 sel :=
  (Generic.callFacts sel hsel args hargs σ).selector

theorem arg_of {sel : Nat} (hsel : sel < 2 ^ 32) {args : List Nat}
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (v : Nat) (σ : List (Nat × Nat)) (i : Nat) (hi : i < args.length)
    (hi2 : i < 2) :
    calldataWord { calldata := Abi.calldata sel args, callvalue := v, storage := σ }
      (BitVec.ofNat 256 (4 + 32 * i)) = BitVec.ofNat 256 (args.getD i 0) := by
  have h := (Generic.callFacts sel hsel args hargs σ).args i hi
    (by simp only [Generic.wordSize]; omega)
  apply BitVec.eq_of_toNat_eq
  have hlt : args.getD i 0 < 2 ^ 256 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hargs _ (List.getElem_mem hi)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine h.trans ?_
  simp only [Generic.WExpr.eval, Generic.wordSize]
  exact Nat.mod_eq_of_lt hlt


/-! ## Runs and what they show -/

theorem run_some {L : Layer} {o : Oracle} {p : L.Prog} {call : Call} {obs : Observable}
    (h : (L.sem o).run p call = some obs) :
    ∃ r, L.Ends o p call r ∧ obs = observe call r.2 r.1 := by
  change (L.result o p call).map _ = some obs at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨r, L.ends_of_result hr, rfl⟩

theorem succ_of {call : Call} {r : Halt × Machine.State} (h : (observe call r.2 r.1).success = true) :
    Succ r := by
  obtain ⟨a, s⟩ := r
  cases a <;> simp [observe, Succ] at h ⊢

theorem storage_of_succ {call : Call} {r : Halt × Machine.State} (hs : Succ r) :
    (observe call r.2 r.1).storage = storageOf r.2 := by
  obtain ⟨a, s⟩ := r
  rcases hs with h | ⟨d, h⟩ <;> simp only at h <;> subst h <;> rfl

theorem fail_of {call : Call} {r : Halt × Machine.State} (h : (observe call r.2 r.1).success = false) :
    (observe call r.2 r.1).storage = slotValue call.storage ∧ (observe call r.2 r.1).logs = [] := by
  obtain ⟨hl, hst, -⟩ := observe_failure call r.2 r.1 h
  exact ⟨hst, hl⟩

/-- A slot of the storage a call starts from, as SolarTV's state holds it. -/
theorem toNat_initial (call : Call) (k : EvmRules.Word) :
    ((Machine.State.initial call).storage k).toNat = slotValue call.storage k.toNat := by
  simp only [Machine.State.initial, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Evm.Wide.slotValue_lt _ _)

theorem storageOf_eq {call : Call} {s : Machine.State} (h : s.storage = (Machine.State.initial call).storage)
    (k : Nat) (hk : k < 2 ^ 256) : storageOf s k = slotValue call.storage k := by
  unfold storageOf
  rw [h, toNat_initial, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem value_zero {o : Oracle} {call : Call} (hv : call.callvalue < 2 ^ 256) {r : Halt × Machine.State}
    (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) (hs : Succ r) : call.callvalue = 0 := by
  by_contra h
  have hw : BitVec.ofNat 256 call.callvalue ≠ 0 := by
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
  exact value_post o call hw r e hs

/-! ## The spec -/

theorem toNat0 (call : Call) :
    ((Machine.State.initial call).storage 0).toNat = slotValue call.storage 0 := toNat_initial call 0

theorem toNat1 (call : Call) :
    ((Machine.State.initial call).storage 1).toNat = slotValue call.storage 1 := toNat_initial call 1

set_option maxHeartbeats 1000000 in
/-- **solar-verify's spec of Counter holds of solar's first lowered MIR**, under every oracle. -/
theorem holds_stage0 (o : Oracle) : Holds (MIR.Lowered.moduleSem o) stage0 spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  obtain ⟨r, e, rfl⟩ := run_some hrun
  refine ⟨fun hs => ?_, fun hs => fail_of hs⟩
  have hsucc := succ_of hs
  have hcv : (f.call args v σ).callvalue = 0 := value_zero hv e hsucc
  rw [storage_of_succ hsucc]
  have h0 := toNat0 (f.call args v σ)
  have h1 := toNat1 (f.call args v σ)
  have hl0 := Evm.Wide.slotValue_lt σ 0
  have hl1 := Evm.Wide.slotValue_lt σ 1
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at hf
  simp only [spec, layout, ContractSpec.pre] at hinv hreq ⊢
  have w0 : (0#256 : EvmRules.Word) = 0 := rfl
  have t1 : (1 : EvmRules.Word).toNat = 1 := rfl
  have w1 : (1#256 : EvmRules.Word) = 1 := rfl
  have w0' : (BitVec.ofNat 256 0 : EvmRules.Word) = 0 := rfl
  have w1' : (BitVec.ofNat 256 1 : EvmRules.Word) = 1 := rfl
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · -- count
    cases ht
    obtain ⟨hst, -⟩ := count_post o _ ((selector_of (by decide) (by simp) v σ).trans rfl) r e hsucc
    refine ⟨trivial, ?_, fun _ => hcv⟩
    rw [storageOf_eq hst 0 (by decide), storageOf_eq hst 1 (by decide)]
    exact hinv
  · -- limit
    cases ht
    obtain ⟨hst, -⟩ := limit_post o _ ((selector_of (by decide) (by simp) v σ).trans rfl) r e hsucc
    refine ⟨trivial, ?_, fun _ => hcv⟩
    rw [storageOf_eq hst 0 (by decide), storageOf_eq hst 1 (by decide)]
    exact hinv
  · -- increment
    cases ht
    simp only [FnSpec.call, incrementSpec] at *
    obtain ⟨hst, -⟩ := increment_post o _ ((selector_of (by decide) (by simp) v σ).trans rfl) r e hsucc
    refine ⟨?_, ?_, fun _ => hcv⟩ <;> unfold storageOf <;> rw [hst] <;>
      simp only [update, BitVec.ofNat_eq_ofNat, ↓reduceIte, show (1 : EvmRules.Word) ≠ 0 by decide]
    · rw [w0, BitVec.toNat_add, h0]
      try simp only [BitVec.toNat_ofNat]
      omega
    · rw [w0, w1, ite_eq_right_iff.mpr (fun h => absurd h (by decide)), BitVec.toNat_add, h0, h1]
      try simp only [BitVec.toNat_ofNat]
      omega
  · -- bump
    obtain ⟨a, hta⟩ : ∃ a, args = [a] ∧ a < 2 ^ 256 := by
      cases ht with
      | cons h t => cases t; exact ⟨_, rfl, by simpa [Abi.Param.clean] using h⟩
    obtain ⟨rfl, ha⟩ := hta
    simp only [FnSpec.call, bumpSpec, List.headD_cons] at *
    have hsel := (selector_of (sel := 0xb20eb4c4) (by decide) (args := [a]) (by simpa using ha) v σ).trans rfl
    have hn := arg_of (sel := 0xb20eb4c4) (by decide) (args := [a]) (by simpa using ha) v σ 0 (by simp) (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at hn
    obtain ⟨hs0, hov, hlim, hother⟩ := stage0_post o _ hsel r e hsucc
    have hnv : (calldataWord { calldata := Abi.calldata 0xb20eb4c4 [a], callvalue := v, storage := σ } 4).toNat = a := by
      rw [show (4 : EvmRules.Word) = BitVec.ofNat 256 4 from rfl, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    have hr1 := hother 1 (by decide)
    refine ⟨?_, ?_, fun _ => hcv⟩ <;> unfold storageOf
    · rw [w0', hs0]
      rw [BitVec.le_def] at hov
      rw [BitVec.toNat_add] at hov ⊢
      omega
    · rw [w0', w1', hs0, hr1]
      rw [BitVec.le_def] at hov hlim
      rw [BitVec.toNat_add] at hov hlim ⊢
      omega
  · -- max
    obtain ⟨a, b, hab⟩ : ∃ a b, args = [a, b] ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 := by
      cases ht with
      | cons h t =>
        cases t with
        | cons h' t' => cases t'; exact ⟨_, _, rfl, by simpa [Abi.Param.clean] using h,
            by simpa [Abi.Param.clean] using h'⟩
    obtain ⟨rfl, ha, hb⟩ := hab
    simp only [FnSpec.call, maxSpec] at *
    have hargs : ∀ x ∈ [a, b], x < 2 ^ 256 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption
    have hsel := (selector_of (sel := 0x6d5433e6) (by decide) hargs v σ).trans rfl
    have h4 := arg_of (sel := 0x6d5433e6) (by decide) hargs v σ 0 (by simp) (by decide)
    have h36 := arg_of (sel := 0x6d5433e6) (by decide) hargs v σ 1 (by simp) (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, List.getD_cons_zero,
      List.getD_cons_succ] at h4 h36
    obtain ⟨hst, m, hret⟩ := max_post o _ hsel r e hsucc
    have e4 : (4 : EvmRules.Word) = BitVec.ofNat 256 4 := rfl
    have e36 : (36 : EvmRules.Word) = BitVec.ofNat 256 36 := rfl
    rw [e4, e36, h4, h36] at hret
    refine ⟨?_, ?_, fun _ => hcv⟩
    · obtain ⟨a', s'⟩ := r
      simp only at hret hst
      subst hret
      have key : (if BitVec.ofNat 256 a < BitVec.ofNat 256 b then BitVec.ofNat 256 b
          else BitVec.ofNat 256 a).toNat = if a ≥ b then a else b := by
        by_cases h : a < b
        · have hl : BitVec.ofNat 256 a < BitVec.ofNat 256 b := by
            rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
              Nat.mod_eq_of_lt hb]
            exact h
          rw [if_pos hl, if_neg (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
        · have hl : ¬BitVec.ofNat 256 a < BitVec.ofNat 256 b := by
            rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
              Nat.mod_eq_of_lt hb]
            exact h
          rw [if_neg hl, if_pos (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
      refine ⟨if a ≥ b then a else b, ?_, rfl, ?_⟩
      · show List.map BitVec.toNat _ = _
        rw [read_store0, key]
      · (try simp only [List.getD_cons_zero, List.getD_cons_succ])
        constructor <;> split <;> omega
    · rw [storageOf_eq hst 0 (by decide), storageOf_eq hst 1 (by decide)]
      exact hinv

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.Mir.holds_stage0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_stage0

/-- **The spec carried back along the backend.** Every program whose every end on a call is
matched by an agreeing end of stage0 (`Certified … p stage0`, which solar-tv's stages give read
backwards, `certified_back`) meets the spec too. -/
theorem holds_of_certified (o : Oracle) {L : Layer} {p : L.Prog}
    (cert : Certified L MIR.Lowered.moduleLayer o p stage0 SolarTV.Milestone.W1.anyCall) :
    Holds (L.sem o) p spec :=
  fun f hf args ht v hv σ hinv hreq obs hrun =>
    holds_stage0 o f hf args ht v hv σ hinv hreq obs (stage_of_certified cert _ trivial obs hrun)

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.Mir.holds_of_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_certified

end SolidCore.Refinement.Solar.VerifyCounter.Mir
