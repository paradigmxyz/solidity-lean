import Contracts.CallFamilies.SkimMir

/-!
# skim in solar's first lowered MIR, for every oracle

run_skim: solar's stage0 runs skim(dst) from the storage σ to mirEnd o σ dst under every oracle
o, for every address dst below 2 ^ 160 and every oracle whose second call returns fewer than
2 ^ 64 bytes: the token's balanceOf(address(this)) STATICCALL, its revert bubbling and short
return check, the checked subtraction of the reserve (panic 0x11), the internal call of pay with
the free-memory-pointer allocation of the transfer calldata and the return buffer, the low-level
CALL of transfer(dst, amount), and the decoding of its return data as empty or a bool word.
Each block step is a lemma of SkimMir over free values and state.
-/

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

namespace SolidCore.Refinement.CallFamilies.Skim

set_option linter.deprecated false

set_option hygiene false in
local notation "tS0" => S0' σ dst

/-- The state skim's body starts in: the free-memory pointer at 128. -/
def S0' (σ : List (Nat × Nat)) (dst : Nat) : State :=
  { State.initial (skimCall σ dst) with memory := (State.initial (skimCall σ dst)).memory.store 64 128 }

set_option hygiene false in
local notation "tT" => S7 o (S0' σ dst)
set_option hygiene false in
local notation "tT4" => ({ S7 o (S0' σ dst) with memory := (S7 o (S0' σ dst)).memory.expand 0 32 } : State)
set_option hygiene false in
local notation "tAmt" => EvmRules.Evm.sub ((S7 o (S0' σ dst)).memory.load 0) ((S7 o (S0' σ dst)).storage 2#256)
set_option hygiene false in
local notation "tU" => S8 o tT4 (BitVec.ofNat 256 dst) tAmt
set_option hygiene false in
local notation "tR" => rds2 o tT4 (BitVec.ofNat 256 dst) tAmt
set_option hygiene false in
local notation "tU1" => ({ tU with memory := (tU).memory.expand 256 32 } : State)
set_option hygiene false in
local notation "tU2" => ({ tU1 with memory := (tU1).memory.expand 256 32 } : State)
set_option hygiene false in
local notation "tU3" => ({ tU2 with memory := (tU2).memory.expand 288 32 } : State)

/-- The revert of Error("TRANSFER_FAILED") from the state s. -/
def errHalt (s : State) : Halt × State :=
  halt { s with memory := (((s.memory.store 32 32#256).store 64 15#256).store 96
    38139611465464413496808033184516339178673403987523396430313160281336026497024#256).store 0 147028384#256 } 28 100 true

/-- The end of solar's stage0 on a call of skim. -/
def mirEnd (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) : Halt × State :=
  if callFlag o (W1 o tS0) = 0#256 then
    halt { tT with memory := ((tT).memory.write 0 (o.env "returndatasize" (tT).world []).toNat
      (fun i => returndataByte o (tT).world (0 + i))) } 0 (o.env "returndatasize" (tT).world []) true
  else if EvmRules.Evm.lt (o.env "returndatasize" (tT).world []) 32#256 = 0#256 then
    if EvmRules.Evm.lt ((tT).memory.load 0) ((tT).storage 2#256) = 0#256 then
      if callFlag o (W2 o tT4 (BitVec.ofNat 256 dst) tAmt) = 0#256 then errHalt tU
      else if EvmRules.Evm.eq tR 0#256 = 0#256 then
        if EvmRules.Evm.slt tR 32#256 = 0#256 then
          if EvmRules.Evm.gt ((tU2).memory.load 288) 1#256 = 0#256 then
            if EvmRules.Evm.ne ((tU2).memory.load 288) 0#256 = 0#256 then errHalt tU3
            else (.stop, tU3)
          else halt tU3 0 0 true
        else halt tU2 0 0 true
      else (.stop, tU1)
    else halt { tT4 with memory := ((tT4).memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true
  else halt tT 0 0 true

theorem load64 (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) : (tT4).memory.load 64 = 128#256 := by
  simp only [S7, called, mem7, S0']
  have e0 : (0#256).toNat = 0 := rfl
  have e32 : (32#256).toNat = 32 := rfl
  rw [Mem.load_expand, Mem.load_write_of_disjoint _ _ _ _ _ (Or.inr (by rw [e0, e32]; omega)), Mem.load_expand, Mem.load_expand,
    Mem.load_store_of_disjoint _ _ _ _ (Or.inr (by omega)), Mem.load_store_of_disjoint _ _ _ _ (Or.inr (by omega)),
    Mem.load_store_same]
  rfl

theorem load256_S8 (o : Oracle) (s : State) (a b : BitVec 256) : (S8 o s a b).memory.load 256 = rds2 o s a b := by
  simp only [S8]
  rw [Mem.load_write_of_disjoint _ _ _ _ _ (Or.inl (by omega)), Mem.load_store_same]

theorem payEnv_0 (a b : BitVec 256) : payEnv a b 0 = a := by simp [payEnv, Env.set]
theorem payEnv_1 (a b : BitVec 256) : payEnv a b 1 = b := by simp [payEnv, Env.set]
theorem payEnv_100 (a b : BitVec 256) : payEnv a b 100 = a := by simp [payEnv, Env.set]

open SolidCore.Refinement.CallFamilies.Sync (iter_next iter_end) in
theorem run_skim (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) (hd : dst < 2 ^ 160)
    (hr : callFlag o (W1 o tS0) ≠ 0#256 →
      EvmRules.Evm.lt (o.env "returndatasize" (tT).world []) 32#256 = 0#256 →
      EvmRules.Evm.lt ((tT).memory.load 0) ((tT).storage 2#256) = 0#256 → (tR).toNat < 2 ^ 64) :
    Module.run o SolarTV.Export.Calls.stage0 (skimCall σ dst) 20 = some (mirEnd o σ dst) := by
  show iterate (step o σ dst) 20 ([], .enter 10 0 0, fun _ => 0, State.initial (skimCall σ dst)) = _
  rw [iter_next (e0 o σ dst 0 _ _), iter_next (e1 o σ dst 0 _ _ (skim_sel σ dst)), iter_next (e4 o σ dst 1 _ _)]
  rw [show ({ State.initial (skimCall σ dst) with memory := (State.initial (skimCall σ dst)).memory.store 64 128 } : State) = tS0 from rfl]
  obtain ⟨h0, h0e⟩ := k0 o σ dst 0 (fun _ => 0) tS0 (skim_size σ dst) (skim_word4 σ dst) hd
  rw [iter_next h0]
  obtain ⟨h7, h7e⟩ := k7 o σ dst 0 _ tS0 h0e hd
  rw [iter_next h7]
  unfold mirEnd
  by_cases c1 : callFlag o (W1 o tS0) = 0#256
  · rw [if_pos c1, if_pos c1, iter_end (k1 o σ dst 7 [] _ _)]
  rw [if_neg c1, if_neg c1]
  obtain ⟨h2, h2e⟩ := k2 o σ dst 7 [] _ tT
  rw [iter_next h2]
  by_cases c2 : EvmRules.Evm.lt (o.env "returndatasize" (tT).world []) 32#256 = 0#256
  swap
  · rw [if_neg c2, if_neg c2, iter_end (k3 o σ dst 2 [] _ _)]
  rw [if_pos c2, if_pos c2]
  obtain ⟨h4, h4e, h4a⟩ := k4 o σ dst 2 [] _ tT
  rw [iter_next h4]
  by_cases c4 : EvmRules.Evm.lt ((tT).memory.load 0) ((tT).storage 2#256) = 0#256
  swap
  · rw [if_neg c4, if_neg c4, iter_end (k5 o σ dst 4 [] _ _)]
  rw [if_pos c4, if_pos c4, iter_next (k6 o σ dst 4 _ _)]
  have h41 : envAfter (step o σ dst ([], .enter 5 2 4, envAfter (step o σ dst ([], .enter 5 7 2,
      envAfter (step o σ dst ([], .enter 5 0 7, envAfter (step o σ dst ([], .enter 5 0 0, fun _ => 0, tS0)), tS0)), tT)), tT)) 41 =
      BitVec.ofNat 256 dst := by rw [h4e, h2e, h7e]
  rw [h41, h4a]
  obtain ⟨hp, hp28, hp94, hp86⟩ := p0 o σ dst 0 _ (payEnv (BitVec.ofNat 256 dst) tAmt) tT4 (load64 o σ dst)
    (payEnv_100 _ _) hd (by rw [payEnv_0, payEnv_1]; exact hr c1 c2 c4)
  rw [payEnv_0, payEnv_1] at hp hp28
  rw [iter_next hp]
  by_cases c5 : callFlag o (W2 o tT4 (BitVec.ofNat 256 dst) tAmt) = 0#256
  · rw [if_pos c5, if_pos c5, iter_next (p3 o σ dst 0 _ _ _), iter_end (r0 o σ dst 0 _ _)]
    rfl
  rw [if_neg c5, if_neg c5]
  obtain ⟨hq, hq28, hq94, hq86⟩ := p1 o σ dst 0 _ _ tU hp94 (by rw [load256_S8, hp28])
  rw [hp28] at hq
  rw [iter_next hq]
  by_cases c6 : EvmRules.Evm.eq tR 0#256 = 0#256
  swap
  · rw [if_neg c6, if_neg c6, iter_next (p4 o σ dst 1 _ _ _),
      iter_end (rs o σ dst _ _ h41 hd)]
  rw [if_pos c6, if_pos c6]
  obtain ⟨hq2, hq2e⟩ := p2 o σ dst 1 _ _ tU1 (hq94.trans hp94) (by rw [Mem.load_expand, load256_S8, hq28, hp28])
  rw [hq28, hp28] at hq2
  rw [iter_next hq2]
  by_cases c7 : EvmRules.Evm.slt tR 32#256 = 0#256
  swap
  · rw [if_neg c7, if_neg c7, iter_end (p5 o σ dst 2 _ _ _)]
  rw [if_pos c7, if_pos c7]
  obtain ⟨hq6, hq6e⟩ := p6 o σ dst 2 _ _ tU2 (hq2e.trans (hq86.trans hp86))
  rw [iter_next hq6]
  by_cases c8 : EvmRules.Evm.gt ((tU2).memory.load 288) 1#256 = 0#256
  swap
  · rw [if_neg c8, if_neg c8, iter_end (p5 o σ dst 6 _ _ _)]
  rw [if_pos c8, if_pos c8]
  rw [iter_next (p7 o σ dst 6 _ _ _), hq6e]
  by_cases c9 : EvmRules.Evm.ne ((tU2).memory.load 288) 0#256 = 0#256
  · rw [if_pos c9, if_pos c9, iter_next (p3 o σ dst 7 _ _ _), iter_end (r0 o σ dst 0 _ _)]
    rfl
  · rw [if_neg c9, if_neg c9, iter_next (p4 o σ dst 7 _ _ _),
      iter_end (rs o σ dst _ _ h41 hd)]

/-- info: 'SolidCore.Refinement.CallFamilies.Skim.run_skim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_skim

end SolidCore.Refinement.CallFamilies.Skim
