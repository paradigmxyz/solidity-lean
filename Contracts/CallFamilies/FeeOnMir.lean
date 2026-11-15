import Contracts.CallFamilies.SyncMir

/-!
# `feeOn` in solar's first lowered MIR, for every oracle

`sem_feeOn`: solar's stage0 runs `feeOn()` from the storage `σ` to `feeOnEnd o σ` under every
oracle `o`: it reads the factory (slot 0), makes one `STATICCALL` of `feeTo()` (world
`W o σ`), reverts with the callee's return data when the call fails, reverts with empty data when
it returned fewer than 32 bytes or a word above `2 ^ 160 - 1` (the address decoder's check), and
otherwise returns whether the word is not zero, after storing 1 in slot 3 when it is not.
-/

open SolidCore.Refinement.Kernel SolidCore.Refinement.CallFamilies.Sync
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

namespace SolidCore.Refinement.CallFamilies.FeeOn

set_option linter.deprecated false

def feeOnCall (σ : List (Nat × Nat)) : Call :=
  { calldata := ⟨#[0x4f, 0x33, 0x5d, 0x0a]⟩, callvalue := 0, storage := σ }

abbrev step (o : Oracle) (σ : List (Nat × Nat)) := moduleBlock o (feeOnCall σ) SolarTV.Export.Calls.stage0

def F0 (σ : List (Nat × Nat)) : Frame := ([], .enter 10 0 0, fun _ => 0, State.initial (feeOnCall σ))
def F1 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F0 σ)
def F2 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F1 o σ)
def F3 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F2 o σ)
def F4 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F3 o σ)

kernel_thm h0 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F0 σ) = some (.inr (F1 o σ))
kernel_thm h1 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F1 o σ) = some (.inr (F2 o σ))
kernel_thm h2 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F2 o σ) = some (.inr (F3 o σ))
kernel_thm h3 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F3 o σ) = some (.inr (F4 o σ))

/-- Memory at the call: the free memory pointer and `feeTo()`'s selector. -/
def mem1 : Mem := (Mem.initial.store 64 128).store 0 0x17e7e58

/-- The call's input: the selector's four bytes. -/
def input : List Memory.Byte := ((mem1.expand 28 4).expand 0 32).read 28 4

/-- The world of the call. -/
def W (o : Oracle) (σ : List (Nat × Nat)) : List Event :=
  [.read "gas", .call .staticcall [o.env "gas" [.read "gas"] [], BitVec.ofNat 256 (slotValue σ 0)] input
    (State.initial (feeOnCall σ)).storage (fun _ => 0)]

def M4 (o : Oracle) (σ : List (Nat × Nat)) : Mem :=
  ((mem1.expand 28 4).expand 0 32).write 0 (min 32 (returndataSize o (W o σ)).toNat)
    (returndataByte o (W o σ))

def S4 (o : Oracle) (σ : List (Nat × Nat)) : State :=
  ⟨M4 o σ, (State.initial (feeOnCall σ)).storage, fun _ => 0, W o σ⟩

kernel_thm F4_eq : ∀ (o : Oracle) (σ : List (Nat × Nat)), F4 o σ =
    ([], .enter 6 0 (if callFlag o (W o σ) = 0 then 1 else 2), (F4 o σ).2.2.1, S4 o σ)

def G2 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := ([], .enter 6 0 2, env, S4 o σ)
def G2n (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := next (step o σ) (G2 o σ env)

kernel_thm g2 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env),
    step o σ (G2 o σ env) = some (.inr (G2n o σ env))
kernel_thm G2n_eq : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env), G2n o σ env =
    ([], .enter 6 2 (if EvmRules.Evm.lt (returndataSize o (W o σ)) 32 = 0 then 6 else 5),
      (G2n o σ env).2.2.1, S4 o σ)

kernel_thm g5 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (p : Nat) (env : Env) (s : State),
    step o σ ([], .enter 6 p 5, env, s) = some (.inl (halt s 0 0 true))

/-- The word the call returned, as `MLOAD` reads it. -/
def ret (o : Oracle) (σ : List (Nat × Nat)) : BitVec 256 := (M4 o σ).load 0

def S6 (o : Oracle) (σ : List (Nat × Nat)) : State := { S4 o σ with memory := (M4 o σ).expand 0 32 }

def G6 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := ([], .enter 6 2 6, env, S4 o σ)
def G6n (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := next (step o σ) (G6 o σ env)

kernel_thm g6 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env),
    step o σ (G6 o σ env) = some (.inr (G6n o σ env))
kernel_thm G6n_eq : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env), G6n o σ env =
    ([], .enter 6 6 (if EvmRules.Evm.gt (ret o σ) 0xffffffffffffffffffffffffffffffffffffffff = 0 then 7 else 5),
      (G6n o σ env).2.2.1, S6 o σ)
kernel_thm G6n_env : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env), (G6n o σ env).2.2.1 16 = ret o σ

def syncFn6 : Function := (SolarTV.Export.Calls.stage0.functions[6]?).getD ⟨[], [], none⟩
kernel_thm fn6 : SolarTV.Export.Calls.stage0.functions[6]? = some syncFn6
kernel_thm b1 : syncFn6.blocks[1]? = some ⟨[],
    [.effect (some 26) .returndatasize [],
     .effect none .returndatacopy [.const 0, .const 0, .value 26],
     .effect (some 27) .returndatasize []],
    .revert (.const 0) (.value 27)⟩
kernel_thm b7 : syncFn6.blocks[7]? = some ⟨[],
    [.pure 34 .and [.value 16, .const 0xffffffffffffffffffffffffffffffffffffffff],
     .ne 21 (.value 16) (.const 0),
     .assume false .eq [.value 34, .value 16]],
    .branch (.value 21) 3 4⟩
kernel_thm b3 : syncFn6.blocks[3]? = some ⟨[], [.effect none .sstore [.const 3, .const 1]], .jump 4⟩
kernel_thm b4 : syncFn6.blocks[4]? = some ⟨[],
    [.word 31 (.value 21), .effect none .mstore [.const 0, .value 31]], .ret (.const 0) (.const 32)⟩

theorem exec_b1 (o : Oracle) (call : Call) (env : Env) (s : State) :
    execInsts o call [.effect (some 26) .returndatasize [],
     .effect none .returndatacopy [.const 0, .const 0, .value 26],
     .effect (some 27) .returndatasize []] env s =
    some ((env.set 26 (returndataSize o s.world)).set 27 (returndataSize o s.world),
      { s with memory := s.memory.write 0 (returndataSize o s.world).toNat (fun i => returndataByte o s.world (0 + i)) }) := by
  simp only [execInsts, Effect.apply, List.map_cons, List.map_nil, Operand.eval]
  have h : (env.set 26 (returndataSize o s.world)) 26 = returndataSize o s.world := by
    simp [Env.set]
  simp only [h, returndataSize]
  simp

theorem g1 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) :
    step o σ ([], .enter 6 0 1, env, S4 o σ) = some (.inl (halt
      { S4 o σ with memory := (M4 o σ).write 0 (returndataSize o (W o σ)).toNat (fun i => returndataByte o (W o σ) (0 + i)) } 0 (returndataSize o (W o σ)) true)) := by
  simp only [step, moduleBlock, fn6, b1, bindPhis, segment, splitCall, exec_b1]
  simp [Operand.eval, Env.set, S4]

/-- The address mask. -/
abbrev mask : BitVec 256 := 0xffffffffffffffffffffffffffffffffffffffff

theorem step_and (c) (a b : BitVec 256) : EVM.step c .and [a, b] = some [a &&& b] := rfl
theorem step_eq (c) (a b : BitVec 256) :
    EVM.step c .eq [a, b] = some [if a = b then 1 else 0] := by
  show some [EvmRules.Evm.eq a b] = _
  unfold EvmRules.Evm.eq
  by_cases h : a = b <;> simp [h]

theorem g7 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) (hv : env 16 &&& mask = env 16) :
    step o σ ([], .enter 6 6 7, env, S6 o σ) = some (.inr ([], .enter 6 7
      (if EvmRules.Evm.ne (env 16) 0 = 0 then 4 else 3),
      ((env.set 34 (env 16 &&& mask)).set 21 (EvmRules.Evm.ne (env 16) 0)), S6 o σ)) := by
  simp only [step, moduleBlock, fn6, b7, bindPhis, segment, splitCall, execInsts, List.map_cons,
    List.map_nil, Operand.eval, evalPure]
  simp only [step_and, step_eq, hv]
  simp [Env.set]

kernel_thm g3 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env),
    step o σ ([], .enter 6 7 3, env, S6 o σ) =
      some (.inr ([], .enter 6 3 4, env, { S6 o σ with storage := update (S6 o σ).storage 3 1 }))

kernel_thm g4 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (p : Nat) (env : Env) (s : State),
    step o σ ([], .enter 6 p 4, env, s) =
      some (.inl (halt { s with memory := s.memory.store 0 (env 21) } 0 32 false))

theorem and_mask_of_gt (v : BitVec 256) (h : EvmRules.Evm.gt v mask = 0) : v &&& mask = v := by
  have hle : v.toNat < 2 ^ 160 := by
    change (bif mask.ult v then (1 : BitVec 256) else 0) = 0 at h
    cases hu : mask.ult v with
    | true => rw [hu] at h; exact absurd h (by decide)
    | false =>
      simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hu
      have : mask.toNat = 2 ^ 160 - 1 := rfl
      omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show mask.toNat = 2 ^ 160 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hle]

/-- The end of solar's stage0 on a call of `feeOn()`. -/
def feeOnEnd (o : Oracle) (σ : List (Nat × Nat)) : Halt × State :=
  if callFlag o (W o σ) = 0 then
    halt { S4 o σ with memory := (M4 o σ).write 0 (returndataSize o (W o σ)).toNat (fun i => returndataByte o (W o σ) (0 + i)) } 0 (returndataSize o (W o σ)) true
  else if EvmRules.Evm.lt (returndataSize o (W o σ)) 32 ≠ 0 then halt (S4 o σ) 0 0 true
  else if EvmRules.Evm.gt (ret o σ) mask ≠ 0 then halt (S6 o σ) 0 0 true
  else if EvmRules.Evm.ne (ret o σ) 0 = 0 then
    halt { S6 o σ with memory := (S6 o σ).memory.store 0 (EvmRules.Evm.ne (ret o σ) 0) } 0 32 false
  else
    halt { S6 o σ with storage := update (S6 o σ).storage 3 1, memory := (S6 o σ).memory.store 0 (EvmRules.Evm.ne (ret o σ) 0) } 0 32 false

theorem run_feeOn (o : Oracle) (σ : List (Nat × Nat)) :
    Module.run o SolarTV.Export.Calls.stage0 (feeOnCall σ) 10 = some (feeOnEnd o σ) := by
  show iterate (step o σ) 10 (F0 σ) = _
  rw [iter_next (h0 o σ), iter_next (h1 o σ), iter_next (h2 o σ), iter_next (h3 o σ), F4_eq]
  unfold feeOnEnd
  by_cases hf : callFlag o (W o σ) = 0
  · rw [if_pos hf, if_pos hf, iter_end (g1 o σ _)]
  rw [if_neg hf, if_neg hf]
  rw [show (([], .enter 6 0 2, (F4 o σ).2.2.1, S4 o σ) : Frame) = G2 o σ (F4 o σ).2.2.1 from rfl,
    iter_next (g2 o σ _), G2n_eq]
  by_cases hl : EvmRules.Evm.lt (returndataSize o (W o σ)) 32 = 0
  · rw [if_pos hl, if_neg (fun h => h hl)]
    generalize (G2n o σ (F4 o σ).2.2.1).2.2.1 = e2
    rw [show (([], .enter 6 2 6, e2, S4 o σ) : Frame) = G6 o σ e2 from rfl, iter_next (g6 o σ _), G6n_eq]
    have henv := G6n_env o σ e2
    generalize (G6n o σ e2).2.2.1 = e6 at henv ⊢
    by_cases hg : EvmRules.Evm.gt (ret o σ) mask = 0
    · rw [if_pos hg, if_neg (fun h => h hg)]
      have hv : e6 16 &&& mask = e6 16 := by rw [henv]; exact and_mask_of_gt _ hg
      rw [iter_next (g7 o σ e6 hv), henv]
      by_cases hn : EvmRules.Evm.ne (ret o σ) 0 = 0
      · rw [if_pos hn, if_pos hn, iter_end (g4 o σ _ _ _)]
        simp [Env.set]
      · rw [if_neg hn, if_neg hn, iter_next (g3 o σ _), iter_end (g4 o σ _ _ _)]
        simp [Env.set]
    · rw [if_neg hg, if_pos hg, iter_end (g5 o σ _ _ _)]
  · rw [if_neg hl, if_pos hl, iter_end (g5 o σ _ _ _)]

theorem sem_feeOn (o : Oracle) (σ : List (Nat × Nat)) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (feeOnCall σ) =
      some (observe (feeOnCall σ) (feeOnEnd o σ).2 (feeOnEnd o σ).1) := by
  show (moduleLayer.result o _ _).map _ = _
  rw [moduleLayer.result_of_ends (show moduleLayer.Ends o SolarTV.Export.Calls.stage0 (feeOnCall σ)
    (feeOnEnd o σ) from ⟨10, run_feeOn o σ⟩)]
  rfl

/-- info: 'SolidCore.Refinement.CallFamilies.FeeOn.sem_feeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sem_feeOn

end SolidCore.Refinement.CallFamilies.FeeOn
