import Contracts.CallFamilies.SyncSource
import SolidCore.Refinement.KernelThm

open SolidCore.Refinement.Kernel
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

namespace SolidCore.Refinement.CallFamilies.Skim

set_option linter.deprecated false

def skimCall (σ : List (Nat × Nat)) (dst : Nat) : Call :=
  SolidCore.Refinement.Evm.Wide.callAt 0xbc25cf77 [BitVec.ofNat 256 dst] σ

abbrev step (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) :=
  moduleBlock o (skimCall σ dst) SolarTV.Export.Calls.stage0

def fn5 : Function := (SolarTV.Export.Calls.stage0.functions[5]?).getD ⟨[], [], none⟩
def fn8 : Function := (SolarTV.Export.Calls.stage0.functions[8]?).getD ⟨[], [], none⟩
def fn9 : Function := (SolarTV.Export.Calls.stage0.functions[9]?).getD ⟨[], [], none⟩
def fn10 : Function := (SolarTV.Export.Calls.stage0.functions[10]?).getD ⟨[], [], none⟩
kernel_thm fn5_eq : SolarTV.Export.Calls.stage0.functions[5]? = some fn5
kernel_thm fn8_eq : SolarTV.Export.Calls.stage0.functions[8]? = some fn8
kernel_thm fn9_eq : SolarTV.Export.Calls.stage0.functions[9]? = some fn9
kernel_thm fn10_eq : SolarTV.Export.Calls.stage0.functions[10]? = some fn10
kernel_thm fn5_params : fn5.params = []
kernel_thm fn8_params : fn8.params = [0, 100, 1]
kernel_thm fn9_params : fn9.params = [0, 1]
kernel_thm fn5_start : ∀ s, fn5.start s = { s with memory := s.memory.store 64 128 }
kernel_thm fn8_start : ∀ s, fn8.start s = s
kernel_thm fn9_start : ∀ s, fn9.start s = s
kernel_thm f5b0 : fn5.blocks[0]? = some ⟨[],
        [.effect (some 37) .calldatasize [],
         .pure 39 .lt [.value 37, .const 36],
         .effect (some 41) .calldataload [.const 4],
         .pure 43 .gt [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff],
         .pure 50 .or [.value 39, .value 43]],
        .branch (.value 50) 3 7⟩

kernel_thm f5b1 : fn5.blocks[1]? = some ⟨[],
        [.effect (some 34) .returndatasize [],
         .effect none .returndatacopy [.const 0, .const 0, .value 34],
         .effect (some 35) .returndatasize []],
        .revert (.const 0) (.value 35)⟩

kernel_thm f5b2 : fn5.blocks[2]? = some ⟨[],
        [.effect (some 18) .returndatasize [],
         .pure 19 .lt [.value 18, .const 32]],
        .branch (.value 19) 3 4⟩

kernel_thm f5b3 : fn5.blocks[3]? = some ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩

kernel_thm f5b4 : fn5.blocks[4]? = some ⟨[],
        [.effect (some 20) .mload [.const 0],
         .effect (some 22) .sload [.const 2],
         .pure 25 .sub [.value 20, .value 22],
         .pure 26 .lt [.value 20, .value 22]],
        .branch (.value 26) 5 6⟩

kernel_thm f5b5 : fn5.blocks[5]? = some ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩

kernel_thm f5b6 : fn5.blocks[6]? = some ⟨[],
        [.call none 8 [.value 41, .value 41, .value 25],
         .assume true .gt [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff]],
        .stop⟩

kernel_thm f5b7 : fn5.blocks[7]? = some ⟨[],
        [.pure 47 .and [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff],
         .effect (some 2) .sload [.const 1],
         .effect (some 5) .gas [],
         .effect (some 6) .address [],
         .effect none .mstore [.const 0, .const 0x70a08231],
         .effect none .mstore [.const 32, .value 6],
         .effect (some 16) (.call .staticcall) [.value 5, .value 2, .const 28, .const 36, .const 0, .const 32],
         .assume true .gt [.value 6, .const 0xffffffffffffffffffffffffffffffffffffffff],
         .assume false .eq [.value 47, .value 41]],
        .branch (.value 16) 2 1⟩

kernel_thm f8b0 : fn8.blocks[0]? = some ⟨[],
        [.effect (some 3) .sload [.const 1],
         .effect (some 6) .gas [],
         .heapFloor 91 128,
         .effect (some 93) .mload [.const 64],
         .assume false .eq [.value 91, .value 93],
         .pure 94 .add [.value 91, .const 128],
         .effect none .mstore [.const 64, .value 94],
         .pure 82 .add [.value 91, .const 32],
         .effect none .mstore [.value 82, .const 0xa9059cbb00000000000000000000000000000000000000000000000000000000],
         .pure 84 .add [.value 91, .const 36],
         .effect none .mstore [.value 84, .value 0],
         .pure 79 .add [.value 84, .const 32],
         .effect none .mstore [.value 79, .value 1],
         .effect (some 27) (.call .call) [.value 6, .value 3, .const 0, .value 82, .const 68, .const 0, .const 0],
         .effect (some 28) .returndatasize [],
         .pure 105 .add [.value 28, .const 63],
         .pure 34 .and [.value 105, .const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0],
         .assume false .lt [.value 28, .const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1],
         .assume false .eq [.const 0, .const 0],
         .pure 98 .add [.value 94, .value 34],
         .effect none .mstore [.const 64, .value 98],
         .effect none .mstore [.value 94, .value 28],
         .pure 86 .add [.value 94, .const 32],
         .effect none .returndatacopy [.value 86, .const 0, .value 28],
         .assume true .gt [.value 100, .const 0xffffffffffffffffffffffffffffffffffffffff]],
        .branch (.value 27) 1 3⟩

kernel_thm f8b1 : fn8.blocks[1]? = some ⟨[],
        [.effect (some 12) .mload [.value 94],
         .pure 14 .eq [.value 28, .const 0],
         .assume false .eq [.value 12, .value 28]],
        .branch (.value 14) 4 2⟩

kernel_thm f8b2 : fn8.blocks[2]? = some ⟨[],
        [.effect (some 56) .mload [.value 94],
         .pure 60 .slt [.value 28, .const 32],
         .assume false .eq [.value 56, .value 28]],
        .branch (.value 60) 5 6⟩

kernel_thm f8b3 : fn8.blocks[3]? = some ⟨[],
        [],
        .tailCall 9 [.const 15, .const 0x5452414e534645525f4641494c45440000000000000000000000000000000000]⟩

kernel_thm f8b4 : fn8.blocks[4]? = some ⟨[],
        [],
        .leave []⟩

kernel_thm f8b5 : fn8.blocks[5]? = some ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩

kernel_thm f8b6 : fn8.blocks[6]? = some ⟨[],
        [.effect (some 63) .mload [.value 86],
         .pure 65 .gt [.value 63, .const 1]],
        .branch (.value 65) 5 7⟩

kernel_thm f8b7 : fn8.blocks[7]? = some ⟨[],
        [.ne 69 (.value 63) (.const 0)],
        .branch (.value 69) 4 3⟩

kernel_thm f9b0 : fn9.blocks[0]? = some ⟨[],
        [.effect none .mstore [.const 32, .const 32],
         .effect none .mstore [.const 64, .value 0],
         .effect none .mstore [.const 96, .value 1],
         .effect none .mstore [.const 0, .const 0x8c379a0]],
        .revert (.const 28) (.const 100)⟩

kernel_thm f10b0 : fn10.blocks[0]? = some ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 10 1⟩

kernel_thm f10b1 : fn10.blocks[1]? = some ⟨[],
        [.effect (some 4) .calldataload [.const 0],
         .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 10 [(.const 0x4f335d0a, 2), (.const 0x7464fc3d, 3), (.const 0xbc25cf77, 4), (.const 0xc45a0155, 5), (.const 0xcd3293de, 6), (.const 0xf740f328, 7), (.const 0xfc0c546a, 8), (.const 0xfff6cae9, 9)]⟩

kernel_thm f10b2 : fn10.blocks[2]? = some ⟨[],
        [],
        .tailCall 6 []⟩

kernel_thm f10b3 : fn10.blocks[3]? = some ⟨[],
        [],
        .tailCall 3 []⟩

kernel_thm f10b4 : fn10.blocks[4]? = some ⟨[],
        [],
        .tailCall 5 []⟩

kernel_thm f10b5 : fn10.blocks[5]? = some ⟨[],
        [],
        .tailCall 0 []⟩

kernel_thm f10b6 : fn10.blocks[6]? = some ⟨[],
        [],
        .tailCall 2 []⟩

kernel_thm f10b7 : fn10.blocks[7]? = some ⟨[],
        [],
        .tailCall 7 []⟩

kernel_thm f10b8 : fn10.blocks[8]? = some ⟨[],
        [],
        .tailCall 1 []⟩

kernel_thm f10b9 : fn10.blocks[9]? = some ⟨[],
        [],
        .tailCall 4 []⟩

kernel_thm f10b10 : fn10.blocks[10]? = some ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩

def mask : BitVec 256 := 0xffffffffffffffffffffffffffffffffffffffff

/-- The values a step leaves, for a step that goes on. -/
def envAfter (r : Option ((Halt × State) ⊕ Frame)) : Env :=
  match r with
  | some (.inr f) => f.2.2.1
  | _ => fun _ => 0

theorem eq_self' (a : BitVec 256) : EvmRules.Evm.eq a a = 1 := by simp [EvmRules.Evm.eq]

theorem ne_self' (a : BitVec 256) : EvmRules.Evm.ne a a = 0 := by simp [EvmRules.Evm.ne]

macro "blk" : tactic => `(tactic| (simp only [step, moduleBlock, fn5_eq, fn8_eq, fn9_eq, fn10_eq, f5b0, f5b1, f5b2, f5b3, f5b4,
    f5b5, f5b6, f5b7, f8b0, f8b1, f8b2, f8b3, f8b4, f8b5, f8b6, f8b7, f9b0, f10b0, f10b1, f10b4, f10b10, bindPhis,
    segment, splitCall, execInsts, Effect.apply, List.map_cons, List.map_nil, Operand.eval, evalPure, EVM.step,
    CallKind.shape, fn5_params, fn8_params, fn9_params, fn5_start, fn8_start, fn9_start, bindParams, envAfter]))

theorem e0 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State) :
    step o σ dst ([], .enter 10 p 0, env, s) =
      some (.inr ([], .enter 10 0 1, envAfter (step o σ dst ([], .enter 10 p 0, env, s)), s)) := by
  blk; simp [Env.set, skimCall, Evm.Wide.callAt, ne_self']

theorem e1 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State)
    (hsel : EvmRules.Evm.shr (224#256) (calldataWord (skimCall σ dst) 0#256) = 3156594551#256) :
    step o σ dst ([], .enter 10 p 1, env, s) =
      some (.inr ([], .enter 10 1 4, envAfter (step o σ dst ([], .enter 10 p 1, env, s)), s)) := by
  blk; simp [Env.set, hsel, switchTarget, Operand.eval]

theorem e4 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State) :
    step o σ dst ([], .enter 10 p 4, env, s) =
      some (.inr ([], .enter 5 0 0, fun _ => 0, { s with memory := s.memory.store 64 128 })) := by
  blk

theorem gt_mask (dst : Nat) (hd : dst < 2 ^ 160) :
    EvmRules.Evm.gt (BitVec.ofNat 256 dst) 1461501637330902918203684832716283019655932542975#256 = 0#256 := by
  have h1 : dst < 2 ^ 256 := by omega
  simp only [EvmRules.Evm.gt, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  have : ¬ (1461501637330902918203684832716283019655932542975 < dst) := by omega
  simp [this]

theorem and_mask (dst : Nat) (hd : dst < 2 ^ 160) :
    EvmRules.Evm.and (BitVec.ofNat 256 dst) 1461501637330902918203684832716283019655932542975#256 =
      BitVec.ofNat 256 dst := by
  apply BitVec.eq_of_toNat_eq
  have h1 : dst < 2 ^ 256 := by omega
  simp only [EvmRules.Evm.and, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  rw [show (1461501637330902918203684832716283019655932542975 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hd]

theorem k0 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State)
    (hsz : (skimCall σ dst).calldata.size = 36)
    (hw : calldataWord (skimCall σ dst) 4#256 = BitVec.ofNat 256 dst) (hd : dst < 2 ^ 160) :
    step o σ dst ([], .enter 5 p 0, env, s) =
      some (.inr ([], .enter 5 0 7, envAfter (step o σ dst ([], .enter 5 p 0, env, s)), s)) ∧
    envAfter (step o σ dst ([], .enter 5 p 0, env, s)) 41 = BitVec.ofNat 256 dst := by
  constructor <;> (blk; simp [Env.set, hsz, hw, gt_mask dst hd, EvmRules.Evm.or, EvmRules.Evm.lt])

def mem7 (s : State) : Mem := (s.memory.store 0 1889567281#256).store 32 (BitVec.ofNat 256 environment.callee)

def W1 (o : Oracle) (s : State) : List Event :=
  s.world ++ [.read "gas", .call .staticcall [o.env "gas" (s.world ++ [.read "gas"]) [], s.storage 1#256]
    ((((mem7 s).expand 28 36).expand 0 32).read 28 36) s.storage s.transient]

def S7 (o : Oracle) (s : State) : State :=
  called o .staticcall { s with memory := mem7 s, world := s.world ++ [.read "gas"] }
    (((mem7 s).expand 28 36).expand 0 32) 0#256 32#256 (W1 o s)

theorem k7 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State)
    (h41 : env 41 = BitVec.ofNat 256 dst) (hd : dst < 2 ^ 160) :
    step o σ dst ([], .enter 5 p 7, env, s) =
      some (.inr ([], .enter 5 7 (if callFlag o (W1 o s) = 0#256 then 1 else 2),
        envAfter (step o σ dst ([], .enter 5 p 7, env, s)), S7 o s)) ∧
    envAfter (step o σ dst ([], .enter 5 p 7, env, s)) 41 = BitVec.ofNat 256 dst := by
  have hc : EvmRules.Evm.gt (BitVec.ofNat 256 environment.callee) 1461501637330902918203684832716283019655932542975#256 = 0#256 := by
    decide
  constructor <;> (blk; simp [Env.set, h41, and_mask dst hd, eq_self', hc, W1, S7, mem7]) <;> rfl

theorem k1 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 5 p 1, env, s) =
      some (.inl (halt { s with memory := (s.memory.write 0 (o.env "returndatasize" s.world []).toNat
          (fun i => returndataByte o s.world (0 + i))) } 0 (o.env "returndatasize" s.world []) true)) := by
  blk; simp [Env.set, returndataSize]

theorem k2 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 5 p 2, env, s) =
      some (.inr (stack, .enter 5 2 (if EvmRules.Evm.lt (o.env "returndatasize" s.world []) 32#256 = 0#256 then 4 else 3),
        envAfter (step o σ dst (stack, .enter 5 p 2, env, s)), s)) ∧
    envAfter (step o σ dst (stack, .enter 5 p 2, env, s)) 41 = env 41 := by
  constructor <;> (blk; simp [Env.set])

theorem k3 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 5 p 3, env, s) = some (.inl (halt s 0 0 true)) := by
  blk

theorem k4 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 5 p 4, env, s) =
      some (.inr (stack, .enter 5 4 (if EvmRules.Evm.lt (s.memory.load 0) (s.storage 2#256) = 0#256 then 6 else 5),
        envAfter (step o σ dst (stack, .enter 5 p 4, env, s)), { s with memory := s.memory.expand 0 32 })) ∧
    envAfter (step o σ dst (stack, .enter 5 p 4, env, s)) 41 = env 41 ∧
    envAfter (step o σ dst (stack, .enter 5 p 4, env, s)) 25 = EvmRules.Evm.sub (s.memory.load 0) (s.storage 2#256) := by
  refine ⟨?_, ?_, ?_⟩ <;> (blk; simp [Env.set])

theorem k5 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 5 p 5, env, s) = some (.inl (halt
      { s with memory := (s.memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true)) := by
  blk; rfl

/-- Where pay returns to in skim. -/
def retSkim (env : Env) : Return :=
  ⟨5, 6, none, [.assume true .gt [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff]], .stop, env, [], none⟩

def payEnv (a b : BitVec 256) : Env := ((Env.set (fun _ => 0#256) 0 a).set 100 a).set 1 b

theorem k6 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (env : Env) (s : State) :
    step o σ dst ([], .enter 5 p 6, env, s) =
      some (.inr ([retSkim env], .enter 8 0 0, payEnv (env 41) (env 25), s)) := by
  blk; simp [retSkim, payEnv]

/-- The transfer selector word solar's MIR stores. -/
def selT : BitVec 256 := 76450787359836037641860180984291677749980919077056822294353438043884394381312#256

def PM (m : Mem) (a b : BitVec 256) : Mem :=
  ((((m.expand 64 32).store 64 256#256).store 160 selT).store 164 a).store 196 b

def in2 (m : Mem) (a b : BitVec 256) : List Memory.Byte := (((PM m a b).expand 160 68).expand 0 0).read 160 68

def W2 (o : Oracle) (s : State) (a b : BitVec 256) : List Event :=
  s.world ++ [.read "gas", .call .call [o.env "gas" (s.world ++ [.read "gas"]) [], s.storage 1#256, 0#256]
    (in2 s.memory a b) s.storage s.transient]

def rds2 (o : Oracle) (s : State) (a b : BitVec 256) : BitVec 256 := o.env "returndatasize" (W2 o s a b) []

def mask31 : BitVec 256 := 115792089237316195423570985008687907853269984665640564039457584007913129639904#256

def S8 (o : Oracle) (s : State) (a b : BitVec 256) : State :=
  ⟨((((((PM s.memory a b).expand 160 68).expand 0 0).write 0 (min 0 (rds2 o s a b).toNat)
      (returndataByte o (W2 o s a b))).store 64 (256#256 + EvmRules.Evm.and (rds2 o s a b + 63#256) mask31)).store 256
      (rds2 o s a b)).write 288 (rds2 o s a b).toNat (fun i => returndataByte o (W2 o s a b) (0 + i)),
    o.storageAfter (W2 o s a b), o.transientAfter (W2 o s a b), W2 o s a b⟩

theorem lt_c1 (r : BitVec 256) (hr : r.toNat < 2 ^ 64) :
    EvmRules.Evm.lt r 115792089237316195423570985008687907853269984665640564039457584007913129639873#256 = 1#256 := by
  simp only [EvmRules.Evm.lt, BitVec.ult]
  have : r.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639873 := by omega
  simp [this]

theorem p0 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State)
    (h64 : s.memory.load 64 = 128#256) (h100 : env 100 = BitVec.ofNat 256 dst) (hd : dst < 2 ^ 160)
    (hr : (rds2 o s (env 0) (env 1)).toNat < 2 ^ 64) :
    step o σ dst (stack, .enter 8 p 0, env, s) =
      some (.inr (stack, .enter 8 0 (if callFlag o (W2 o s (env 0) (env 1)) = 0#256 then 3 else 1),
        envAfter (step o σ dst (stack, .enter 8 p 0, env, s)), S8 o s (env 0) (env 1))) ∧
    envAfter (step o σ dst (stack, .enter 8 p 0, env, s)) 28 = rds2 o s (env 0) (env 1) ∧
    envAfter (step o σ dst (stack, .enter 8 p 0, env, s)) 94 = 256#256 ∧
    envAfter (step o σ dst (stack, .enter 8 p 0, env, s)) 86 = 288#256 := by
  have hr' := lt_c1 _ hr
  simp only [rds2, W2, in2, PM, selT] at hr'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (blk; simp [Env.set, h64, h100, gt_mask dst hd, eq_self', EvmRules.Evm.add, hr', called,
    S8, W2, rds2, in2, PM, selT, mask31]) <;> rfl

theorem p3 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 8 p 3, env, s) =
      some (.inr (stack, .enter 9 0 0, (Env.set (fun _ => 0#256) 0 15#256).set 1 38139611465464413496808033184516339178673403987523396430313160281336026497024#256, s)) := by
  blk; rfl


theorem p1 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State)
    (h94 : env 94 = 256#256) (hm : s.memory.load 256 = env 28) :
    step o σ dst (stack, .enter 8 p 1, env, s) =
      some (.inr (stack, .enter 8 1 (if EvmRules.Evm.eq (env 28) 0#256 = 0#256 then 2 else 4),
        envAfter (step o σ dst (stack, .enter 8 p 1, env, s)), { s with memory := s.memory.expand 256 32 })) ∧
    envAfter (step o σ dst (stack, .enter 8 p 1, env, s)) 28 = env 28 ∧
    envAfter (step o σ dst (stack, .enter 8 p 1, env, s)) 94 = env 94 ∧
    envAfter (step o σ dst (stack, .enter 8 p 1, env, s)) 86 = env 86 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (blk; simp [Env.set, h94, hm, eq_self']) <;> rfl

theorem p2 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State)
    (h94 : env 94 = 256#256) (hm : s.memory.load 256 = env 28) :
    step o σ dst (stack, .enter 8 p 2, env, s) =
      some (.inr (stack, .enter 8 2 (if EvmRules.Evm.slt (env 28) 32#256 = 0#256 then 6 else 5),
        envAfter (step o σ dst (stack, .enter 8 p 2, env, s)), { s with memory := s.memory.expand 256 32 })) ∧
    envAfter (step o σ dst (stack, .enter 8 p 2, env, s)) 86 = env 86 := by
  refine ⟨?_, ?_⟩ <;> (blk; simp [Env.set, h94, hm, eq_self']) <;> rfl

theorem p5 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 8 p 5, env, s) = some (.inl (halt s 0 0 true)) := by
  blk

theorem p6 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State)
    (h86 : env 86 = 288#256) :
    step o σ dst (stack, .enter 8 p 6, env, s) =
      some (.inr (stack, .enter 8 6 (if EvmRules.Evm.gt (s.memory.load 288) 1#256 = 0#256 then 7 else 5),
        envAfter (step o σ dst (stack, .enter 8 p 6, env, s)), { s with memory := s.memory.expand 288 32 })) ∧
    envAfter (step o σ dst (stack, .enter 8 p 6, env, s)) 63 = s.memory.load 288 := by
  refine ⟨?_, ?_⟩ <;> (blk; simp [Env.set, h86]) <;> rfl

theorem p7 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (env : Env) (s : State) :
    step o σ dst (stack, .enter 8 p 7, env, s) =
      some (.inr (stack, .enter 8 7 (if EvmRules.Evm.ne (env 63) 0#256 = 0#256 then 3 else 4),
        envAfter (step o σ dst (stack, .enter 8 p 7, env, s)), s)) := by
  blk; simp [Env.set]

theorem p4 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (e env : Env) (s : State) :
    step o σ dst ([retSkim e], .enter 8 p 4, env, s) =
      some (.inr ([], .resume 5 6 [.assume true .gt [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff]] .stop, e, s)) := by
  blk; simp [retSkim, bindResults, bindResult, publishResults]

theorem rs (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) (e : Env) (s : State)
    (h41 : e 41 = BitVec.ofNat 256 dst) (hd : dst < 2 ^ 160) :
    step o σ dst ([], .resume 5 6 [.assume true .gt [.value 41, .const 0xffffffffffffffffffffffffffffffffffffffff]] .stop, e, s) =
      some (.inl (.stop, s)) := by
  blk; simp [h41, gt_mask dst hd]

/-- The revert of \`Error("TRANSFER_FAILED")\`. -/
theorem r0 (o : Oracle) (σ : List (Nat × Nat)) (dst p : Nat) (stack : List Return) (s : State) :
    step o σ dst (stack, .enter 9 p 0, (Env.set (fun _ => 0#256) 0 15#256).set 1 38139611465464413496808033184516339178673403987523396430313160281336026497024#256, s) =
      some (.inl (halt { s with memory := (((s.memory.store 32 32#256).store 64 15#256).store 96
        38139611465464413496808033184516339178673403987523396430313160281336026497024#256).store 0 147028384#256 } 28 100 true)) := by
  blk; simp [Env.set]


section calldata
open EthLib.Base EthLib.Execution EthLib.Execution.Evm SolidCore.Refinement SolidCore.Refinement.Evm

theorem calldata_skim (σ : List (Nat × Nat)) (dst : Nat) :
    (skimCall σ dst).calldata = cdOf (selectorOf 0xbc25cf77) [BitVec.ofNat 256 dst] := by
  have := calldata_eq_cdOf 0xbc25cf77 [(BitVec.ofNat 256 dst).toNat] (by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl
    exact BitVec.isLt _)
  rw [show (skimCall σ dst).calldata = Abi.calldata 0xbc25cf77 [(BitVec.ofNat 256 dst).toNat] from rfl, this]
  simp only [List.map_cons, List.map_nil, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem skim_sel (σ : List (Nat × Nat)) (dst : Nat) :
    EvmRules.Evm.shr (224#256) (calldataWord (skimCall σ dst) 0#256) = 3156594551#256 := by
  rw [SolidCore.Refinement.Generic.calldataWord_eq, calldata_skim]
  have := shr_cdOf_selectorOf 0xbc25cf77 [BitVec.ofNat 256 dst] (by decide)
  simpa [EvmRules.Evm.shr, bitwiseShr] using this

theorem skim_word4 (σ : List (Nat × Nat)) (dst : Nat) :
    calldataWord (skimCall σ dst) 4#256 = BitVec.ofNat 256 dst := by
  rw [SolidCore.Refinement.Generic.calldataWord_eq, calldata_skim]
  exact loadWord_cdOf_getD _ [BitVec.ofNat 256 dst] 4 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem skim_size (σ : List (Nat × Nat)) (dst : Nat) : (skimCall σ dst).calldata.size = 36 := by
  rw [calldata_skim, size_cdOf, size_selectorOf]; simp

end calldata

end SolidCore.Refinement.CallFamilies.Skim
