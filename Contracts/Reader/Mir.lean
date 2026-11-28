import Contracts.CallFamilies.SkimAgree
import reader.gen.Reader.Stage0

/-!
# `read` in solar's first lowered MIR, for every oracle

`run_read`: solar's stage0 of `Certified/reader/reader.sol` (`SolarTV.Export.Reader.stage0`) runs
`read(a)` from the storage `σ` to `mirEnd o σ a` under every oracle `o`, for every address `a`
below `2 ^ 160`: the dispatcher, the argument's size and range check, one `STATICCALL` of
`price()` to `a` (world `W1`), the bubbled revert of a failed call, the empty revert of a
return shorter than 32 bytes, and the checked increment of the returned word (`Panic(0x11)` on
overflow, else the 32-byte result). Each block step is a lemma over free values and state.
-/

open SolidCore.Refinement.Kernel
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

namespace SolidCore.Refinement.Reader

set_option linter.deprecated false

/-- The call of `read(a)` from the storage `σ`, with no value. -/
def readCall (σ : List (Nat × Nat)) (a : Nat) : Call :=
  { calldata := Abi.calldata 0xa087a87e [a], callvalue := 0, storage := σ }

abbrev step (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) :=
  moduleBlock o (readCall σ a) SolarTV.Export.Reader.stage0

def fn0 : Function := (SolarTV.Export.Reader.stage0.functions[0]?).getD ⟨[], [], none⟩
def fn1 : Function := (SolarTV.Export.Reader.stage0.functions[1]?).getD ⟨[], [], none⟩
kernel_thm fn0_eq : SolarTV.Export.Reader.stage0.functions[0]? = some fn0
kernel_thm fn1_eq : SolarTV.Export.Reader.stage0.functions[1]? = some fn1
kernel_thm fn0_params : fn0.params = []
kernel_thm fn0_start : ∀ s, fn0.start s = { s with memory := s.memory.store 64 128 }

kernel_thm f0b0 : fn0.blocks[0]? = some ⟨[],
        [.effect (some 33) .calldatasize [],
         .pure 35 .lt [.value 33, .const 36],
         .effect (some 37) .calldataload [.const 4],
         .pure 39 .gt [.value 37, .const 0xffffffffffffffffffffffffffffffffffffffff],
         .pure 47 .or [.value 35, .value 39]],
        .branch (.value 47) 3 7⟩

kernel_thm f0b1 : fn0.blocks[1]? = some ⟨[],
        [.effect (some 30) .returndatasize [],
         .effect none .returndatacopy [.const 0, .const 0, .value 30],
         .effect (some 31) .returndatasize []],
        .revert (.const 0) (.value 31)⟩

kernel_thm f0b2 : fn0.blocks[2]? = some ⟨[],
        [.effect (some 13) .returndatasize [],
         .pure 14 .lt [.value 13, .const 32]],
        .branch (.value 14) 3 4⟩

kernel_thm f0b3 : fn0.blocks[3]? = some ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩

kernel_thm f0b4 : fn0.blocks[4]? = some ⟨[],
        [.effect (some 15) .mload [.const 0],
         .pure 19 .add [.value 15, .const 1],
         .pure 20 .eq [.value 19, .const 0]],
        .branch (.value 20) 5 6⟩

kernel_thm f0b5 : fn0.blocks[5]? = some ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩

kernel_thm f0b6 : fn0.blocks[6]? = some ⟨[],
        [.effect none .mstore [.const 0, .value 19]],
        .ret (.const 0) (.const 32)⟩

kernel_thm f0b7 : fn0.blocks[7]? = some ⟨[],
        [.effect (some 3) .gas [],
         .effect none .mstore [.const 0, .const 0xa035b1fe],
         .effect (some 11) (.call .staticcall) [.value 3, .value 37, .const 28, .const 4, .const 0, .const 32]],
        .branch (.value 11) 2 1⟩

kernel_thm f1b0 : fn1.blocks[0]? = some ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 3 1⟩

kernel_thm f1b1 : fn1.blocks[1]? = some ⟨[],
        [.effect (some 4) .calldataload [.const 0],
         .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 3 [(.const 0xa087a87e, 2)]⟩

kernel_thm f1b2 : fn1.blocks[2]? = some ⟨[],
        [],
        .tailCall 0 []⟩

/-- The values a step leaves, for a step that goes on. -/
def envAfter (r : Option ((Halt × State) ⊕ Frame)) : Env :=
  match r with
  | some (.inr f) => f.2.2.1
  | _ => fun _ => 0

macro "blk" : tactic => `(tactic| (simp only [step, moduleBlock, fn0_eq, fn1_eq, f0b0, f0b1, f0b2, f0b3, f0b4,
    f0b5, f0b6, f0b7, f1b0, f1b1, f1b2, bindPhis,
    segment, splitCall, execInsts, Effect.apply, List.map_cons, List.map_nil, Operand.eval, evalPure, EVM.step,
    CallKind.shape, fn0_params, fn0_start, bindParams, envAfter]))

theorem e0 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 1 p 0, env, s) =
      some (.inr ([], .enter 1 0 1, envAfter (step o σ a ([], .enter 1 p 0, env, s)), s)) := by
  blk; simp [Env.set, readCall, CallFamilies.Skim.ne_self']

theorem e1 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State)
    (hsel : EvmRules.Evm.shr (224#256) (calldataWord (readCall σ a) 0#256) = 2693245054#256) :
    step o σ a ([], .enter 1 p 1, env, s) =
      some (.inr ([], .enter 1 1 2, envAfter (step o σ a ([], .enter 1 p 1, env, s)), s)) := by
  blk; simp [Env.set, hsel, switchTarget, Operand.eval]

theorem e2 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 1 p 2, env, s) =
      some (.inr ([], .enter 0 0 0, fun _ => 0, { s with memory := s.memory.store 64 128 })) := by
  blk

theorem k0 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State)
    (hsz : (readCall σ a).calldata.size = 36)
    (hw : calldataWord (readCall σ a) 4#256 = BitVec.ofNat 256 a) (ha : a < 2 ^ 160) :
    step o σ a ([], .enter 0 p 0, env, s) =
      some (.inr ([], .enter 0 0 7, envAfter (step o σ a ([], .enter 0 p 0, env, s)), s)) ∧
    envAfter (step o σ a ([], .enter 0 p 0, env, s)) 37 = BitVec.ofNat 256 a := by
  constructor <;> (blk; simp [Env.set, hsz, hw, CallFamilies.Skim.gt_mask a ha, EvmRules.Evm.or, EvmRules.Evm.lt])

/-- Memory after the selector store of `price()`. -/
def mem7 (s : State) : Mem := s.memory.store 0 2687873534#256

/-- The world after the `STATICCALL` of `price()` to `a`. -/
def W1 (o : Oracle) (s : State) (a : Nat) : List Event :=
  s.world ++ [.read "gas", .call .staticcall [o.env "gas" (s.world ++ [.read "gas"]) [], BitVec.ofNat 256 a]
    ((((mem7 s).expand 28 4).expand 0 32).read 28 4) s.storage s.transient]

/-- The state after the call. -/
def S7 (o : Oracle) (s : State) (a : Nat) : State :=
  called o .staticcall { s with memory := mem7 s, world := s.world ++ [.read "gas"] }
    (((mem7 s).expand 28 4).expand 0 32) 0#256 32#256 (W1 o s a)

theorem k7 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State)
    (h37 : env 37 = BitVec.ofNat 256 a) :
    step o σ a ([], .enter 0 p 7, env, s) =
      some (.inr ([], .enter 0 7 (if callFlag o (W1 o s a) = 0#256 then 1 else 2),
        envAfter (step o σ a ([], .enter 0 p 7, env, s)), S7 o s a)) := by
  blk; simp [Env.set, h37, W1, S7, mem7]

theorem k1 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 1, env, s) =
      some (.inl (halt { s with memory := (s.memory.write 0 (o.env "returndatasize" s.world []).toNat
          (fun i => returndataByte o s.world (0 + i))) } 0 (o.env "returndatasize" s.world []) true)) := by
  blk; simp [Env.set, returndataSize]

theorem k2 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 2, env, s) =
      some (.inr ([], .enter 0 2 (if EvmRules.Evm.lt (o.env "returndatasize" s.world []) 32#256 = 0#256 then 4 else 3),
        envAfter (step o σ a ([], .enter 0 p 2, env, s)), s)) := by
  blk; simp [Env.set]

theorem k3 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 3, env, s) = some (.inl (halt s 0 0 true)) := by
  blk

theorem k4 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 4, env, s) =
      some (.inr ([], .enter 0 4 (if EvmRules.Evm.eq (s.memory.load 0 + 1#256) 0#256 = 0#256 then 6 else 5),
        envAfter (step o σ a ([], .enter 0 p 4, env, s)), { s with memory := s.memory.expand 0 32 })) ∧
    envAfter (step o σ a ([], .enter 0 p 4, env, s)) 19 = s.memory.load 0 + 1#256 := by
  constructor <;> (blk; simp [Env.set, EvmRules.Evm.add])

theorem k5 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 5, env, s) = some (.inl (halt
      { s with memory := (s.memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true)) := by
  blk; rfl

theorem k6 (o : Oracle) (σ : List (Nat × Nat)) (a p : Nat) (env : Env) (s : State) :
    step o σ a ([], .enter 0 p 6, env, s) = some (.inl (halt
      { s with memory := s.memory.store 0 (env 19) } 0 32 false)) := by
  blk; rfl

section calldata
open EthLib.Base EthLib.Execution EthLib.Execution.Evm SolidCore.Refinement SolidCore.Refinement.Evm

theorem calldata_read (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    (readCall σ a).calldata = cdOf (selectorOf 0xa087a87e) [BitVec.ofNat 256 a] := by
  have := calldata_eq_cdOf 0xa087a87e [a] (by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl
    omega)
  rw [show (readCall σ a).calldata = Abi.calldata 0xa087a87e [a] from rfl, this]
  simp only [List.map_cons, List.map_nil]

theorem read_sel (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    EvmRules.Evm.shr (224#256) (calldataWord (readCall σ a) 0#256) = 2693245054#256 := by
  rw [SolidCore.Refinement.Generic.calldataWord_eq, calldata_read σ a ha]
  have := shr_cdOf_selectorOf 0xa087a87e [BitVec.ofNat 256 a] (by decide)
  simpa [EvmRules.Evm.shr, bitwiseShr] using this

theorem read_word4 (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    calldataWord (readCall σ a) 4#256 = BitVec.ofNat 256 a := by
  rw [SolidCore.Refinement.Generic.calldataWord_eq, calldata_read σ a ha]
  exact loadWord_cdOf_getD _ [BitVec.ofNat 256 a] 4 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem read_size (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) : (readCall σ a).calldata.size = 36 := by
  rw [calldata_read σ a ha, size_cdOf, size_selectorOf]; simp

end calldata

end SolidCore.Refinement.Reader

/-! ## The run -/

namespace SolidCore.Refinement.Reader

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

set_option linter.deprecated false

/-- The state `read`'s body starts in: the free-memory pointer at 128. -/
def S0 (σ : List (Nat × Nat)) (a : Nat) : State :=
  { State.initial (readCall σ a) with memory := (State.initial (readCall σ a)).memory.store 64 128 }

/-- The state after the call. -/
def T (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) : State := S7 o (S0 σ a) a

/-- The returned word plus one, as the MIR adds. -/
def inc (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) : BitVec 256 := (T o σ a).memory.load 0 + 1#256

/-- The state after the returned word's load. -/
def T4 (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) : State :=
  { T o σ a with memory := (T o σ a).memory.expand 0 32 }

/-- The end of solar's stage0 on a call of `read(a)`. -/
def mirEnd (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) : Halt × State :=
  if callFlag o (W1 o (S0 σ a) a) = 0#256 then
    halt { T o σ a with memory := ((T o σ a).memory.write 0 (o.env "returndatasize" (T o σ a).world []).toNat
      (fun i => returndataByte o (T o σ a).world (0 + i))) } 0 (o.env "returndatasize" (T o σ a).world []) true
  else if EvmRules.Evm.lt (o.env "returndatasize" (T o σ a).world []) 32#256 = 0#256 then
    if EvmRules.Evm.eq (inc o σ a) 0#256 = 0#256 then
      halt { T4 o σ a with memory := (T4 o σ a).memory.store 0 (inc o σ a) } 0 32 false
    else halt { T4 o σ a with memory := ((T4 o σ a).memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true
  else halt (T o σ a) 0 0 true

open SolidCore.Refinement.CallFamilies.Sync (iter_next iter_end) in
theorem run_read (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    Module.run o SolarTV.Export.Reader.stage0 (readCall σ a) 8 = some (mirEnd o σ a) := by
  show iterate (step o σ a) 8 ([], .enter 1 0 0, fun _ => 0, State.initial (readCall σ a)) = _
  rw [iter_next (e0 o σ a 0 _ _), iter_next (e1 o σ a 0 _ _ (read_sel σ a ha)), iter_next (e2 o σ a 1 _ _)]
  rw [show ({ State.initial (readCall σ a) with memory := (State.initial (readCall σ a)).memory.store 64 128 } : State) = S0 σ a from rfl]
  obtain ⟨h0, h0e⟩ := k0 o σ a 0 (fun _ => 0) (S0 σ a) (read_size σ a ha) (read_word4 σ a ha) ha
  rw [iter_next h0, iter_next (k7 o σ a 0 _ (S0 σ a) h0e)]
  rw [show S7 o (S0 σ a) a = T o σ a from rfl]
  unfold mirEnd
  by_cases c1 : callFlag o (W1 o (S0 σ a) a) = 0#256
  · rw [if_pos c1, if_pos c1, iter_end (k1 o σ a 7 _ _)]
  rw [if_neg c1, if_neg c1, iter_next (k2 o σ a 7 _ _)]
  by_cases c2 : EvmRules.Evm.lt (o.env "returndatasize" (T o σ a).world []) 32#256 = 0#256
  swap
  · rw [if_neg c2, if_neg c2, iter_end (k3 o σ a 2 _ _)]
  rw [if_pos c2, if_pos c2]
  obtain ⟨h4, h4e⟩ := k4 o σ a 2 _ (T o σ a)
  rw [iter_next h4]
  rw [show ({ T o σ a with memory := (T o σ a).memory.expand 0 32 } : State) = T4 o σ a from rfl,
    show (T o σ a).memory.load 0 + 1#256 = inc o σ a from rfl]
  by_cases c4 : EvmRules.Evm.eq (inc o σ a) 0#256 = 0#256
  · rw [if_pos c4, if_pos c4, iter_end (k6 o σ a 4 _ _), h4e]
    rfl
  · rw [if_neg c4, if_neg c4, iter_end (k5 o σ a 4 _ _)]

theorem sem_read (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    (moduleSem o).run SolarTV.Export.Reader.stage0 (readCall σ a) =
      some (observe (readCall σ a) (mirEnd o σ a).2 (mirEnd o σ a).1) := by
  show (moduleLayer.result o _ _).map _ = _
  rw [moduleLayer.result_of_ends (show moduleLayer.Ends o SolarTV.Export.Reader.stage0 (readCall σ a) (mirEnd o σ a) from ⟨8, run_read o σ a ha⟩)]
  rfl

/-- info: 'SolidCore.Refinement.Reader.sem_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sem_read

end SolidCore.Refinement.Reader
