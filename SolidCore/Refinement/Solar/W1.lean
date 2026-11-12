import SolidCore.Refinement.Evm.WideStorage
import SolidCore.Refinement.Dirty.Source
import SolidCore.Refinement.Compose
import SolarTV.Composition
import SolarTV.Stages.AssemblyCheck
import gen.Main.Evm4
import gen.Main.Bytecode
import SolidCore.Refinement.Solar.AssembleSim

/-!
# w1: solar's EVM IR to bytecode on EthLib

The milestone contract w1,

    contract Main { function f(uint256 a, uint256 b) external pure returns (uint256) {
      return a + b; } }

compiled by solar at commit c7ac11c0 with -Ogas for osaka. program is the final EVM IR program
the assembler lays out (solar -Zemit-lean-stages, the output of the last EVM IR pass, the same
program -Zdump=evm-ir-runtime prints) in SolarTV's EVM IR semantics, and code is the runtime
bytecode solar emits for it, as a literal: bytes_exported checks it against the bytecode solar
exported with the program, and scripts/refinement/check-solar-w1.sh checks its sha256
(runtimeSha256) against solar's --emit=bin-runtime.

* checked and decodes: the bytecode decodes, linearly from offset 0, to exactly the program's
  instructions at the layout -Zvalidate-assembly finds (bb3 at 0x2e, bb7 at 0x32), by the
  kernel's evaluation of SolarTV.Assembly.walk.
* evmir_run: SolarTV's EVM IR semantics runs program on every call f(a, b) of the scope, under
  every oracle, to expected a b, in three blocks of proof fuel.
* target_run: EthLib runs code on the same call to expected a b: one processMessage at Fusaka
  (osaka) from 0x2000 to 0x1000 with 10M gas in one frame (Statement.lean's Target.run), stepped
  opcode by opcode with EthLib's program logic, each step's gas side condition discharged with
  the gas left; the overflow path reaches its REVERT with 9,999,861 gas left. So 10M gas
  suffices on every path of the scope, and runtime gas never makes the bytecode fail there.
* stage: EVM IR to bytecode is a stage on the scope under every oracle, from the generic
  theorem Assemble.stage_of_check (AssembleSim.lean) and check_ok, the kernel's evaluation of
  the checker on program, code and cert; stage_ethLib and assembly (SolarTV.AssemblyStage) with
  oracle, the environment of EthLib's call. stage_run proves the same stage directly, by
  running both sides to the same observable (evmir_run and target_run), as a cross-check.
* mutant_check: the checker rejects the mutant below.
* mutant_not_stage: replacing ADD (0x01, offset 33) by SUB (0x03) makes the stage false, with
  the counterexample f(2, 1), where the program returns 3 and the mutant reverts with
  Panic(0x11); mutant_no_walk: the checker's walk rejects the mutant, because offset 33 decodes
  as SUB where the program has ADD (mutant_decodes_sub).

The scope is every call of f with any two argument words below 2^256, no value and empty
storage (fullScope), as solidity-lean's specifications state.
stageAt is the stage on scopeAt, the same calls from any storage σ, from the same generic
theorem and check_ok. stageAt_run proves it directly, as a cross-check: evmir_run_at and
target_run_at run both sides to expectedAt σ a b, expected a b with σ kept. EthLib's frames
(frame_ok, frame_overflow) hold from every state, so only the reads of the final storage change
(run_of_post_at).

stage no longer depends on this contract's runs: the checker relates the final EVM IR program
to the bytes directly (its lowering to assembly is inside the checker and the generic theorem),
so what is trusted for w1 is the exporter's EVM IR program and the kernel's evaluation of
check_ok. stage_run, the direct proof, remains as a cross-check. Proof fuel (the EVM IR semantics' blocks) and runtime
gas (EthLib's metered 10M) are separate: the first is existential in SolarTV's fuel-free
semantics, the second is checked on every step.

No sorry, native_decide or bv_decide: the theorems below depend on propext, Quot.sound and
Classical.choice only.
-/

namespace SolidCore.Refinement.Solar.W1

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Wide

/-! ## The artifacts -/

/-- The runtime bytecode solar emits for w1, as hex. -/
def runtimeHex : String :=
  "34602e575f3560e01c806313d1aa2e03602e5760443610602e5760043560243581019081106032575f5260205ff35b5f5ffd5b6011602052634e487b715f526024601cfd"

/-- The sha256 of the runtime bytecode, which the check script compares with solar's output. -/
def runtimeSha256 : String := "24d2438e4d77b39b2530aac7af63774b10576eabc3c093d282620ab44403778b"

/-- The runtime bytecode, read big-endian. -/
def runtimeNat : Nat :=
  0x34602e575f3560e01c806313d1aa2e03602e5760443610602e5760043560243581019081106032575f5260205ff35b5f5ffd5b6011602052634e487b715f526024601cfd

def runtimeSize : Nat := 68

/-- The runtime bytecode. -/
def code : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat runtimeNat runtimeSize

/-- Its bytes. -/
def bytes : List Nat := code.data.toList.map (·.toNat)

/-- The selector of `f(uint256,uint256)`. -/
def fSelector : Nat := 0x13d1aa2e

/-- The final EVM IR program of w1's runtime in SolarTV's EVM IR, as solar exports it
(-Zemit-lean-stages, solar-tv/milestone/w1/gen/Main/Evm4.lean: the output of the last EVM IR
pass, cfg-simplify-early), with EVM IR's block ids: block 0 is bb0, 1 is bb3 and 2 is bb7. -/
def program : SolarTV.EVM.Program.Program := SolarTV.Export.Main.evm4

/-- The literal is the bytecode solar exported with the program. -/
theorem bytes_exported : bytes = SolarTV.Export.Main.bytecode := by decide

/-! ## The bytecode is the program's linear decoding -/

open SolarTV.Assembly

/-- The assembly items of the program in layout order: each instruction as its opcode, a
jump as a push of its label and the jump, and a label (a `JUMPDEST`) at each jumped-to block. -/
def items : List Item :=
  [.op 0x34, .pushLabel 1, .op 0x57,
   .push 0, .op 0x35, .push 224, .op 0x1c, .op 0x80, .push 0x13d1aa2e, .op 0x03,
   .pushLabel 1, .op 0x57,
   .push 68, .op 0x36, .op 0x10, .pushLabel 1, .op 0x57,
   .push 4, .op 0x35, .push 36, .op 0x35, .op 0x81, .op 0x01, .op 0x90, .op 0x81, .op 0x10,
   .pushLabel 2, .op 0x57,
   .push 0, .op 0x52, .push 32, .push 0, .op 0xf3,
   .label 1, .push 0, .push 0, .op 0xfd,
   .label 2, .push 17, .push 32, .op 0x52, .push 0x4e487b71, .push 0, .op 0x52, .push 36,
   .push 28, .op 0xfd]

/-- The layout -Zvalidate-assembly finds: bb3 at 0x2e, bb7 at 0x32. -/
def offset (label : Nat) : Nat := if label = 1 then 0x2e else if label = 2 then 0x32 else 0

/-- The instructions the walk reaches, each at its offset. -/
def stream : List (Nat × Instr) := (walk bytes offset 0 items).getD []

theorem walk_eq : walk bytes offset 0 items = some stream := by decide

/-- The checker's walk over w1's bytecode exists: its linear decoding is the program's
instructions at the layout, and each label is a `JUMPDEST` that decoding reaches. -/
theorem checked : Walk bytes offset 0 items stream := walk_sound walk_eq

theorem decodes : decodeFrom bytes (bytes.length + 1) 0 = stream := by
  have := walk_length checked
  exact walk_decodes checked _ (by omega)

/-! ## The calls of the scope -/

/-- `f` and its parameters. -/
def fns : List Fn := [⟨fSelector, [.uint 256, .uint 256]⟩]

/-- Every call of `f` on any two argument words, with no value and empty storage. -/
def scope : Call → Prop := fullScope fns []

/-- What the call of `f(a, b)` shows: the word `a + b` when it fits in 256 bits, and otherwise
a revert with `Panic(0x11)`; no logs, and storage stays empty. -/
def expected (a b : U256) : Observable :=
  if a.toNat + b.toNat < 2 ^ 256 then
    { success := true, output := (natToBytes 32 (a.toNat + b.toNat)).map (·.toNat), logs := [],
      storage := fun _ => 0 }
  else
    { success := false,
      output := (natToBytes 4 0x4e487b71).map (·.toNat) ++ (natToBytes 32 0x11).map (·.toNat),
      logs := [], storage := fun _ => 0 }

theorem scope_callOf {call : Call} (h : scope call) :
    ∃ a b : U256, call = callOf fSelector [a, b] := by
  obtain ⟨fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a, b], _ =>
    refine ⟨BitVec.ofNat 256 a, BitVec.ofNat 256 b, ?_⟩
    have ha := hlt a (by simp)
    have hb := hlt b (by simp)
    have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt ha
    have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt hb
    simp only [callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha', hb']

/-- Every call of `f` on any two argument words, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope fns σ call

/-- What the call of `f(a, b)` from the storage `σ` shows: `expected a b`, with `σ` kept. -/
def expectedAt (σ : List (Nat × Nat)) (a b : U256) : Observable :=
  { expected a b with storage := slotValue σ }

theorem expectedAt_nil (a b : U256) : expectedAt [] a b = expected a b := by
  unfold expectedAt expected
  split <;> rfl

theorem scopeAt_callOf {call : Call} (h : scopeAt call) :
    ∃ a b : U256, ∃ σ, call = { callOf fSelector [a, b] with storage := σ } := by
  obtain ⟨σ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a, b], _ =>
    refine ⟨BitVec.ofNat 256 a, BitVec.ofNat 256 b, σ, ?_⟩
    have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (hlt b (by simp))
    simp only [callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha', hb']

/-! ## SolarTV's EVM IR runs the program to `expected` -/

section Evmir

open SolarTV SolarTV.Machine

theorem shl_or_ofNat (acc b : Nat) (hb : b < 256) :
    (BitVec.ofNat 256 acc <<< 8) ||| BitVec.ofNat 256 b = BitVec.ofNat 256 (acc * 256 + b) := by
  have hand : (BitVec.ofNat 256 acc <<< 8) &&& BitVec.ofNat 256 b = 0 := by
    ext i hi
    rw [BitVec.getElem_and, BitVec.getElem_shiftLeft, ← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
    by_cases h8 : i < 8
    · simp [h8]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
          (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h8)))
      simp [BitVec.getLsbD_ofNat, this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem foldl_word (data : ByteArray) (off : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun (acc : BitVec 256) i =>
        (acc <<< 8) ||| BitVec.ofNat 256 (data.data.getD (off + i) 0).toNat)
        (BitVec.ofNat 256 acc) =
      BitVec.ofNat 256 (l.foldl (fun acc i => acc * 256 + (byteAt data (off + i)).toNat) acc)
  | [], _ => rfl
  | i :: l, acc => by
    simp only [List.foldl_cons]
    have hget : (data.data.getD (off + i) 0) = byteAt data (off + i) := rfl
    rw [hget, shl_or_ofNat _ _ (byteAt data (off + i)).toNat_lt, foldl_word data off l]

/-- CALLDATALOAD in SolarTV is EthLib's: the big-endian word of 32 bytes of call data from the
offset, zero past its end. -/
theorem calldataWord_eq (call : Call) (off : BitVec 256) :
    calldataWord call off = loadWord call.calldata off.toNat 32 := by
  unfold calldataWord loadWord bufferRead bytesToNat
  rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_word, List.foldl_map]

end Evmir

section EvmirRun

open SolarTV SolarTV.Machine SolarTV.EVM.Program

theorem sem_of_run {o : Oracle} {p : SolarTV.EVM.Program.Program} {call : Call} {obs : Observable}
    (n : Nat) (h : (SolarTV.EVM.Program.run o p call n).map (fun r => observe call r.2 r.1) = some obs) :
    (SolarTV.evmirSem o).run p call = some obs := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  have e : SolarTV.EVM.Program.layer.result o p call = some r :=
    SolarTV.EVM.Program.layer.result_of_ends ⟨n, hr⟩
  show (SolarTV.EVM.Program.layer.result o p call).map _ = _
  rw [e]
  rfl

/-- The call data facts the program reads. -/
theorem calldata_callOf (a b : U256) :
    (callOf fSelector [a, b]).calldata = cdOf (selectorOf fSelector) [a, b] := by
  have := calldata_eq_cdOf fSelector [a.toNat, b.toNat] (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> exact BitVec.isLt _)
  simpa [callOf, List.map_map, Function.comp_def] using this

theorem word0 (a b : U256) :
    EvmRules.Evm.shr 224 (calldataWord (callOf fSelector [a, b]) 0) = BitVec.ofNat 256 fSelector := by
  rw [calldataWord_eq, calldata_callOf]
  have := shr_cdOf_selectorOf fSelector [a, b] (by decide)
  simpa [EvmRules.Evm.shr, bitwiseShr] using this

theorem word4 (a b : U256) : calldataWord (callOf fSelector [a, b]) 4 = a := by
  rw [calldataWord_eq, calldata_callOf]
  exact loadWord_cdOf_getD _ [a, b] 4 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem word36 (a b : U256) : calldataWord (callOf fSelector [a, b]) 36 = b := by
  rw [calldataWord_eq, calldata_callOf]
  exact loadWord_cdOf_getD _ [a, b] 36 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem size_callOf (a b : U256) : (callOf fSelector [a, b]).calldata.size = 68 := by
  rw [calldata_callOf, size_cdOf, size_selectorOf]; rfl

namespace Exec
variable {o : Oracle} {call : Call} {b : Nat} {rest : List SolarTV.EVM.Program.Instr} {s : State}

abbrev W := EvmRules.Word

theorem exec_push {v : W} {st : List W} (h : st.length < 1024) :
    exec o call b (.op (.stack (.push v)) :: rest) st s = exec o call b rest (v :: st) s := by
  have h1 : ¬ 1024 < st.length := by omega
  have h2 : ¬ 1024 < st.length + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Except.map, h1, h2]

theorem exec_bin {op : SolarTV.EVM.Op} {f : W → W → W} {x y : W} {st : List W}
    (hf : ∀ ctx x y st, SolarTV.EVM.step ctx op (x :: y :: st) = some (f x y :: st))
    (h : st.length < 1023) :
    exec o call b (.op (.stack op) :: rest) (x :: y :: st) s = exec o call b rest (f x y :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 + 1 := by omega
  have h2 : ¬ 1024 < st.length + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, hf, Except.map, h1, h2]

theorem exec_calldatasize {st : List W} (h : st.length < 1024) :
    exec o call b (.op (.stack .calldatasize) :: rest) st s =
      exec o call b rest (BitVec.ofNat 256 call.calldata.size :: st) s := by
  have h1 : ¬ 1024 < st.length := by omega
  have h2 : ¬ 1024 < st.length + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Except.map, h1, h2, context]

theorem exec_dup0 {x : W} {st : List W} (h : st.length < 1023) :
    exec o call b (.op (.stack (.dup 0)) :: rest) (x :: st) s = exec o call b rest (x :: x :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 := by omega
  have h2 : ¬ 1024 < st.length + 1 + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Except.map, h1, h2]

theorem exec_dup1 {x y : W} {st : List W} (h : st.length < 1022) :
    exec o call b (.op (.stack (.dup 1)) :: rest) (x :: y :: st) s =
      exec o call b rest (y :: x :: y :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 + 1 := by omega
  have h2 : ¬ 1024 < st.length + 1 + 1 + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Except.map, h1, h2]

theorem exec_swap0 {x y : W} {st : List W} (h : st.length < 1023) :
    exec o call b (.op (.stack (.swap 0)) :: rest) (x :: y :: st) s =
      exec o call b rest (y :: x :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 + 1 := by omega
  simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Except.map, h1]

theorem exec_store {x y : W} {st : List W} (h : st.length < 1023) :
    exec o call b (.op .store :: rest) (x :: y :: st) s =
      exec o call b rest st { s with memory := s.memory.store x.toNat y } := by
  have h1 : ¬ 1024 < st.length + 1 + 1 := by omega
  simp [exec, stepOp, h1]

theorem exec_callvalue {st : List W} (h : st.length < 1024) :
    exec o call b (.effect .callvalue 0 :: rest) st s =
      exec o call b rest (BitVec.ofNat 256 call.callvalue :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 := by omega
  simp [exec, Effect.apply, h1]

theorem exec_calldataload {x : W} {st : List W} (h : st.length < 1024) :
    exec o call b (.effect .calldataload 1 :: rest) (x :: st) s =
      exec o call b rest (calldataWord call x :: st) s := by
  have h1 : ¬ 1024 < st.length + 1 := by omega
  simp [exec, Effect.apply, h1]

theorem exec_jumpi {t : Nat} {c : W} {st : List W} (h : st.length < 1023) :
    exec o call b (.jumpi t :: rest) (c :: st) s =
      if c = 0 then exec o call b rest st s else .inr (t, st, s) := by
  have h1 : ¬ 1024 < st.length + 1 + 1 := by omega
  simp [exec, h1]

theorem exec_ret {st : List W} : exec o call b (.ret :: rest) st s = .inl (output s st false) := by
  simp [exec]

theorem exec_revert {st : List W} : exec o call b (.revert :: rest) st s = .inl (output s st true) := by
  simp [exec]


theorem step_shr (ctx : EVM.Context) (x y : W) (st : List W) :
    SolarTV.EVM.step ctx .shr (x :: y :: st) = some (EvmRules.Evm.shr x y :: st) := rfl
theorem step_sub (ctx : EVM.Context) (x y : W) (st : List W) :
    SolarTV.EVM.step ctx .sub (x :: y :: st) = some (EvmRules.Evm.sub x y :: st) := rfl
theorem step_lt (ctx : EVM.Context) (x y : W) (st : List W) :
    SolarTV.EVM.step ctx .lt (x :: y :: st) = some (EvmRules.Evm.lt x y :: st) := rfl
theorem step_add (ctx : EVM.Context) (x y : W) (st : List W) :
    SolarTV.EVM.step ctx .add (x :: y :: st) = some (EvmRules.Evm.add x y :: st) := rfl

end Exec

open Exec

theorem lt_add_self (a b : W) :
    EvmRules.Evm.lt (EvmRules.Evm.add a b) a = if a.toNat + b.toNat < 2 ^ 256 then 0 else 1 := by
  unfold EvmRules.Evm.lt EvmRules.Evm.add
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · have : ¬ (a + b).ult a := by
      simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq, Nat.mod_eq_of_lt h]; omega
    simp only [h, this, ite_true, Bool.cond_false]
  · have : (a + b).ult a := by
      have ha := a.isLt; have hb := b.isLt
      simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, this, ite_false, Bool.cond_true]

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

theorem byte_toNat (v : W) (i : Nat) (hi : i < 32) :
    (SolarTV.Memory.byte v i).toNat = v.toNat / 256 ^ (31 - i) % 256 := by
  unfold SolarTV.Memory.byte
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem read_store (m : Mem) (v : W) :
    (((m.store 0 v).expand 0 32).read 0 32).map BitVec.toNat = (natToBytes 32 v.toNat).map (·.toNat) := by
  rw [← bytes_toNat]
  simp only [Mem.read, Mem.expand, Mem.store, List.map_map]
  simp only [show (32 = 0) = False from by decide, ite_false]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, Nat.zero_add, Nat.zero_le, true_and, hi, ite_true, Nat.sub_zero]
  rw [byte_toNat v i hi]

theorem evmir_run_of (o : Oracle) (call : Call) (a b : W) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 68) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 332507694)
    (h4 : calldataWord call 4 = a) (h36 : calldataWord call 36 = b) :
    (SolarTV.EVM.Program.run o program call 2).map (fun r => observe call r.2 r.1) =
      some (expectedAt call.storage a b) := by
  simp only [SolarTV.EVM.Program.run, iterate, block, program, SolarTV.Export.Main.evm4,
    List.getElem?_cons_zero]
  simp (disch := simp) only [exec_push, exec_callvalue, exec_jumpi, exec_calldataload,
    exec_bin (step_shr), exec_bin (step_sub), exec_bin (step_lt), exec_bin (step_add),
    exec_dup0, exec_dup1, exec_swap0, exec_store, exec_calldatasize, exec_ret]
  simp only [hv, hsize, h0, h4, h36, lt_add_self]
  by_cases hof : a.toNat + b.toNat < 2 ^ 256
  · simp only [hof, ite_true]
    simp (config := {decide := true}) only [BitVec.ofNat_eq_ofNat, ite_true, output, Option.map_some]
    simp only [↓reduceIte, BitVec.reduceToNat, observe, expectedAt, expected, hof,
      Option.some.injEq, Observable.mk.injEq, true_and]
    refine ⟨?_, rfl, ?_⟩
    · rw [read_store]
      simp only [EvmRules.Evm.add, BitVec.toNat_add, Nat.mod_eq_of_lt hof]
    · funext slot
      simp [storageOf, State.initial]
      exact slotValue_mod_mod call.storage slot
  · simp only [hof, ite_false]
    simp (config := {decide := true}) only [BitVec.ofNat_eq_ofNat, ite_true, ite_false,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    simp (disch := simp) only [exec_push, exec_store, exec_revert]
    simp only [output, Option.map_some, ↓reduceIte, BitVec.reduceToNat, observe, expectedAt,
      expected, hof, Option.some.injEq, Observable.mk.injEq]
    refine ⟨trivial, ?_, trivial, ?_⟩
    · simp only [State.initial]
      decide
    · trivial

/-- SolarTV's EVM IR semantics runs w1's final program on every call of f(a, b), under every
oracle, to the observable expected a b. -/
theorem evmir_run (o : Oracle) (a b : U256) :
    (SolarTV.evmirSem o).run program (callOf fSelector [a, b]) = some (expected a b) := by
  rw [← expectedAt_nil]
  exact sem_of_run 2 (evmir_run_of o _ a b rfl (size_callOf a b) (by rw [word0]; rfl) (word4 a b)
    (word36 a b))

/-- The same from any storage `σ`, which the program keeps. -/
theorem evmir_run_at (o : Oracle) (a b : U256) (σ : List (Nat × Nat)) :
    (SolarTV.evmirSem o).run program { callOf fSelector [a, b] with storage := σ } =
      some (expectedAt σ a b) :=
  sem_of_run 2 (evmir_run_of o _ a b rfl (size_callOf a b)
    (by have h := word0 a b; rw [show BitVec.ofNat 256 fSelector = 332507694 from rfl] at h; exact h)
    (word4 a b) (word36 a b))

end EvmirRun

/-! ## EthLib runs the bytecode to the same observable -/

section Target

open EthLib.Execution.Evm.Logic GasCosts SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- When $a + b$ fits, EthLib's frame returns the word from every state: every opcode stepped by
EthLib's program logic from pc 0 with 10M gas, its branches decided from the call data and the
bound. -/
theorem frame_ok (a b : U256) (hof : a.toNat + b.toNat < 2 ^ 256) :
    ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf fSelector) [a, b] →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty)
        (Post (expected a b) st ss) := by
  have he : expected a b =
      ⟨true, (natToBytes 32 (a.toNat + b.toNat)).map (fun x => x.toNat), [], fun _ => 0⟩ := by
    rw [expected, ite_cond_eq_true _ _ (eq_true hof)]
  rw [he]
  wide_tgt [code, runtimeNat, runtimeSize, fSelector]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- When it overflows, EthLib's frame reverts with Panic(0x11) from every state. -/
theorem frame_overflow (a b : U256) (hof : ¬ a.toNat + b.toNat < 2 ^ 256) :
    ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf fSelector) [a, b] →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty)
        (Post (expected a b) st ss) := by
  have he : expected a b =
      ⟨false, (natToBytes 4 0x4e487b71).map (fun x => x.toNat) ++
        (natToBytes 32 0x11).map (fun x => x.toNat), [], fun _ => 0⟩ := by
    rw [expected, ite_cond_eq_false _ _ (eq_false hof)]
  rw [he]
  wide_tgt [code, runtimeNat, runtimeSize, fSelector]
  refine revert_post (by decide) ?_ ?_ ?_ rfl ?_
  · evm_code [code, runtimeNat, runtimeSize, fSelector]
  · evm_code [code, runtimeNat, runtimeSize, fSelector]
  · wide_mem
  · simp only
    decide +kernel

/-- EthLib's frame of every call of f(a, b) stops as expected a b shows, from every state. -/
theorem frame (a b : U256) :
    ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf fSelector) [a, b] →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty)
        (Post (expected a b) st ss) := by
  by_cases hof : a.toNat + b.toNat < 2 ^ 256
  · exact frame_ok a b hof
  · exact frame_overflow a b hof

theorem expected_logs (a b : U256) : (expected a b).logs = [] := by
  unfold expected; split <;> rfl

/-- EthLib runs solar's bytecode on every call of f(a, b) to the observable expected a b. -/
theorem target_run (a b : U256) :
    Target.run code (callOf fSelector [a, b]) = some (expected a b) :=
  run_of_post code fSelector [a, b] _ (expected_logs a b)
    (fun _ => by unfold expected; split <;> rfl) (frame a b)

/-- EthLib runs solar's bytecode on every call of f(a, b) from any storage `σ` to the
observable expectedAt σ a b. -/
theorem target_run_at (a b : U256) (σ : List (Nat × Nat)) :
    Target.run code { callOf fSelector [a, b] with storage := σ } = some (expectedAt σ a b) :=
  run_of_post_at code fSelector [a, b] σ _ (expected_logs a b) (fun _ => rfl) (frame a b)

end Target

/-! ## The stage -/

/-- The oracle of EthLib's call: one frame at 0x1000 called by 0x2000 (also the origin), in
Target.blockEnv (chain 1, block 1 at time 1, gas limit 30M, coinbase 0, base fee 0) and
Target.txEnv (gas price 0). No call has returned, so return data is empty, and the frame calls
nothing, so call results never arise. GAS, balances and every other read the EVM IR semantics
asks the oracle for are 0: w1 reads none of them, and the stage holds under every oracle
(stage). -/
def oracle : SolarTV.Machine.Oracle where
  env name _ _ :=
    if name = "caller" ∨ name = "origin" then BitVec.ofNat 256 callerAddress
    else if name = "address" then BitVec.ofNat 256 selfAddress
    else if name = "chainid" ∨ name = "number" ∨ name = "timestamp" then 1
    else if name = "gaslimit" then 30000000
    else 0
  result _ := 0
  storageAfter _ _ := 0
  transientAfter _ _ := 0
  keccak _ := 0
  caller := BitVec.ofNat 160 callerAddress

/-- The same stage, shown directly by running both sides to the same observable: the
cross-check of stage. -/
theorem stage_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scope := by
  intro call hc obs hrun
  obtain ⟨a, b, rfl⟩ := scope_callOf hc
  rw [evmir_run o a b] at hrun
  cases hrun
  exact target_run a b

/-- The certificate of the check: each block's offset (bb3 at 0x2e, bb7 at 0x32), the stack
height each block needs on entry (none), and the bound on memory (64 bytes). -/
def cert : Assemble.Cert := { offsets := [0, 0x2e, 0x32], needs := [0, 0, 0], top := 64 }

/-- The checker's lowering of the program is the item list above. -/
theorem lower_eq : Assemble.lower program cert = items := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check program code cert = true := by decide +kernel

theorem scope_facts {call : Call} (h : scope call) : call.callvalue = 0 ∧ call.storage = [] := by
  obtain ⟨a, b, rfl⟩ := scope_callOf h
  exact ⟨rfl, rfl⟩

/-- EVM IR to bytecode is a stage for w1 on the scope, under every oracle: every observable
SolarTV's EVM IR semantics gives for the final program, EthLib gives for solar's bytecode. It
is the generic theorem for every program and code the checker accepts, at check_ok. -/
theorem stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scope :=
  Assemble.stage_of_check check_ok o fun _ h => (scope_facts h).1

/-- EVM IR to bytecode is a stage for w1 on every call, with any value, call data and storage,
under every oracle: the generic theorem at check_ok. -/
theorem stageAll (o : SolarTV.Machine.Oracle) (scope : Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scope :=
  Assemble.stage_of_check_all check_ok o scope

/-- The same with EthLib's environment as the oracle. -/
theorem stage_ethLib : SolarTV.Stage (SolarTV.evmirSem oracle) ethLib program code scope := stage oracle

/-- EVM IR to bytecode is a stage for w1 on every call of f with no value from any storage, under
every oracle: the generic theorem at the same check_ok, since every call of scopeAt has no
value. -/
theorem stageAt (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scopeAt :=
  Assemble.stage_of_check check_ok o fun _ ⟨_, _, _, _, _, _, h⟩ => by rw [h]

/-- The same stage from any storage proved directly, by running both sides to the same observable
(evmir_run_at and target_run_at), as a cross-check of stageAt. -/
theorem stageAt_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scopeAt := by
  intro call hc obs hrun
  obtain ⟨a, b, σ, rfl⟩ := scopeAt_callOf hc
  rw [evmir_run_at o a b σ] at hrun
  cases hrun
  exact target_run_at a b σ

/-- It is SolarTV's assembly stage, which mir_to_bytecode composes. -/
theorem assembly : SolarTV.AssemblyStage ethLib oracle program (show ethLib.Prog from code) scope :=
  stage oracle

/-! ## A one-byte mutation is caught -/

/-- The bytecode with its ADD (0x01, at offset 33) replaced by SUB (0x03). -/
def mutantNat : Nat :=
  0x34602e575f3560e01c806313d1aa2e03602e5760443610602e5760043560243581039081106032575f5260205ff35b5f5ffd5b6011602052634e487b715f526024601cfd

def mutant : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat mutantNat runtimeSize

def mutantBytes : List Nat := mutant.data.toList.map (·.toNat)

/-- It differs from solar's bytecode in exactly one byte, at offset 33. -/
theorem mutant_one_byte :
    mutantBytes.length = bytes.length ∧ bytes[33]? = some 0x01 ∧ mutantBytes[33]? = some 0x03 ∧
      ∀ i, i ≠ 33 → mutantBytes[i]? = bytes[i]? := by
  refine ⟨by decide, by decide, by decide, fun i hi => ?_⟩
  by_cases h : i < 68
  · revert hi; revert i; decide
  · have h1 : bytes.length = 68 := by decide
    have h2 : mutantBytes.length = 68 := by decide
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The checker rejects the mutant: at offset 33 it decodes SUB where the program has ADD. -/
theorem mutant_decodes_sub : decode mutantBytes 33 = some (.op 0x03, 34) ∧
    items[22]? = some (.op 0x01) := by decide

theorem mutant_rejected : walk mutantBytes offset 0 items = none := by decide

set_option maxRecDepth 100000 in
/-- The generic checker rejects the mutant too. -/
theorem mutant_check : Assemble.check program mutant cert = false := by decide +kernel

theorem mutant_no_walk (stream : List (Nat × Instr)) : ¬ Walk mutantBytes offset 0 items stream :=
  no_walk mutant_rejected stream

/-- The call f(2, 1). -/
def call21 : Call := callOf fSelector [2, 1]

theorem call21_scope : scope call21 :=
  ⟨⟨fSelector, [.uint 256, .uint 256]⟩, List.mem_singleton_self _, [2, 1], rfl,
    by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; omega, rfl⟩

/-- On f(2, 1) the final EVM IR program returns 3. -/
theorem evmir_call21 (o : SolarTV.Machine.Oracle) :
    (SolarTV.evmirSem o).run program call21 =
      some ⟨true, (natToBytes 32 3).map (·.toNat), [], fun _ => 0⟩ := by
  rw [call21, evmir_run o 2 1, expected, if_pos (by decide)]
  rfl

section Mutant

open EthLib.Execution.Evm.Logic GasCosts SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- On f(2, 1) the mutant computes 2 - 1 = 1, which its overflow check takes for an overflow
since 1 < 2: it reverts with Panic(0x11). -/
theorem mutant_call21 :
    Target.run mutant call21 =
      some ⟨false, (natToBytes 4 0x4e487b71).map (fun x => x.toNat) ++
        (natToBytes 32 0x11).map (fun x => x.toNat), [], fun _ => 0⟩ := by
  refine run_of_post mutant fSelector [2, 1] _ rfl (fun _ => rfl) ?_
  wide_tgt [mutant, mutantNat, runtimeSize, fSelector]
  refine revert_post (by decide) ?_ ?_ ?_ rfl ?_
  · evm_code [mutant, mutantNat, runtimeSize, fSelector]
  · evm_code [mutant, mutantNat, runtimeSize, fSelector]
  · wide_mem
  · simp only
    decide +kernel

end Mutant

/-- The mutation makes the stage false: on f(2, 1), in the scope, the program returns 3 and the
mutant reverts. -/
theorem mutant_not_stage (o : SolarTV.Machine.Oracle) :
    ¬ SolarTV.Stage (SolarTV.evmirSem o) ethLib program mutant scope := by
  intro h
  have := h call21 call21_scope _ (evmir_call21 o)
  change Target.run mutant call21 = _ at this
  rw [mutant_call21] at this
  cases this

/-- info: 'SolidCore.Refinement.Solar.W1.stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage

/--
info: 'SolidCore.Refinement.Solar.W1.stage_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_run

/-- info: 'SolidCore.Refinement.Solar.W1.stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAt

/--
info: 'SolidCore.Refinement.Solar.W1.stageAt_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stageAt_run

/-- info: 'SolidCore.Refinement.Solar.W1.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.W1.mutant_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutant_check

/--
info: 'SolidCore.Refinement.Solar.W1.assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms assembly

/--
info: 'SolidCore.Refinement.Solar.W1.mutant_not_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mutant_not_stage

/-- info: 'SolidCore.Refinement.Solar.W1.mutant_no_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutant_no_walk

/-- info: 'SolidCore.Refinement.Solar.W1.decodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodes

end SolidCore.Refinement.Solar.W1
