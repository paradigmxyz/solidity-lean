import SolidCore.Refinement.Evm.Lemmas
import SolidCore.Refinement.Bytecode.C1
import EthLib.Execution.Evm.Call.MessageCall
/-!
# c1 on EthLib: solar's bytecode for `f(uint8 x) = x * 3 + 1`

Source: `scripts/refinement/corpus/c1.sol`

    contract Main { function f(uint8 x) external pure returns (uint8) { return x * 3 + 1; } }

The bytecode is `Bytecode.C1.Main.runtimeNat`, which `scripts/refinement/gen.sh`
writes from solar at the commit in `scripts/refinement/solar-rev`. The proofs
step through those exact bytes, so they stop checking if solar's output changes.

At the pinned commit the code is 83 bytes (selector `f(uint8)` = 0x3120d434):

    pc  opcode                 stack after, top first
    00  CALLVALUE              [v]
    01  PUSH1 0x3d; JUMPI      []                  v ≠ 0 → revert(0, 0)
    04  PUSH0; CALLDATALOAD    [cd[0:32]]
    06  PUSH1 0xe0; SHR        [sel]
    09  DUP1; PUSH4 0x3120d434; SUB; PUSH1 0x3d; JUMPI
                               [sel]               sel ≠ f → revert(0, 0)
    13  PUSH1 0x24; CALLDATASIZE; LT; PUSH1 0xff; PUSH1 0x04; CALLDATALOAD; GT; OR
        PUSH1 0x3d; JUMPI      [sel]               short or x > 255 → revert(0, 0)
    21  PUSH1 0x04; CALLDATALOAD; PUSH1 0x03; MUL; DUP1; PUSH1 0x01; ADD; SWAP1
        PUSH1 0xff; LT; DUP2; PUSH1 0xff; LT; OR; PUSH1 0x41; JUMPI
                               [3x+1, sel]         overflow → 0x41
    37  PUSH0; MSTORE; PUSH1 0x20; PUSH0; RETURN   return word(3x+1)
    3d  JUMPDEST; PUSH0; PUSH0; REVERT             revert(0, 0)
    41  JUMPDEST; mem[32:64] = 0x11; mem[0:32] = 0x4e487b71
        PUSH1 0x24; PUSH1 0x1c; REVERT             revert Panic(0x11)

Results, kernel-checked with no `sorry`, `native_decide` or `bv_decide`:

* `frame_spec`: from pc 0, at any fork from Shanghai, with no value, call data
  `cd w` and 10M gas, the frame stops with the error and output `spec w` and
  leaves state and substate as they were.
* `processMessage_spec`: the same for the whole `processMessage` at Fusaka, from
  any state and substate.
* `frame_spec_value`: a nonzero call value reverts with empty output.
* `processMessage_reject`: a wrong selector or call data shorter than 36 bytes
  reverts with empty output.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open SolidCore.Refinement.Evm SolidCore.Refinement.Evm.Logic
open SolidCore.Refinement.Bytecode.C1

namespace SolidCore.Refinement.C1
/-- solar's runtime bytecode for `Main`, from the generated file. -/
def codeNat : Nat := Main.runtimeNat

/-- The bytecode as EthLib runs it. -/
def code : ByteArray := NatCode.ofNat codeNat Main.runtimeSize
def sel : ByteArray := ⟨#[0x31, 0x20, 0xd4, 0x34]⟩
def cd (w : U256) : ByteArray := sel ++ wordBytes w

theorem size_cd (w : U256) : (cd w).size = 36 := by
  simp [cd, ByteArray.size_append, size_wordBytes]; rfl
theorem shr_cd (w : U256) : bitwiseShr (224#256) (loadWord (cd w) 0 32) = 824235060#256 := by
  have := bitwiseShr_loadWord_zero (cd w) 4 (by decide) (by decide)
  rw [show BitVec.ofNat 256 (8 * (32 - 4)) = 224#256 from rfl] at this
  rw [this, cd, bufferRead_append_of_le _ _ (by decide)]
  rfl
theorem load4_cd (w : U256) : loadWord (cd w) 4 32 = w := loadWord_append_wordBytes sel w

macro "c1_step" : tactic => `(tactic| first
  | (refine' Triple.seq (push0 (by assumption) ?lt ?op ?gas ?room) ?next
     case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
     case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
     case gas => evm_gas
     case room => evm_room
     all_goals evm_tidy)
  | evm_step [code, codeNat, Main.runtimeNat, Main.runtimeSize])

variable {fork : Fork}

theorem Spec.close {P R Q : Evm fork Nat → Prop} (h : Spec fork P R) (imp : ∀ e, R e → Q e) :
    Triple (Step fork) P (fun evm => evm.running = false ∧ Q evm) :=
  Spec.consequence h (fun _ h => h) imp

def panicData : ByteArray := ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ wordBytes 0x11

/-- The error and the output the spec gives for `f(w)`. -/
def spec (w : U256) : Option EvmError × ByteArray :=
  if 256 ≤ w.toNat then (some .revert, .empty)
  else if 255 < 3 * w.toNat + 1 then (some .revert, panicData)
  else (none, wordBytes (3 * w + 1))

def Post (w : U256) (st : State.TransactionState) (ss : Substate) (evm : Evm fork Nat) : Prop :=
  evm.error = (spec w).1 ∧ evm.output = (spec w).2 ∧ evm.state = st ∧ evm.substate = ss

theorem spec_dirty {w : U256} (h : 256 ≤ w.toNat) : spec w = (some .revert, .empty) := by
  simp [spec, h]
theorem spec_panic {w : U256} (h : w.toNat < 256) (h2 : 255 < 3 * w.toNat + 1) :
    spec w = (some .revert, panicData) := by
  simp [spec, h2, show ¬ 256 ≤ w.toNat by omega]
theorem spec_ok {w : U256} (h2 : 3 * w.toNat + 1 ≤ 255) :
    spec w = (none, wordBytes (3 * w + 1)) := by
  simp [spec, show ¬ 255 < 3 * w.toNat + 1 by omega, show ¬ 256 ≤ w.toNat by omega]

theorem byz (hf : Fork.shapella ≤ fork) : Fork.byzantium ≤ fork := by
  refine' Nat.le_trans ?_ hf; decide

theorem frame_spec (hf : Fork.shapella ≤ fork) (w : U256) (message : Message fork)
    (hv : message.value = 0) (hd : message.data = cd w) (st ss) :
    Spec fork (At code message 0 [] .empty 10000000 st ss .empty) (Post w st ss) := by
  c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step
  rw [hd, shr_cd]
  c1_step; c1_step; c1_step
  c1_step; c1_step
  c1_step; c1_step
  rw [hd, size_cd]
  c1_step; c1_step; c1_step; c1_step
  rw [hd, load4_cd]
  c1_step; c1_step; c1_step
  by_cases hw : w.toNat < 256
  · have h0 : bitwiseOr (greaterThan w 255#256) (lessThan 36#256 36#256) = 0 := by
      simp [bitwiseOr, greaterThan, lessThan]; bv_omega
    c1_step
    c1_step; c1_step
    rw [hd, load4_cd]
    c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step
    have hm3 : (mul (3#256) w).toNat = 3 * w.toNat := by
      simp only [mul, BitVec.toNat_mul]; rw [Nat.mod_eq_of_lt] <;> simp <;> omega
    have hv3 : (add (1#256) (mul (3#256) w)).toNat = 1 + 3 * w.toNat := by
      simp only [add, BitVec.toNat_add, hm3]; rw [Nat.mod_eq_of_lt] <;> simp <;> omega
    by_cases ho : 3 * w.toNat + 1 ≤ 255
    · have h2 : bitwiseOr (lessThan (255#256) (add (1#256) (mul (3#256) w))) (lessThan (255#256) (mul (3#256) w)) = 0 := by
        simp only [bitwiseOr, lessThan, hv3, hm3, BitVec.toNat_ofNat]; split <;> split <;> first | decide | omega
      c1_step
      c1_step
      c1_step
      refine' Triple.seq (mstore ?lt ?op ?gas) ?_
      case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case gas => decide
      have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by decide
      simp only [hext, show (0 : U256).toNat = 0 from rfl]
      rw [memoryWrite_whole (by rw [size_memoryExtend, size_wordBytes]; rfl)]
      c1_step; c1_step
      refine Spec.close (Logic.«return» ?lt ?op ?gas) ?_
      case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case gas => rw [size_wordBytes]; decide
      rintro e ⟨-, herr, hout, -, hs, hss⟩
      refine ⟨?_, ?_, hs, hss⟩
      · rw [herr, spec_ok ho]; rfl
      · rw [hout, size_wordBytes, show (extendMemory 32 [((0 : U256), 32#256)]).expandBy = 0 by decide,
          memoryExtend_zero]
        have := memoryReadBytes_whole (memory := wordBytes (add (1#256) (mul (3#256) w)))
        rw [size_wordBytes] at this
        rw [show (0 : U256).toNat = 0 from rfl, show (32#256).toNat = 32 from rfl, this, spec_ok ho]
        show wordBytes _ = wordBytes _
        congr 1
        simp only [add, mul]; exact BitVec.add_comm _ _
    · have h2 : bitwiseOr (lessThan (255#256) (add (1#256) (mul (3#256) w))) (lessThan (255#256) (mul (3#256) w)) ≠ 0 := by
        simp only [bitwiseOr, lessThan, hv3, hm3, BitVec.toNat_ofNat]; split <;> split <;> first | decide | omega
      c1_step
      c1_step; c1_step; c1_step
      c1_step
      refine' Triple.seq (mstore ?lt ?op ?gas) ?_
      case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case gas => decide
      have hext : extendMemory ByteArray.empty.size [(32#256, (32 : U256))] = ⟨6, 64⟩ := by decide
      simp only [hext]
      c1_step; c1_step
      refine' Triple.seq (mstore ?lt ?op ?gas) ?_
      case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case gas => decide
      have hext2 : extendMemory (memoryWrite (memoryExtend ByteArray.empty 64) 32 (wordBytes 17#256)).size
          [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by decide
      simp only [hext2, memoryExtend_zero]
      c1_step; c1_step
      refine Spec.close (revert (byz hf) ?lt ?op ?gas) ?_
      case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
      case gas => decide
      rintro e ⟨-, herr, hout, -, hs, hss⟩
      refine ⟨?_, ?_, hs, hss⟩
      · rw [herr, spec_panic hw (by omega)]; rfl
      · rw [hout, spec_panic hw (by omega)]
        decide +kernel
  · have h0 : bitwiseOr (greaterThan w 255#256) (lessThan 36#256 36#256) ≠ 0 := by
      simp [bitwiseOr, greaterThan, lessThan]; bv_omega
    c1_step
    c1_step; c1_step; c1_step
    refine Spec.close (revert (byz hf) ?lt ?op ?gas) ?_
    case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case gas => decide
    rintro e ⟨-, herr, hout, -, hs, hss⟩
    refine ⟨?_, ?_, hs, hss⟩
    · rw [herr, spec_dirty (by omega)]; rfl
    · rw [hout, spec_dirty (by omega)]
      decide +kernel

/-- The interpreter loop, from the frame that `processMessage` starts, ends as the spec says. -/
theorem runFrame_spec (hf : Fork.shapella ≤ fork) (w : U256) (message : Message fork)
    (hcode : message.code = code) (hv : message.value = 0) (hd : message.data = cd w)
    (st : State.TransactionState) (ss : Substate) (g : Nat) (hg : g = 10000000) {bound : Nat}
    {runChild : MessageRunner fork Nat bound}
    (within : GasMeter.gasHeld (startFrame message st ss g).gas ≤ bound) :
    ∃ after, runFrame (step fork) (step_decreases fork) bound runChild
        (startFrame message st ss g) within = .ok after ∧
      after.running = false ∧ after.error = (spec w).1 ∧ after.output = (spec w).2 ∧
      after.state = st ∧ after.substate = ss := by
  obtain ⟨after, h, herr, hout, hs, hss⟩ := Spec.runFrame (frame_spec hf w message hv hd st ss)
    (evm := startFrame message st ss g)
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, hg, rfl, rfl,
      rfl, rfl, rfl, rfl⟩ within
  exact ⟨after, h, running_runFrame h, herr, hout, hs, hss⟩

/-- Any spec of the frame at pc 0 gives the result of the interpreter loop, from any equation for
the run (general: any code, any postcondition). -/
theorem runFrame_of_spec {c : ByteArray} {message : Message fork} {st : State.TransactionState}
    {ss : Substate} {g : Nat} {Q : Evm fork Nat → Prop} (hcode : message.code = c)
    (h : Spec fork (At c message 0 [] .empty g st ss .empty) Q) {bound : Nat}
    {runChild : MessageRunner fork Nat bound}
    {within : GasMeter.gasHeld (startFrame message st ss g).gas ≤ bound} {result}
    (hr : runFrame (step fork) (step_decreases fork) bound runChild
        (startFrame message st ss g) within = result) :
    ∃ after, result = .ok after ∧ after.running = false ∧ Q after := by
  obtain ⟨after, h', hq⟩ := Spec.runFrame h (evm := startFrame message st ss g)
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩ within (runChild := runChild)
  exact ⟨after, hr ▸ h', running_runFrame h', hq⟩

/-- A spec of the frame of a message with no value, that fixes the error and the output and
leaves state and substate alone, gives the result of `processMessage` at Fusaka (general: any
code that is no precompile). A failed call is rolled back, so the state is known only on success. -/
theorem processMessage_of_spec {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (hv : message.value = 0)
    (hpre : precompileAddress .fusaka message = none) {E : Option EvmError} {O : ByteArray}
    {Q : State.TransactionState → Substate → Evm .fusaka Nat → Prop}
    (h : ∀ st ss, Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) (Q st ss))
    (hQ : ∀ st ss e, Q st ss e → e.error = E ∧ e.output = O ∧ e.state = st ∧ e.substate = ss)
    (st : State.TransactionState) (ss : Substate) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = E ∧ evm.1.output = O ∧ evm.1.substate = ss ∧
      (E = none → evm.1.state = st) := by
  rw [processMessage]
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre]
  split
  · rename_i htr; exact absurd htr.2 (by simp [hv])
  simp only [pure, Except.pure, bind, Except.bind]
  split
  · rename_i e hr
    obtain ⟨after, h', -⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
  · rename_i after hr
    obtain ⟨after', h', -, hq⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
    obtain ⟨herr, hout, hst, hsub⟩ := hQ _ _ _ hq
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> simp [hout]
    · simp only [rollbackOnError]; split <;> simp [hsub, hv]
    · intro hE
      simp only [rollbackOnError, herr, hE, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact hst

/-- The whole message call of `f` on call data `selector ++ toBeBytes w`, at Fusaka
with 10M gas and no value: for every 256-bit `w`, the error and the output are the spec. -/
theorem processMessage_spec (w : U256) (message : Message .fusaka)
    (hcode : message.code = code) (hv : message.value = 0) (hd : message.data = cd w)
    (hgas : message.gas = 10000000) (hpre : precompileAddress .fusaka message = none)
    (st : State.TransactionState) (ss : Substate) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = (spec w).1 ∧ evm.1.output = (spec w).2 ∧ evm.1.substate = ss ∧
      ((spec w).1 = none → evm.1.state = st) :=
  processMessage_of_spec message hcode hv hpre
    (fun st ss => hgas ▸ frame_spec (by decide) w message hv hd st ss)
    (fun _ _ _ h => h) st ss

/-- The empty revert, as a postcondition. -/
def Rejected (st : State.TransactionState) (ss : Substate) (evm : Evm fork Nat) : Prop :=
  evm.error = some .revert ∧ evm.output = .empty ∧ evm.state = st ∧ evm.substate = ss

theorem rejected_of_halted {st ss g} {e : Evm fork Nat}
    (h : Halted true (memoryReadBytes (memoryExtend ByteArray.empty
      (extendMemory ByteArray.empty.size [((0 : U256), (0 : U256))]).expandBy) (0 : U256).toNat
      (0 : U256).toNat) g st ss e) : Rejected st ss e := by
  obtain ⟨-, herr, hout, -, hs, hss⟩ := h
  exact ⟨herr, by rw [hout]; decide +kernel, hs, hss⟩

/-- Nonzero call value: the non-payable function reverts with no data, for any call data. -/
theorem frame_spec_value (hf : Fork.shapella ≤ fork) (message : Message fork)
    (hv : message.value ≠ 0) (st ss) :
    Spec fork (At code message 0 [] .empty 10000000 st ss .empty) (Rejected st ss) := by
  c1_step; c1_step; c1_step; c1_step; c1_step; c1_step
  refine Spec.close (revert (byz hf) ?lt ?op ?gas) ?_
  case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
  case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
  case gas => decide
  exact fun e h => rejected_of_halted h

/-- No call value, and call data whose first 4 bytes are not `f`'s selector, or that is shorter
than 36 bytes: the call reverts with no data. -/
theorem frame_spec_reject (hf : Fork.shapella ≤ fork) (message : Message fork)
    (hv : message.value = 0)
    (hbad : bytesToNat (bufferRead message.data 0 4) ≠ 0x3120d434 ∨ message.data.size < 36)
    (st ss) :
    Spec fork (At code message 0 [] .empty 10000000 st ss .empty) (Rejected st ss) := by
  have hsel := bitwiseShr_loadWord_zero message.data 4 (by decide) (by decide)
  rw [show BitVec.ofNat 256 (8 * (32 - 4)) = 224#256 from rfl] at hsel
  have hlt4 := bytesToNat_lt (bufferRead message.data 0 4)
  rw [bufferRead_length] at hlt4
  c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step
  rw [hsel]
  c1_step; c1_step; c1_step
  c1_step
  by_cases hs : bytesToNat (bufferRead message.data 0 4) = 0x3120d434
  · have hsize : message.data.size < 36 := hbad.resolve_left (by simpa using hs)
    rw [hs]
    have h0 : sub (824235060#256) (BitVec.ofNat 256 0x3120d434) = 0 := by decide
    c1_step
    c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step; c1_step
    have h1 : bitwiseOr (greaterThan (loadWord message.data 4 32) 255#256)
        (lessThan (BitVec.ofNat 256 message.data.size) 36#256) ≠ 0 := by
      have : lessThan (BitVec.ofNat 256 message.data.size) 36#256 = 1 := by
        unfold lessThan
        rw [ite_eq_left]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hsize
      rw [this]
      intro h
      have := congrArg (BitVec.getLsbD · 0) h
      simp [bitwiseOr] at this
    c1_step; c1_step; c1_step; c1_step; c1_step
    refine Spec.close (revert (byz hf) ?lt ?op ?gas) ?_
    case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case gas => decide
    exact fun e h => rejected_of_halted h
  · have h0 : sub (824235060#256) (BitVec.ofNat 256 (bytesToNat (bufferRead message.data 0 4))) ≠ 0 := by
      intro h
      apply hs
      have h' : BitVec.ofNat 256 (bytesToNat (bufferRead message.data 0 4)) = 824235060#256 := by
        simp only [sub] at h; bv_omega
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    c1_step
    c1_step; c1_step; c1_step
    refine Spec.close (revert (byz hf) ?lt ?op ?gas) ?_
    case lt => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case op => evm_code [code, codeNat, Main.runtimeNat, Main.runtimeSize]
    case gas => decide
    exact fun e h => rejected_of_halted h

/-- Wrong selector or short call data, as a whole message call: it reverts with no data. -/
theorem processMessage_reject (message : Message .fusaka)
    (hcode : message.code = code) (hv : message.value = 0) (hgas : message.gas = 10000000)
    (hpre : precompileAddress .fusaka message = none)
    (hbad : bytesToNat (bufferRead message.data 0 4) ≠ 0x3120d434 ∨ message.data.size < 36)
    (st : State.TransactionState) (ss : Substate) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = some .revert ∧ evm.1.output = .empty ∧ evm.1.substate = ss ∧
      (some EvmError.revert = none → evm.1.state = st) :=
  processMessage_of_spec message hcode hv hpre
    (fun st ss => hgas ▸ frame_spec_reject (by decide) message hv hbad st ss)
    (fun _ _ _ h => h) st ss

end SolidCore.Refinement.C1
