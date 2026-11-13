import EthLib.Execution.Evm.Instructions.StackOnly
import EthLib.Execution.Proofs.Evm.Logic.Rules
import SolarTV.Stages.Assembly
import SolarTV.EVMIR.Ops

/-!
# DUPN, SWAPN and EXCHANGE against EthLib

SolarTV's EVM IR takes `dup` and `swap` positions up to 255 and `exchange` pairs up to 31.
DUP1 to DUP16 and SWAP1 to SWAP16 reach the first sixteen; deeper ones, and EXCHANGE, are
EIP-8024's DUPN, SWAPN and EXCHANGE, opcodes with a one-byte immediate that exist from
Glamsterdam. This file ties SolarTV's encoding of them (`SolarTV.Assembly.encodeDepth`,
`encodePair`, as solar's assembler writes them) to EthLib's:

* the immediates are EthLib's, byte for byte, both ways (`decodeSingle_eq`, `encodeSingle_eq`,
  `decodePair_eq`, `encodePair_eq`);
* from Glamsterdam, DUPN, SWAPN and EXCHANGE at the immediate of an EVM IR `dup i`, `swap i` or
  `exchange n m` do what SolarTV's `step` does, two bytes on, for 3 gas (`dupn_step`,
  `swapn_step`, `exchange_step`);
* before Glamsterdam none of the three is an instruction (`stackN_fusaka`), so the assembly
  check at Fusaka (`Assemble.check`) refuses every `dup` and `swap` past the sixteenth word and
  every `exchange` (`Assemble.blockStep_dup`, `blockStep_swap`, `blockStep_exchange`).
-/

namespace SolidCore.Refinement.Solar.Assemble

open EthLib.Base EthLib.Execution EthLib.Execution.Evm GasCosts
open SolarTV.Assembly (encodeDepth decodeDepth depthOk encodePair decodePair pairOk)

/-! ## The immediates are EthLib's -/

theorem decodeSingle_eq (x : UInt8) : decodeSingle x = decodeDepth x.toNat := rfl

theorem encodeSingle_eq (n : Nat) : encodeSingle n = (encodeDepth n).toUInt8 := rfl

theorem decodePair_eq (x : UInt8) : Evm.decodePair x = SolarTV.Assembly.decodePair x.toNat := rfl

theorem encodePair_eq (n m : Nat) :
    Evm.encodePair n m = (SolarTV.Assembly.encodePair n m).toUInt8 := rfl

theorem toNat_encodeDepth (n : Nat) : (encodeDepth n).toUInt8.toNat = encodeDepth n := by
  have := SolarTV.Assembly.encodeDepth_lt n
  simp [Nat.toUInt8, Nat.mod_eq_of_lt this]

/-! ## Before Glamsterdam the three are no instruction -/

theorem stackN_fusaka :
    stackOnlyStep (Meter := Nat) .fusaka .dupn = none ∧
      stackOnlyStep (Meter := Nat) .fusaka .swapn = none ∧
      stackOnlyStep (Meter := Nat) .fusaka .exchange = none := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [stackOnlyStep] <;> decide

/-! ## From Glamsterdam they do what SolarTV's step does -/

variable {fork : Fork}

/-- DUPN at the immediate of EVM IR's `dup i` (depth `i + 1`, past the sixteenth) pushes the
word at position `i`, as `SolarTV.EVM.step` does, two bytes on, for 3 gas. -/
theorem dupn_step {evm : Evm fork Nat} {i : Nat} {x : U256}
    (hd : depthOk (i + 1) = true)
    (himm : immediateByte evm.code evm.pc = (encodeDepth (i + 1)).toUInt8)
    (hgas : 3 ≤ evm.gas) (hx : evm.stack.val[i]? = some x)
    (hlen : evm.stack.val.length < STACK_LIMIT) :
    ∃ after, dupnStep evm = .ok after ∧ after.stack.val = x :: evm.stack.val ∧
      after.pc = evm.pc + 2 ∧ after.gas = evm.gas - 3 := by
  have hdec : decodeSingle (immediateByte evm.code evm.pc) = some (i + 1) := by
    rw [himm, decodeSingle_eq, toNat_encodeDepth]
    exact SolarTV.Assembly.decodeDepth_encodeDepth hd
  have hne : evm.stack.val.length ≠ STACK_LIMIT := by omega
  simp only [dupnStep, chargeGas, OPCODE_DUPN, VERY_LOW, Logic.charge_nat hgas, bind, Except.bind,
    pure, Except.pure, hdec, Nat.add_sub_cancel, hx, pushWord, Stack.push, hne, dite_false]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- SWAPN at the immediate of EVM IR's `swap i` (depth `i + 1`, past the sixteenth) exchanges the
top with the word below it at position `i`, as `SolarTV.EVM.step` does, two bytes on, for 3 gas. -/
theorem swapn_step {evm : Evm fork Nat} {i : Nat} {top x : U256} {rest : List U256}
    (hd : depthOk (i + 1) = true)
    (himm : immediateByte evm.code evm.pc = (encodeDepth (i + 1)).toUInt8)
    (hgas : 3 ≤ evm.gas) (hs : evm.stack.val = top :: rest) (hx : rest[i]? = some x) :
    ∃ after, swapnStep evm = .ok after ∧ after.stack.val = x :: rest.set i top ∧
      after.pc = evm.pc + 2 ∧ after.gas = evm.gas - 3 := by
  have hdec : decodeSingle (immediateByte evm.code evm.pc) = some (i + 1) := by
    rw [himm, decodeSingle_eq, toNat_encodeDepth]
    exact SolarTV.Assembly.decodeDepth_encodeDepth hd
  have h0 : evm.stack.val[0]? = some top := by rw [hs]; rfl
  have h1 : evm.stack.val[i + 1]? = some x := by rw [hs]; exact hx
  simp only [swapnStep, chargeGas, OPCODE_SWAPN, VERY_LOW, Logic.charge_nat hgas, bind,
    Except.bind, pure, Except.pure, hdec, exchangeItems, h0, h1]
  refine ⟨_, rfl, ?_, rfl, rfl⟩
  simp only [advance, hs, List.set_cons_zero, List.set_cons_succ]

/-- EXCHANGE at the immediate of EVM IR's `exchange n m` exchanges the words at positions `n` and
`m`, as `SolarTV.EVM.step` does, two bytes on, for 3 gas. -/
theorem exchange_step {evm : Evm fork Nat} {n m : Nat} {a b : U256}
    (hp : pairOk n m = true)
    (himm : immediateByte evm.code evm.pc = (SolarTV.Assembly.encodePair n m).toUInt8)
    (hgas : 3 ≤ evm.gas) (ha : evm.stack.val[n]? = some a) (hb : evm.stack.val[m]? = some b) :
    ∃ after, exchangeStep evm = .ok after ∧
      after.stack.val = (evm.stack.val.set n b).set m a ∧
      after.pc = evm.pc + 2 ∧ after.gas = evm.gas - 3 := by
  obtain ⟨hdp, hlt⟩ := SolarTV.Assembly.decodePair_encodePair hp
  have hdec : Evm.decodePair (immediateByte evm.code evm.pc) = some (n, m) := by
    rw [himm, decodePair_eq]
    simpa [Nat.toUInt8, Nat.mod_eq_of_lt hlt] using hdp
  simp only [exchangeStep, chargeGas, OPCODE_EXCHANGE, VERY_LOW, Logic.charge_nat hgas, bind,
    Except.bind, pure, Except.pure, hdec, exchangeItems, ha, hb]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- SolarTV's `step` of `exchange` is the exchange EthLib's EXCHANGE makes. -/
theorem step_exchange (ctx : SolarTV.EVM.Context) (n m : Fin 32) (stack : List EvmRules.Word)
    {a b : EvmRules.Word} (ha : stack[n.val]? = some a) (hb : stack[m.val]? = some b) :
    SolarTV.EVM.step ctx (.exchange n m) stack = some ((stack.set n.val b).set m.val a) := by
  simp [SolarTV.EVM.step, ha, hb]

/-- SolarTV's `step` of `dup i` pushes the word at position `i`. -/
theorem step_dup (ctx : SolarTV.EVM.Context) (i : Fin 256) (stack : List EvmRules.Word)
    {x : EvmRules.Word} (hx : stack[i.val]? = some x) :
    SolarTV.EVM.step ctx (.dup i) stack = some (x :: stack) := by
  simp [SolarTV.EVM.step, hx]

/-- SolarTV's `step` of `swap i` exchanges the top with the word below it at position `i`. -/
theorem step_swap (ctx : SolarTV.EVM.Context) (i : Fin 256) (top : EvmRules.Word)
    (rest : List EvmRules.Word) {x : EvmRules.Word} (hx : rest[i.val]? = some x) :
    SolarTV.EVM.step ctx (.swap i) (top :: rest) = some (x :: rest.set i.val top) := by
  simp [SolarTV.EVM.step, hx]

/-- info: 'SolidCore.Refinement.Solar.Assemble.dupn_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dupn_step

/-- info: 'SolidCore.Refinement.Solar.Assemble.swapn_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swapn_step

/-- info: 'SolidCore.Refinement.Solar.Assemble.exchange_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exchange_step

end SolidCore.Refinement.Solar.Assemble
