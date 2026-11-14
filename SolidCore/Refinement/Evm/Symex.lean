import SolidCore.Refinement.Evm.Calldata
import SolidCore.Refinement.Statement
import Std.Tactic.BVDecide

/-!
# Symbolic execution of a dispatcher on dirty call data

A per-contract theorem that solar's bytecode rejects dirty ABI arguments is one
call of the tactic `dirty_symex` here, under the generic lemma `dirty_of_frame`.

`dirty_of_frame` reduces the statement about `Target.run` (as
`Statement.lean` runs a call) to a frame specification: from pc 0 with no value,
10M gas and call data `cdOf (selectorOf s) ws`, where the argument words `ws`
are not all clean, the frame halts with `Reverted` (the revert error and empty
output). It goes through `processMessage_reverts`, the generic form of C1's
`processMessage_of_spec` for a frame that reverts.

`dirty_symex [code rules]` proves that frame specification:

1. it splits the argument list into as many words as there are parameters and
   turns the dirty hypothesis into one fact about one word per case, stated on
   bit vectors (`cleanBv`);
2. it steps the bytecode with EthLib's `evm_step`, and PUSH0 with `push0`,
   rewriting after each step the frame's words with the call-data rules of
   `Calldata.lean` (selector, argument words, size), the call value 0 and the
   EVM's comparison, shift and sign-extension operations as bit-vector terms,
   which `simp` evaluates when they are ground;
3. at each JUMPI it takes the branch the condition decides, by `decide` or
   from the dirty fact, and otherwise splits on the condition (`jumpi_split`)
   and closes the branches whose path condition the dirty fact refutes; both
   go through `symex_bv`, which rewrites the condition into comparisons of
   the words' values (`symex_bits`) and closes it by `bv_omega`, a
   kernel-checked proof, and falls back to `bv_decide` only where that fails;
4. it steps MSTORE, evaluating the growth of a memory of known size;
5. it closes a REVERT of 0 bytes with `revert_empty`.

A path that reaches RETURN or STOP, or an opcode no rule covers, is left as an
unsolved goal, so the theorem fails rather than claim a rejection it has not
shown.

`bv_decide` trusts Lean's compiler through `Lean.ofReduceBool`, as
`native_decide` does, so a theorem proved without it depends on the standard
axioms only; on the corpus every branch `dirty_symex` meets closes by
`bv_omega`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic

namespace SolidCore.Refinement.Evm.Symex

variable {fork : Fork}

/-! ## The postcondition and the rules the tactic adds -/

/-- The frame reverted with empty output. -/
def Reverted (evm : Evm fork Nat) : Prop := evm.error = some .revert ∧ evm.output = .empty

theorem extendMemory_size_zero (n : Nat) (start : U256) :
    extendMemory n [(start, 0)] = ⟨0, 0⟩ := by
  simp [extendMemory]

/-- REVERT of 0 bytes, from any offset, reverts with empty output. -/
theorem revert_empty (hfork : .byzantium ≤ fork) {code : ByteArray} {message : Message fork}
    {pc : Nat} {start : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) :
    Spec fork (At code message pc (start :: 0 :: rest) memory gas state substate returnData)
      Reverted := by
  refine Spec.consequence (revert hfork hlt hbyte ?_) (fun _ h => h) ?_
  · rw [extendMemory_size_zero]; exact Nat.zero_le _
  · rintro e ⟨-, herr, hout, -⟩
    exact ⟨herr, by rw [hout]; simp [memoryReadBytes]⟩

/-- JUMPI on any condition: the specification holds when it holds after the fall-through
for a zero condition and after the jump for a nonzero one. -/
theorem jumpi_split {code : ByteArray} {message : Message fork} {pc : Nat}
    {destination condition : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    {Q : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true)
    (zero : condition = 0 →
      Spec fork (At code message (pc + 1) rest memory (gas - 10) state substate returnData) Q)
    (taken : condition ≠ 0 →
      Spec fork (At code message destination.toNat rest memory (gas - 10) state substate
        returnData) Q) :
    Spec fork (At code message pc (destination :: condition :: rest) memory gas state substate
      returnData) Q := by
  by_cases h : condition = 0
  · exact Spec.seq (jumpi_of_eq_zero hlt hbyte hgas h) (zero h)
  · exact Spec.seq (jumpi_taken hlt hbyte hgas h valid) (taken h)

/-- LT as a bit-vector comparison. -/
theorem lessThan_eq (a b : U256) : lessThan a b = if a < b then 1 else 0 := by
  simp [lessThan, BitVec.lt_def]

/-- GT as a bit-vector comparison. -/
theorem greaterThan_eq (a b : U256) : greaterThan a b = if b < a then 1 else 0 := by
  simp [greaterThan, BitVec.lt_def]

/-- SIGNEXTEND by a byte index below 31 is `BitVec.signExtend` of the low bytes. -/
theorem signextend_eq (b : Nat) (hb : b < 31) (x : U256) :
    signextend (BitVec.ofNat 256 b) x = BitVec.signExtend 256 (x.setWidth (8 * (b + 1))) := by
  have hbn : (BitVec.ofNat 256 b).toNat = b := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hk : 8 * (b + 1) ≤ 248 := by omega
  have hk1 : 8 * (b + 1) - 1 + 1 = 8 * (b + 1) := by omega
  have hpk : 2 ^ (8 * (b + 1)) ≤ 2 ^ 248 := Nat.pow_le_pow_right (by decide) hk
  have hpk1 : 2 ^ (8 * (b + 1)) = 2 * 2 ^ (8 * (b + 1) - 1) := by
    conv_lhs => rw [← hk1]
    rw [Nat.pow_succ]; omega
  have h248 : (2 : Nat) ^ 248 < 2 ^ 256 := by decide
  have hlow : x.toNat % 2 ^ (8 * (b + 1)) < 2 ^ (8 * (b + 1)) := Nat.mod_lt _ (Nat.two_pow_pos _)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, BitVec.toNat_setWidth]
  unfold signextend
  rw [hbn, ite_eq_right (by omega)]
  simp only
  rw [Nat.mod_eq_of_lt (a := x.toNat % 2 ^ (8 * (b + 1))) (by omega)]
  split
  · rename_i h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [show ¬ 2 ^ (8 * (b + 1) - 1) ≤ x.toNat % 2 ^ (8 * (b + 1)) by omega]
  · rename_i h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [show 2 ^ (8 * (b + 1) - 1) ≤ x.toNat % 2 ^ (8 * (b + 1)) by omega]
    omega

/-! ## Branch conditions as comparisons

A dispatcher checks an argument word against its type by an OR of one word per
argument: `GT` against the type's maximum for an unsigned or enum word, and the
XOR of the word with its sign extension for a signed one. The rules below turn
such a condition, compared with zero, into a proposition on the words' values,
which `bv_omega` decides from the dirty fact. -/

theorem or_eq_zero' {w : Nat} (x y : BitVec w) : x ||| y = 0 ↔ x = 0 ∧ y = 0 :=
  BitVec.or_eq_zero_iff

theorem xor_eq_zero' {w : Nat} (x y : BitVec w) : x ^^^ y = 0 ↔ x = y :=
  BitVec.xor_eq_zero_iff

theorem ite_one_zero_eq_zero (p : Prop) [Decidable p] :
    ((if p then 1#256 else 0#256) = 0) ↔ ¬ p := by
  split <;> simp_all

/-- A word is its sign extension from its low `k` bits, a whole number of bytes, exactly when
its value is below `2 ^ (k - 1)` or at least `2 ^ 256 - 2 ^ (k - 1)`. -/
theorem signExtend_setWidth_eq_iff {k : Nat} (hk : 0 < k ∧ k < 256 ∧ k % 8 = 0) (a : U256) :
    BitVec.signExtend 256 (a.setWidth k) = a ↔
      a.toNat < 2 ^ (k - 1) ∨ 2 ^ 256 - 2 ^ (k - 1) ≤ a.toNat := by
  rw [← BitVec.toNat_inj, BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth]
  have ha := a.isLt
  obtain ⟨h0, h1, h2⟩ := hk
  obtain ⟨b, rfl⟩ : ∃ b, k = 8 * (b + 1) := ⟨k / 8 - 1, by omega⟩
  have hb : b < 31 := by omega
  clear h0 h1 h2
  iterate 31
    rcases b with _ | b
    · simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, decide_eq_true_eq] at *
      split <;> omega
  omega

/-- The value of a sign extension from the low `k` bits, as an `if` on the sign bit, which
`omega` reads once the `if` is split. -/
theorem toNat_signExtend_setWidth {k : Nat} (hk : 0 < k ∧ k ≤ 256) (x : U256) :
    (BitVec.signExtend 256 (x.setWidth k)).toNat =
      if 2 ^ (k - 1) ≤ x.toNat % 2 ^ k then x.toNat % 2 ^ k + (2 ^ 256 - 2 ^ k)
      else x.toNat % 2 ^ k := by
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hk2 : 2 ^ k ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hk.2
  have hlt : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.mod_eq_of_lt (by omega : x.toNat % 2 ^ k < 2 ^ 256)]
  by_cases h : 2 ^ (k - 1) ≤ x.toNat % 2 ^ k <;> simp [h]

/-! ## From the frame to `Target.run` -/

/-- Any spec of the frame at pc 0 gives the result of the interpreter loop. -/
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

/-- A message with no value, to code that is no precompile, whose frame reverts with empty
output from every state: `processMessage` at Fusaka returns the revert with empty output. -/
theorem processMessage_reverts {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (hv : message.value = 0)
    (hpre : precompileAddress .fusaka message = none)
    (h : ∀ st ss, Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) Reverted)
    (st : State.TransactionState) (ss : Substate) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = some .revert ∧ evm.1.output = .empty := by
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
    obtain ⟨after', h', -, herr, hout⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> simp [hout]

theorem precompileAddress_message (code : ByteArray) (c : Call) :
    precompileAddress .fusaka (Target.message code c) = none := by
  simp only [precompileAddress, Target.message]
  decide

/-- A call with no value whose frame reverts with empty output from every state: `Target.run`
shows the rejection, `Abi.rejected`. -/
theorem run_of_reverts (code : ByteArray) (c : Call) (hv : c.callvalue = 0)
    (h : ∀ st ss, Spec .fusaka (At code (Target.message code c) 0 [] .empty 10000000 st ss .empty)
      Reverted) :
    Target.run code c = some (Abi.rejected c.storage) := by
  obtain ⟨evm, hr, herr, hout⟩ := processMessage_reverts (Target.message code c) rfl
    (by simp [Target.message, hv])
    (precompileAddress_message code c) h (Target.preState code c) Substate.empty
  simp [Target.run, hr, herr, hout, Abi.rejected]

/-- The generic dirty-argument theorem: if, for every list of argument words that are not
all clean for `ps`, the frame of every message with no value and call data
`cdOf (selectorOf s) ws` reverts with empty output, then every dirty call of the ABI
interface shows the rejection `Abi.rejected`, from any storage. -/
theorem dirty_of_frame (code : ByteArray) (s : Nat) (ps : List Abi.Param)
    (h : ∀ ws : List U256, ws.length = ps.length → ¬ cleanAllBv ps ws →
      ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) Reverted)
    (σ : List (Nat × Nat)) (args : List Nat) (hlen : args.length = ps.length)
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (hd : Abi.Dirty ps args) :
    Target.run code { calldata := Abi.calldata s args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) :=
  run_of_reverts code _ rfl fun st ss =>
    h (args.map (BitVec.ofNat 256)) (by simpa using hlen) (not_cleanAllBv ps args hargs hd)
      _ rfl (calldata_eq_cdOf s args hargs) st ss

/-! ## The tactic -/

open Lean.Parser.Tactic

/-- Rewrites branch conditions, in the goal and the hypotheses, into comparisons of the words'
values: an OR or XOR compared with zero, a comparison's `if` compared with zero, and a sign
extension compared with its word. -/
syntax "symex_bits" : tactic

macro_rules
  | `(tactic| symex_bits) => `(tactic| (simp only [ne_eq, BitVec.or_zero, BitVec.zero_or,
      or_eq_zero', xor_eq_zero', ite_one_zero_eq_zero, signExtend_setWidth_eq_iff, Nat.reduceSub,
      Nat.reducePow, Nat.reduceMod, Nat.reduceLT, _root_.and_self, true_and] at *))

/-- Closes a goal about the words of a run by linear arithmetic on their values, a
kernel-checked proof: `bv_omega`, after `symex_bits` when it needs it, and else the same with
every `x % n` whose `x < n` `omega` shows from the hypotheses (such as a path condition that
bounds an argument word) replaced by `x`, which spares `omega` the large moduli it cannot
eliminate. -/
syntax "symex_omega" : tactic

macro_rules
  | `(tactic| symex_omega) => `(tactic| first
      | bv_omega
      | ((try symex_bits) <;> bv_omega)
      | ((try symex_bits) <;>
          (try simp only [toNat_signExtend_setWidth, Nat.reduceLT, Nat.reduceLeDiff, Nat.reducePow,
            Nat.reduceSub, Nat.reduceMod, Nat.lt_irrefl, _root_.and_self] at *) <;>
          (try simp -implicitDefEqProofs only [bitvec_to_nat] at *) <;>
          (repeat (simp (disch := omega) only [Nat.mod_eq_of_lt] at *)) <;>
          (repeat' split) <;> omega))

/-- Closes a goal about the words of a run, without the hypothesis `hf` about the fork: by
`symex_omega`, a kernel-checked proof, or else by `bv_decide` without its enum preprocessing.
That preprocessing would add an auxiliary declaration for the enum `Fork` to the environment,
which then clashes between two modules that both use the tactic. -/
syntax "symex_bv" ident : tactic

macro_rules
  | `(tactic| symex_bv $hf) => `(tactic| (clear $hf; first
      | symex_omega
      | bv_decide (config := { enums := false })))

/-- Rewrites the words of the frame: call data, call value and the EVM's operations as
bit-vector terms, evaluated when ground. `ns` are the facts about the message. -/
syntax "symex_norm" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| symex_norm [$ns,*]) => `(tactic| (
      (try simp only [$ns,*, loadWord_cdOf_getD, shr_cdOf_selectorOf, size_cdOf, size_selectorOf,
        List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
        Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv,
        Nat.reduceMod, Nat.reducePow, BitVec.reduceToNat, Nat.reduceEqDiff])
      try simp only [sub, add, mul, bitwiseOr,
      bitwiseAnd, bitwiseXor, bitwiseNot, lessThan_eq, greaterThan_eq, equal, isZero,
      signextend_eq, bitwiseShr, ↓reduceIte, ite_true, ite_false, BitVec.ofNat_eq_ofNat,
      Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceToNat,
      BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd,
      BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot, BitVec.reduceLT, BitVec.reduceEq,
      BitVec.reduceNe, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth,
      BitVec.reduceSignExtend]))

/-- Runs one step of a symbolic run: closes an empty REVERT, or steps one opcode, taking or
splitting a JUMPI. `ls` are the rules of the code, `ns` the facts about the message and
`hf` the hypothesis that names the fork. -/
syntax "symex_one" " [" simpLemma,* "]" " [" simpLemma,* "]" ident : tactic

macro_rules
  | `(tactic| symex_one [$ls,*] [$ns,*] $hf) => `(tactic| ((try unfold Spec) <;> first
      | (refine revert_empty (by decide) ?lt ?op
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*])
      | ((refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case room => evm_room) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case zero => first | assumption | decide) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case nz => first | assumption | decide
          case dest => evm_dest [$ls,*]) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case zero => symex_bv $hf) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case nz => symex_bv $hf
          case dest => evm_dest [$ls,*]) <;> evm_tidy)
      | ((refine jumpi_split ?lt ?op ?gas ?dest (fun _ => ?zero) (fun _ => ?taken)
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case dest => evm_dest [$ls,*]
          case zero => try (exfalso; symex_bv $hf)
          case taken => try (exfalso; symex_bv $hf)) <;> evm_tidy)
      | ((refine' Triple.seq (mstore ?lt ?op ?gas) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => simp only [extendMemory, memoryGasCost, wordCount, ceil32, MEMORY_PER_WORD,
            WORD_BYTES, ByteArray.size_empty, size_memoryExtend, BitVec.reduceToNat, BitVec.reduceEq,
            ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reducePow,
            Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff] <;> omega) <;>
          (try simp only [extendMemory, memoryGasCost, wordCount, ceil32, MEMORY_PER_WORD,
            WORD_BYTES, ByteArray.size_empty, size_memoryExtend, BitVec.reduceToNat, BitVec.reduceEq,
            ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reducePow,
            Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff]) <;> evm_tidy)
      | evm_step [$ls,*]) <;> (try symex_norm [$ns,*]))

/-- Proves the frame hypothesis of `dirty_of_frame` for a code: every path of the code on
dirty call data reverts with empty output. `ls` are the rules that turn the code into numbers,
as for `evm_step`, and the definitions of the selectors, which are unfolded in the call data. Handles up to 6 parameters. -/
syntax "dirty_symex" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| dirty_symex [$ls,*]) => `(tactic| (
      intro ws hl hdirty msg hv hd st ss
      have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
      try simp only [$ls,*] at hd
      rcases ws with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _⟩⟩⟩⟩⟩⟩⟩ <;>
        try (simp at hl; done)
      all_goals
        simp only [cleanAllBv, cleanBv, and_true, not_and_or, Nat.reduceLT, Nat.reduceLeDiff,
          Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, and_self, ite_true, ite_false,
          BitVec.ofNat_eq_ofNat, Abi.Param.clean, decide_eq_true_eq] at hdirty
        try rcases hdirty with hdirty | hdirty | hdirty | hdirty | hdirty | hdirty
      all_goals repeat symex_one [$ls,*] [hd, hv] hfork))

end SolidCore.Refinement.Evm.Symex




