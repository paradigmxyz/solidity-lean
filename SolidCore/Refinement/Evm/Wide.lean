import SolidCore.Refinement.Evm.Symex

/-!
# Symbolic execution of a dispatcher to its outputs

`Symex.lean`'s `dirty_symex` proves that a dispatcher rejects dirty call data: every
path it follows ends in an empty REVERT. A function with wide parameters (`uint256`,
`address`, `int256`, `bytes32`) has 2^256 clean argument words per parameter, so its
results must be proved symbolically too, on every path to RETURN or REVERT.

The statement for one path is a frame specification with the postcondition
`Post X st ss`: the frame stops with the error and the output the observable `X`
shows (no error and `X.output` when `X.success`, the revert error otherwise), and with
the state and substate it started from. `X` is SolidCore's observable for the same
call, which the source side evaluates first, so the bytecode is checked against the
source directly, with no specification in between.

* `return_post` and `revert_post` close a path at RETURN or REVERT: the output read
  from memory must be `X.output`, byte for byte.
* `processMessage_post` lifts a frame specification to `processMessage` at Fusaka, as
  `C1.processMessage_of_spec` does for one contract.
* `run_of_post` turns it into `Target.run code call = some X` for a call with no value
  and empty storage, when `X` shows no logs and an empty storage, as a function
  that writes no storage does.
* `wide_tgt [rules]` proves the frame hypothesis of `run_of_post` for one path of the
  source: it steps the code with `symex_one` (whose JUMPI rule decides a branch by
  `bv_decide` or splits it), deciding the branches the source's path conditions fix by
  `bv_omega`, and closes RETURN and REVERT with `return_post` and `revert_post`.

`bv_decide` trusts Lean's compiler through `Lean.ofReduceBool`, as `native_decide` does.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace SolidCore.Refinement.Evm.Wide

variable {fork : Fork}

/-- The error of a frame that shows the observable `X`. -/
def errorOf (X : Observable) : Option EvmError := if X.success then none else some .revert

/-- The frame stopped as `X` shows, from state `st` and substate `ss`, which it kept. -/
def Post (X : Observable) (st : State.TransactionState) (ss : Substate) (evm : Evm fork Nat) :
    Prop :=
  evm.error = errorOf X ∧ evm.output.toList.map (·.toNat) = X.output ∧ evm.state = st ∧
    evm.substate = ss

/-- RETURN of the range of memory that reads as `X.output` shows `X`, when `X` succeeds. -/
theorem return_post {X : Observable} {code : ByteArray} {message : Message fork} {pc : Nat}
    {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = true)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Post X state substate) :=
  Spec.consequence (Logic.«return» hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, hst, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, hst, hss⟩)

/-- REVERT of the range of memory that reads as `X.output` shows `X`, when `X` fails. -/
theorem revert_post {X : Observable} {code : ByteArray} {message : Message fork} {pc : Nat}
    {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hfork : .byzantium ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = false)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Post X state substate) :=
  Spec.consequence (revert hfork hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, hst, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, hst, hss⟩)

/-- A message with no value, to code that is no precompile, whose frame stops as `X` shows
from every state: `processMessage` at Fusaka shows `X`'s error and output, keeps the
substate, and on success the state. -/
theorem processMessage_post {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (hv : message.value = 0)
    (hpre : precompileAddress .fusaka message = none) (X : Observable)
    (h : ∀ st ss, Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) (Post X st ss))
    (st : State.TransactionState) (ss : Substate) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = errorOf X ∧ evm.1.output.toList.map (·.toNat) = X.output ∧
      evm.1.substate = ss ∧ (X.success = true → evm.1.state = st) := by
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
    obtain ⟨after', h', -, herr, hout, hst, hsub⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> exact hout
    · simp only [rollbackOnError]; split <;> simp [hsub, hv]
    · intro hX
      have hE : errorOf X = none := by simp [errorOf, hX]
      simp only [rollbackOnError, herr, hE, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact hst

open EthLib.Execution.State in
theorem getStorage_preState_nil (code : ByteArray) (c : Call) (hst : c.storage = []) (k : Nat) :
    (Target.preState code c).getStorage (Target.address selfAddress) (Target.storageKey k) = 0 := by
  simp [Target.preState, hst, State.TransactionState.getStorage, State.TransactionState.ofBlock,
    StorageMap.slot, State.getStorage]

/-- The call with selector `s`, argument words `ws`, no value and empty storage. -/
def callOf (s : Nat) (ws : List U256) : Call :=
  { calldata := Abi.calldata s (ws.map BitVec.toNat), callvalue := 0, storage := [] }

/-- The frame of every message with no value and call data `cdOf (selectorOf s) ws` stops as
`X` shows: `Target.run` of the call with argument words `ws`, no value and empty storage is
`X`, when `X` shows no logs and an empty storage. -/
theorem run_of_post (code : ByteArray) (s : Nat) (ws : List U256) (X : Observable)
    (hlogs : X.logs = []) (hstore : ∀ slot, X.storage slot = 0)
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) (Post X st ss)) :
    Target.run code (callOf s ws) = some X := by
  have hd : Abi.calldata s (ws.map BitVec.toNat) = cdOf (selectorOf s) ws := by
    rw [calldata_eq_cdOf s _ (by simpa using fun a _ => a.isLt)]
    simp [List.map_map, Function.comp_def]
  let c := callOf s ws
  obtain ⟨evm, hr, herr, hout, hsub, hst⟩ := processMessage_post (Target.message code c) rfl rfl
    (precompileAddress_message code c) X
    (fun st ss => h _ rfl (by simp [Target.message, c, callOf, hd]) st ss) (Target.preState code c)
    Substate.empty
  show Target.run code c = some X
  simp only [Target.run, hr]
  have hsucc : evm.1.error.isNone = X.success := by
    rw [herr]; cases hX : X.success <;> simp [errorOf, hX]
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout hlogs hstore hst ⊢
    subst hlogs
    rw [Observable.mk.injEq]
    refine ⟨hsucc, hout, by simp [hsub, Substate.empty], ?_⟩
    funext slot
    rw [hstore slot, hsucc]
    cases hs : success
    · simp [slotValue, c, callOf]
    · simp only [ite_true]
      rw [hst hs, getStorage_preState_nil code c (by simp [c, callOf])]
      rfl

/-- A read of the 32 bytes of a word is the word. -/
theorem memoryReadBytes_wordBytes (v : U256) : memoryReadBytes (wordBytes v) 0 32 = wordBytes v := by
  have := memoryReadBytes_whole (memory := wordBytes v)
  rwa [size_wordBytes] at this

/-- The bytes of a word, as a list, are its 32 big-endian bytes. -/
theorem toList_wordBytes (v : U256) :
    (wordBytes v).toList.map (·.toNat) = (natToBytes 32 v.toNat).map (·.toNat) := by
  have : (wordBytes v).data.toList = natToBytes 32 v.toNat := EthLib.Base.U256.toList_toBeBytes v
  simp [this]

/-- A word written just past the end of a memory, into the 32 bytes it grew by, appends it. -/
theorem memoryWrite_extend_word {m : ByteArray} {n : Nat} (v : U256) (h : m.size = n) :
    memoryWrite (memoryExtend m 32) n (wordBytes v) = m ++ wordBytes v := by
  subst h
  have := memoryWrite_extend_end (memory := m) (value := wordBytes v)
  rwa [size_wordBytes] at this

/-- A read of a whole memory, of a size given by a hypothesis, is the memory. -/
theorem memoryReadBytes_whole_of {m : ByteArray} {n : Nat} (h : m.size = n) :
    memoryReadBytes m 0 n = m := by
  subst h; exact memoryReadBytes_whole

/-- The bytes of two byte arrays one after the other. -/
theorem toList_append_map (a b : ByteArray) (f : UInt8 → Nat) :
    (a ++ b).toList.map f = a.toList.map f ++ b.toList.map f := by
  simp

/-! ## The tactic -/

open Lean.Parser.Tactic

/-- The rules that evaluate memory and its growth on the way to RETURN or REVERT: the price of
growth, the size of memory after a write that fits, and a write of a whole word-sized memory. -/
syntax "wide_mem" : tactic

macro_rules
  | `(tactic| wide_mem) => `(tactic| (simp only [extendMemory, memoryGasCost, wordCount, ceil32,
      MEMORY_PER_WORD, WORD_BYTES, ByteArray.size_empty, size_memoryExtend, size_wordBytes,
      size_memoryWrite, memoryWrite_whole, memoryReadBytes_wordBytes, BitVec.reduceToNat,
      BitVec.reduceEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub,
      Nat.reducePow, Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff,
      memoryExtend_zero, Nat.zero_add, Nat.add_zero, ByteArray.size_append, memoryWrite_extend_word,
      memoryReadBytes_whole_of]))

/-- Proves that the output a RETURN or REVERT reads from memory is the observable's. -/
syntax "wide_out" : tactic

macro_rules
  | `(tactic| wide_out) => `(tactic| ((try wide_mem) <;> first
      | rfl
      | (simp only [Source.observe]; decide +kernel)
      | (simp only [toList_wordBytes, Source.observe, BitVec.toNat_add, BitVec.toNat_xor,
          BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow,
          Nat.reduceMod]; done)
      | (simp [*, toList_wordBytes, Source.observe, BitVec.toNat_add, BitVec.toNat_sub,
          BitVec.toNat_mul, BitVec.toNat_xor, BitVec.lt_def]; done)
      | (simp only [toList_wordBytes, Source.observe]
         congr 2
         (repeat' split) <;> simp_all [BitVec.toNat_add, BitVec.toNat_sub, BitVec.lt_def] <;>
           bv_omega)
      | (simp only [toList_wordBytes, Source.observe]
         congr 2
         (repeat' split) <;> symex_omega)
      | (simp only [toList_append_map, toList_wordBytes, Source.observe, List.append_assoc]
         repeat' (first
           | refine congrArg₂ (· ++ ·) ?_ ?_
           | refine congrArg (List.map _) ?_
           | refine congrArg (natToBytes 32) ?_)
         all_goals first | rfl | ((repeat' split) <;> symex_omega))))

/-- Decides the condition of a JUMPI from the path conditions in context, which are facts about
the values of the argument words: it splits the `if`s of the condition and closes each case by
evaluation or by `bv_omega`. -/
syntax "wide_dec" : tactic

macro_rules
  | `(tactic| wide_dec) => `(tactic| first
      | decide
      | assumption
      | ((try simp only [BitVec.zero_or, BitVec.or_zero, BitVec.zero_and, BitVec.and_zero]) <;>
          (repeat' split) <;> first | rfl | decide | (exfalso; bv_omega) | bv_omega))

/-- Steps one opcode of a path to its outputs: RETURN and REVERT close the path against the
observable of the postcondition, every other opcode goes to `symex_one`. -/
syntax "wide_one" " [" simpLemma,* "]" " [" simpLemma,* "]" ident : tactic

macro_rules
  | `(tactic| wide_one [$ls,*] [$ns,*] $hf) => `(tactic| ((try unfold Spec) <;> first
      | (refine return_post ?lt ?op ?gas ?succ ?out
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out)
      | (refine revert_post (by decide) ?lt ?op ?gas ?succ ?out
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out)
      | ((refine' Triple.seq (mstore ?lt ?op ?gas) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => wide_mem <;> omega) <;> (try wide_mem) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case zero => wide_dec) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case nz => wide_dec
          case dest => evm_dest [$ls,*]) <;> evm_tidy)
      | symex_one [$ls,*] [$ns,*] $hf))

/-- Proves the frame hypothesis of `run_of_post` on one path of the source: every path of the
code that the hypotheses in context allow stops as the observable says. `ls` are the rules of
the code, as for `dirty_symex`. -/
syntax "wide_tgt" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| wide_tgt [$ls,*]) => `(tactic| (
      intro msg hv hd st ss
      have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
      try simp only [$ls,*] at hd
      repeat wide_one [$ls,*] [hd, hv] hfork))

end SolidCore.Refinement.Evm.Wide
