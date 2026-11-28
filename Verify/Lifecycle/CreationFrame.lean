import Verify.Lifecycle.DeployFrame
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# The creation frame of solar's constructors, once for every contract

solar compiles a constructor to one straight run of the creation frame on its success path:

    CODESIZE PUSH SUB DUP CODECOPY ...            ; copy the argument words after the code
    ... GT CALLVALUE OR PUSH JUMPI                ; too few argument bytes or a value: revert
    MLOAD ... SHR PUSH JUMPI                      ; decode each word, revert on dirty bits
    ... SSTORE ...                                ; the body's writes
    ... MSTORE                                    ; patch each immutable into the runtime copy
    PUSH DUP PUSH PUSH0 CODECOPY ... PUSH0 RETURN ; return the runtime code

This module proves that whole shape once. `run` is an evaluator of the creation frame over the
opcodes such a constructor runs: PUSH0 to PUSH32, DUP, SWAP, POP, every one- and two-operand
opcode of the stack, CALLVALUE, CODESIZE, CODECOPY, MLOAD, MSTORE, SSTORE, JUMP, JUMPI, JUMPDEST
and RETURN. It reads EthLib's own decoder, prices, memory growth, copies and words, so each of
its steps is one rule of EthLib's program logic, and `run_good` proves it sound against
EthLib once, by induction on the steps. The price of SSTORE depends on the access lists of the
message, so the evaluator charges its most expensive case (`sstore_then`).

`observes` then gives EthLib's run of the creation: whenever the evaluator returns, within the gas
of the creation, EthLib's run of that code succeeds, returns the bytes the evaluator returned and
leaves the storage of the writes it recorded. `deploys_of_check` turns a Boolean `check` into
`Deploys`, and `not_deploys_of_slot` and `not_deploys_of_output` refute a deployment that
names another storage or other runtime bytes. A contract's deployment is then one kernel
evaluation of `check` on its creation code, with no per-contract stepping.

Outside the evaluator: opcodes not listed above (SLOAD, KECCAK256, calls, logs, CREATE, and the
rest), so a constructor that reads storage, hashes, calls or emits is not covered; it runs on
concrete argument words, one creation at a time.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex
open SolidCore.Refinement.Evm.Wide

namespace Verify.Lifecycle.Creation

/-- A frame of the evaluator: the program counter, the stack, the memory and the storage writes,
newest first. -/
structure Cfg where
  pc : Nat
  stack : List U256
  mem : ByteArray
  ws : List (U256 × U256)

/-- One step of the evaluator: the next frame and the price of the step, or the bytes RETURN
gives and the price of that halt. -/
inductive R where
  | next (c : Cfg) (cost : Nat)
  | ret (out : ByteArray) (cost : Nat)

/-- The word at a key after the writes `ws`, newest first, from the empty storage. -/
def look : List (U256 × U256) → U256 → U256
  | [], _ => 0
  | (a, v) :: r, k => if a = k then v else look r k

/-- The two-operand opcodes of the stack, with their price and word function (`stackOnlyStep`). -/
def binOf : Op → Option (Nat × (U256 → U256 → U256))
  | .add => some (OPCODE_ADD, add)
  | .mul => some (OPCODE_MUL, mul)
  | .sub => some (OPCODE_SUB, sub)
  | .div => some (OPCODE_DIV, div)
  | .sdiv => some (OPCODE_SDIV, sdiv)
  | .mod => some (OPCODE_MOD, mod)
  | .smod => some (OPCODE_SMOD, smod)
  | .signextend => some (OPCODE_SIGNEXTEND, signextend)
  | .lt => some (OPCODE_LT, lessThan)
  | .gt => some (OPCODE_GT, greaterThan)
  | .slt => some (OPCODE_SLT, signedLessThan)
  | .sgt => some (OPCODE_SGT, signedGreaterThan)
  | .eq => some (OPCODE_EQ, equal)
  | .and => some (OPCODE_AND, bitwiseAnd)
  | .or => some (OPCODE_OR, bitwiseOr)
  | .xor => some (OPCODE_XOR, bitwiseXor)
  | .byte => some (OPCODE_BYTE, getByte)
  | .shl => some (OPCODE_SHL, bitwiseShl)
  | .shr => some (OPCODE_SHR, bitwiseShr)
  | .sar => some (OPCODE_SAR, bitwiseSar)
  | _ => none

/-- The one-operand opcodes of the stack, with their price and word function. -/
def unOf : Op → Option (Nat × (U256 → U256))
  | .iszero => some (OPCODE_ISZERO, isZero)
  | .not => some (OPCODE_NOT, bitwiseNot)
  | _ => none

theorem binOf_sound {fork : Fork} {op : Op} {k : Nat} {f : U256 → U256 → U256}
    (h : binOf op = some (k, f)) : instruction (Meter := Nat) fork op = some (binaryOp k f) := by
  apply instruction_of_stackOnlyStep
  cases op <;> simp only [binOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; rfl)

theorem unOf_sound {fork : Fork} {op : Op} {k : Nat} {f : U256 → U256}
    (h : unOf op = some (k, f)) : instruction (Meter := Nat) fork op = some (unaryOp k f) := by
  apply instruction_of_stackOnlyStep
  cases op <;> simp only [unOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; rfl)

theorem decode_of_ofByte {fork : Fork} {b : UInt8} {op : Op} (h : Op.ofByte fork b = some op) :
    Op.decode b = some op := by
  simp only [Op.ofByte, Option.filter_eq_some_iff] at h
  exact h.1

/-! ## The evaluator -/

/-- The opcodes the evaluator reads through EthLib's decoder: the stack operations, PUSH1 to
PUSH32, DUP and SWAP. -/
def family (code : ByteArray) (c : Cfg) (op : Op) : Option R :=
  match binOf op with
  | some (k, f) =>
    match c.stack with
    | x :: y :: r => some (.next { c with pc := c.pc + 1, stack := f x y :: r } k)
    | _ => none
  | none =>
    match unOf op with
    | some (k, f) =>
      match c.stack with
      | x :: r => some (.next { c with pc := c.pc + 1, stack := f x :: r } k)
      | _ => none
    | none =>
      match op with
      | .push n =>
        if n.val ≠ 0 ∧ c.stack.length < STACK_LIMIT then
          some (.next { c with pc := c.pc + (1 + n.val), stack := pushData code c.pc n :: c.stack } 3)
        else none
      | .dup n =>
        match c.stack[n.val]? with
        | some x =>
          if c.stack.length < STACK_LIMIT then
            some (.next { c with pc := c.pc + 1, stack := x :: c.stack } 3)
          else none
        | none => none
      | .swap n =>
        match c.stack with
        | top :: r =>
          match r[n.val]? with
          | some x => some (.next { c with pc := c.pc + 1, stack := x :: r.set n.val top } 3)
          | none => none
        | [] => none
      | _ => none

def sPush0 (c : Cfg) : Option R :=
  if c.stack.length < STACK_LIMIT then some (.next { c with pc := c.pc + 1, stack := 0 :: c.stack } 2)
  else none

def sCodesize (code : ByteArray) (c : Cfg) : Option R :=
  if c.stack.length < STACK_LIMIT then
    some (.next { c with pc := c.pc + 1, stack := BitVec.ofNat 256 code.size :: c.stack } 2)
  else none

def sPop (c : Cfg) : Option R :=
  match c.stack with
  | _ :: r => some (.next { c with pc := c.pc + 1, stack := r } 2)
  | [] => none

def sJump (code : ByteArray) (c : Cfg) : Option R :=
  match c.stack with
  | d :: r =>
    if isValidJumpDest (validJumpDestinations code) d.toNat = true then
      some (.next { c with pc := d.toNat, stack := r } 8)
    else none
  | [] => none

def sJumpi (code : ByteArray) (c : Cfg) : Option R :=
  match c.stack with
  | d :: x :: r =>
    if x = 0 then some (.next { c with pc := c.pc + 1, stack := r } 10)
    else if isValidJumpDest (validJumpDestinations code) d.toNat = true then
      some (.next { c with pc := d.toNat, stack := r } 10)
    else none
  | _ => none

def sMload (c : Cfg) : Option R :=
  match c.stack with
  | start :: r =>
    some (.next { c with
      pc := c.pc + 1
      stack := loadWord (memoryReadBytes
          (memoryExtend c.mem (extendMemory c.mem.size [(start, 32)]).expandBy) start.toNat 32) 0 32 :: r
      mem := memoryExtend c.mem (extendMemory c.mem.size [(start, 32)]).expandBy }
      (3 + (extendMemory c.mem.size [(start, 32)]).cost))
  | [] => none

def sMstore (c : Cfg) : Option R :=
  match c.stack with
  | start :: v :: r =>
    some (.next { c with
      pc := c.pc + 1
      stack := r
      mem := memoryWrite (memoryExtend c.mem (extendMemory c.mem.size [(start, 32)]).expandBy)
        start.toNat (wordBytes v) }
      (3 + (extendMemory c.mem.size [(start, 32)]).cost))
  | _ => none

def sCodecopy (code : ByteArray) (c : Cfg) : Option R :=
  match c.stack with
  | start :: off :: size :: r =>
    some (.next { c with
      pc := c.pc + 1
      stack := r
      mem := memoryWrite (memoryExtend c.mem (extendMemory c.mem.size [(start, size)]).expandBy)
        start.toNat ⟨(bufferRead code off.toNat size.toNat).toArray⟩ }
      (3 + 3 * wordCount size.toNat + (extendMemory c.mem.size [(start, size)]).cost))
  | _ => none

def sSstore (c : Cfg) : Option R :=
  match c.stack with
  | key :: new :: r => some (.next { c with pc := c.pc + 1, stack := r, ws := (key, new) :: c.ws } 22100)
  | _ => none

def sReturn (c : Cfg) : Option R :=
  match c.stack with
  | start :: size :: _ =>
    some (.ret (memoryReadBytes (memoryExtend c.mem (extendMemory c.mem.size [(start, size)]).expandBy)
      start.toNat size.toNat) (extendMemory c.mem.size [(start, size)]).cost)
  | _ => none

/-- One step of the evaluator on the byte `b` at the program counter. CALLVALUE pushes 0: a creation
of the lifecycle statement sends no value. -/
def stepB (code : ByteArray) (c : Cfg) (b : UInt8) : Option R :=
  if b = 0x5f then sPush0 c
  else if b = 0x34 then sPush0 c
  else if b = 0x38 then sCodesize code c
  else if b = 0x50 then sPop c
  else if b = 0x5b then some (.next { c with pc := c.pc + 1 } 1)
  else if b = 0x56 then sJump code c
  else if b = 0x57 then sJumpi code c
  else if b = 0x51 then sMload c
  else if b = 0x52 then sMstore c
  else if b = 0x39 then sCodecopy code c
  else if b = 0x55 then sSstore c
  else if b = 0xf3 then sReturn c
  else
    match Op.ofByte .fusaka b with
    | some op => family code c op
    | none => none

/-- The evaluator: at most `fuel` steps from `c`, to the bytes RETURN gives, the storage writes and
the price of the whole run. -/
def run (code : ByteArray) : Nat → Cfg → Option (ByteArray × List (U256 × U256) × Nat)
  | 0, _ => none
  | fuel + 1, c =>
    if h : c.pc < code.size then
      match stepB code c code[c.pc] with
      | some (.next c' k) =>
        match run code fuel c' with
        | some (o, ws, n) => some (o, ws, k + n)
        | none => none
      | some (.ret o k) => some (o, c.ws, k)
      | none => none
    else none

/-! ## Soundness against EthLib -/

/-- What a frame of the creation keeps along the run: the account exists, its storage is that of
the writes `ws`, and there are no logs. -/
structure Inv (st : TransactionState) (ss : Substate) (ws : List (U256 × U256)) : Prop where
  acct : st.getAccountOptional (Target.address selfAddress) ≠ none
  store : ∀ k : U256, st.getStorage (Target.address selfAddress) (U256.toBeBytes k) = look ws k
  logs : ss.logs = Substate.empty.logs

/-- The frame stopped with no error, the output `out`, no logs and the storage of `ws`. -/
def Ends (out : ByteArray) (ws : List (U256 × U256)) (evm : Evm .fusaka Nat) : Prop :=
  evm.error = none ∧ evm.output = out ∧ evm.substate.logs = Substate.empty.logs ∧
    ∀ k : U256, evm.state.getStorage (Target.address selfAddress) (U256.toBeBytes k) = look ws k

/-- From the frame `c` with at least `need` gas, the creation frame stops as `Ends out ws` says. -/
def Good (code : ByteArray) (msg : Message .fusaka) (c : Cfg) (out : ByteArray)
    (ws : List (U256 × U256)) (need : Nat) : Prop :=
  ∀ (gas : Nat) (st : TransactionState) (ss : Substate), need ≤ gas → Inv st ss c.ws →
    Spec .fusaka (At code msg c.pc c.stack c.mem gas st ss .empty) (Ends out ws)

variable {code : ByteArray} {msg : Message .fusaka} {out : ByteArray} {ws : List (U256 × U256)}
  {need : Nat}

/-- A step that keeps the storage writes and costs `k`. -/
theorem good_seq {c c' : Cfg} {k : Nat} (ih : Good code msg c' out ws need) (hws : c'.ws = c.ws)
    (rule : ∀ (gas : Nat) (st : TransactionState) (ss : Substate), k ≤ gas →
      Hoare .fusaka (At code msg c.pc c.stack c.mem gas st ss .empty)
        (At code msg c'.pc c'.stack c'.mem (gas - k) st ss .empty)) : Good code msg c out ws (k + need) :=
  fun gas st ss hg hi => Spec.seq (rule gas st ss (by omega)) (ih _ _ _ (by omega) (hws ▸ hi))

theorem family_good {c c' : Cfg} {k : Nat} {op : Op} (hlt : c.pc < code.size)
    (hop : Op.ofByte .fusaka code[c.pc] = some op)
    (h : family code c op = some (.next c' k)) (ih : Good code msg c' out ws need) :
    Good code msg c out ws (k + need) := by
  obtain ⟨pc, stack, mem, cws⟩ := c
  simp only at hlt hop
  unfold family at h
  repeat' split at h
  all_goals try (simp at h; done)
  all_goals simp only [Option.some.injEq, R.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h; subst_vars
  · exact good_seq ih rfl (fun _ _ _ hg => binary hlt rfl hop (binOf_sound ‹_›) hg)
  · exact good_seq ih rfl (fun _ _ _ hg => unary hlt rfl hop (unOf_sound ‹_›) hg)
  · rename_i hc
    exact good_seq ih rfl (fun _ _ _ hg =>
      push_of_decode hlt rfl (decode_of_ofByte hop) hc.1 rfl hg hc.2)
  · exact good_seq ih rfl (fun _ _ _ hg =>
      dup_of_decode hlt rfl (decode_of_ofByte hop) ‹_› hg ‹_›)
  · exact good_seq ih rfl (fun _ _ _ hg => swap_of_decode hlt rfl (decode_of_ofByte hop) ‹_› hg)

/-- SSTORE keeps the invariant with the new write in front. -/
theorem inv_sstore {st : TransactionState} {ss : Substate} {cws : List (U256 × U256)}
    (htgt : msg.currentTarget = Target.address selfAddress) (hi : Inv st ss cws) (key new : U256) :
    Inv (writeOf (st.recordStorageRead msg.currentTarget (U256.toBeBytes key)) msg.currentTarget
        (U256.toBeBytes key) new)
      { ss with
        accessedStorageKeys := ss.accessedStorageKeys.insert msg.currentTarget
          ((ss.accessedStorageKeys.getD msg.currentTarget ∅).insert (U256.toBeBytes key))
        refundCounter := ss.refundCounter + sstoreRefund .fusaka
          (st.getStorageOriginal msg.currentTarget (U256.toBeBytes key))
          (st.getStorage msg.currentTarget (U256.toBeBytes key)) new }
      ((key, new) :: cws) where
  acct := hi.acct
  store k := by
    rw [getStorage_writeOf_of, getStorage_recordStorageRead, htgt]
    simp only [look, true_and]
    by_cases hk : key = k
    · subst hk; simp
    · have hne : U256.toBeBytes k ≠ U256.toBeBytes key := fun e => hk (U256.toBeBytes_inj e).symm
      simp only [hne, hk, ↓reduceIte]
      exact hi.store k
  logs := hi.logs

theorem stepB_good (hv : msg.value = 0) (hstat : msg.isStatic = false)
    (htgt : msg.currentTarget = Target.address selfAddress) {c c' : Cfg} {k : Nat}
    (hlt : c.pc < code.size) (h : stepB code c code[c.pc] = some (.next c' k))
    (ih : Good code msg c' out ws need) : Good code msg c out ws (k + need) := by
  obtain ⟨pc, stack, mem, cws⟩ := c
  simp only at hlt h
  unfold stepB at h
  by_cases hb1 : code[pc] = 0x5f
  · rw [ite_cond_eq_true _ _ (eq_true hb1)] at h
    have hb := hb1
    unfold sPush0 at h
    split at h
    · rename_i hlen
      simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => push0 (by decide) hlt hb hg hlen)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb1)] at h
  by_cases hb2 : code[pc] = 0x34
  · rw [ite_cond_eq_true _ _ (eq_true hb2)] at h
    have hb := hb2
    unfold sPush0 at h
    split at h
    · rename_i hlen
      simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => hv ▸ callvalue hlt hb hg hlen)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb2)] at h
  by_cases hb3 : code[pc] = 0x38
  · rw [ite_cond_eq_true _ _ (eq_true hb3)] at h
    have hb := hb3
    unfold sCodesize at h
    split at h
    · rename_i hlen
      simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => codesize hlt hb hg hlen)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb3)] at h
  by_cases hb4 : code[pc] = 0x50
  · rw [ite_cond_eq_true _ _ (eq_true hb4)] at h
    have hb := hb4
    unfold sPop at h
    split at h
    · simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => pop hlt hb hg)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb4)] at h
  by_cases hb5 : code[pc] = 0x5b
  · rw [ite_cond_eq_true _ _ (eq_true hb5)] at h
    have hb := hb5
    simp only [Option.some.injEq, R.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst_vars
    exact good_seq ih rfl (fun _ _ _ hg => jumpdest hlt hb hg)
  rw [ite_cond_eq_false _ _ (eq_false hb5)] at h
  by_cases hb6 : code[pc] = 0x56
  · rw [ite_cond_eq_true _ _ (eq_true hb6)] at h
    have hb := hb6
    unfold sJump at h
    split at h
    · split at h
      · rename_i hvalid
        simp only [Option.some.injEq, R.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst_vars
        exact good_seq ih rfl (fun _ _ _ hg => jump hlt hb hg hvalid)
      · simp at h
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb6)] at h
  by_cases hb7 : code[pc] = 0x57
  · rw [ite_cond_eq_true _ _ (eq_true hb7)] at h
    have hb := hb7
    unfold sJumpi at h
    split at h
    · split at h
      · rename_i hz
        simp only [Option.some.injEq, R.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst_vars
        exact good_seq ih rfl (fun _ _ _ hg => jumpi_of_eq_zero hlt hb hg rfl)
      · split at h
        · rename_i hz hvalid
          simp only [Option.some.injEq, R.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst_vars
          exact good_seq ih rfl (fun _ _ _ hg => jumpi_taken hlt hb hg hz hvalid)
        · simp at h
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb7)] at h
  by_cases hb8 : code[pc] = 0x51
  · rw [ite_cond_eq_true _ _ (eq_true hb8)] at h
    have hb := hb8
    unfold sMload at h
    split at h
    · simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => mload hlt hb hg)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb8)] at h
  by_cases hb9 : code[pc] = 0x52
  · rw [ite_cond_eq_true _ _ (eq_true hb9)] at h
    have hb := hb9
    unfold sMstore at h
    split at h
    · simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => mstore hlt hb hg)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb9)] at h
  by_cases hb10 : code[pc] = 0x39
  · rw [ite_cond_eq_true _ _ (eq_true hb10)] at h
    have hb := hb10
    unfold sCodecopy at h
    split at h
    · simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact good_seq ih rfl (fun _ _ _ hg => codecopy hlt hb hg)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb10)] at h
  by_cases hb11 : code[pc] = 0x55
  · rw [ite_cond_eq_true _ _ (eq_true hb11)] at h
    have hb := hb11
    unfold sSstore at h
    split at h
    · rename_i key new r _
      simp only [Option.some.injEq, R.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      intro gas st ss hg hi
      refine sstore_then hlt hb hstat (by omega)
        (setStorage_ok _ _ (by rw [htgt]; exact hi.acct)) ?_
      intro g hgle
      exact ih _ _ _ (by omega) (inv_sstore htgt hi key new)
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb11)] at h
  by_cases hb12 : code[pc] = 0xf3
  · rw [ite_cond_eq_true _ _ (eq_true hb12)] at h
    have hb := hb12
    unfold sReturn at h
    split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb12)] at h
  split at h
  · rename_i op hop
    exact family_good hlt hop h ih
  · simp at h

theorem family_ne_ret {c : Cfg} {o : ByteArray} {k : Nat} (op : Op) :
    family code c op ≠ some (.ret o k) := by
  intro hf
  unfold family at hf
  repeat' split at hf
  all_goals simp at hf

theorem stepB_ret {c : Cfg} {o : ByteArray} {k : Nat} (hlt : c.pc < code.size)
    (h : stepB code c code[c.pc] = some (.ret o k)) : Good code msg c o c.ws k := by
  obtain ⟨pc, stack, mem, cws⟩ := c
  simp only at hlt h
  unfold stepB at h
  by_cases hb1 : code[pc] = 0x5f
  · rw [ite_cond_eq_true _ _ (eq_true hb1)] at h; unfold sPush0 at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb1)] at h
  by_cases hb2 : code[pc] = 0x34
  · rw [ite_cond_eq_true _ _ (eq_true hb2)] at h; unfold sPush0 at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb2)] at h
  by_cases hb3 : code[pc] = 0x38
  · rw [ite_cond_eq_true _ _ (eq_true hb3)] at h; unfold sCodesize at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb3)] at h
  by_cases hb4 : code[pc] = 0x50
  · rw [ite_cond_eq_true _ _ (eq_true hb4)] at h; unfold sPop at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb4)] at h
  by_cases hb5 : code[pc] = 0x5b
  · rw [ite_cond_eq_true _ _ (eq_true hb5)] at h; simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb5)] at h
  by_cases hb6 : code[pc] = 0x56
  · rw [ite_cond_eq_true _ _ (eq_true hb6)] at h; unfold sJump at h; split at h <;> (try split at h) <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb6)] at h
  by_cases hb7 : code[pc] = 0x57
  · rw [ite_cond_eq_true _ _ (eq_true hb7)] at h
    unfold sJumpi at h
    split at h
    · split at h
      · simp at h
      · split at h <;> simp at h
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb7)] at h
  by_cases hb8 : code[pc] = 0x51
  · rw [ite_cond_eq_true _ _ (eq_true hb8)] at h; unfold sMload at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb8)] at h
  by_cases hb9 : code[pc] = 0x52
  · rw [ite_cond_eq_true _ _ (eq_true hb9)] at h; unfold sMstore at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb9)] at h
  by_cases hb10 : code[pc] = 0x39
  · rw [ite_cond_eq_true _ _ (eq_true hb10)] at h; unfold sCodecopy at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb10)] at h
  by_cases hb11 : code[pc] = 0x55
  · rw [ite_cond_eq_true _ _ (eq_true hb11)] at h; unfold sSstore at h; split at h <;> simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb11)] at h
  by_cases hb12 : code[pc] = 0xf3
  · rw [ite_cond_eq_true _ _ (eq_true hb12)] at h
    have hb := hb12
    unfold sReturn at h
    split at h
    · rename_i start size r
      simp only [Option.some.injEq, R.ret.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      intro gas st ss hg hi
      refine Spec.consequence (Logic.«return» hlt hb hg) (fun _ h => h) ?_
      rintro evm ⟨_, herr, hout, _, hst, hss⟩
      exact ⟨by simpa using herr, hout, by rw [hss]; exact hi.logs,
        fun k => by rw [hst]; exact hi.store k⟩
    · simp at h
  rw [ite_cond_eq_false _ _ (eq_false hb12)] at h
  split at h
  · rename_i op _
    exact absurd h (family_ne_ret op)
  · simp at h

theorem run_good (hv : msg.value = 0) (hstat : msg.isStatic = false)
    (htgt : msg.currentTarget = Target.address selfAddress) :
    ∀ fuel c o ws n, run code fuel c = some (o, ws, n) → Good code msg c o ws n := by
  intro fuel
  induction fuel with
  | zero => intro c o ws n h; simp [run] at h
  | succ fuel ih =>
    intro c o ws n h
    unfold run at h
    split at h
    · rename_i hlt
      split at h
      · rename_i c' k hs
        split at h
        · rename_i o' ws' n' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact stepB_good hv hstat htgt hlt hs (ih c' o' ws' n' hr)
        · simp at h
      · rename_i o' k hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact stepB_ret hlt hs
      · simp at h
    · simp at h

/-! ## EthLib's run of the creation -/

/-- What a creation that returns `o` after the writes `ws` shows. -/
def obsOf (o : ByteArray) (ws : List (U256 × U256)) : Observable :=
  { success := true, output := o.toList.map (·.toNat), logs := [],
    storage := fun k => (look ws (BitVec.ofNat 256 k)).toNat }

/-- The start of the creation frame. -/
def initCfg : Cfg := ⟨0, [], .empty, []⟩

/-- **The creation frame, for every code the evaluator runs.** When the evaluator runs the
creation code `init` to RETURN within the gas of the creation, EthLib's run of `init` succeeds,
returns the bytes the evaluator returned and leaves the storage of its writes. -/
theorem observes {init o : ByteArray} {ws : List (U256 × U256)} {n : Nat} (fuel : Nat)
    (h : run init fuel initCfg = some (o, ws, n)) (hn : n ≤ 10000000) :
    ∃ obs, ethLib.run init deployCall = some obs ∧ obs.success = true ∧
      obs.output = o.toList.map (·.toNat) ∧
      ∀ k, obs.storage k = (look ws (BitVec.ofNat 256 k)).toNat := by
  let X := obsOf o ws
  have hspec : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = .empty →
      msg.isStatic = false → msg.currentTarget = Target.address selfAddress →
      Spec .fusaka (At init msg 0 [] .empty 10000000 (Target.preState init deployCall)
        Substate.empty .empty) (PostS X Substate.empty) := by
    intro msg hv _ hstat htgt
    have hi : Inv (Target.preState init deployCall) Substate.empty [] :=
      ⟨account_preState _ _, fun k => by
        rw [getStorage_preState_toBeBytes]; simp [SolarTV.slotValue, look, deployCall], rfl⟩
    refine Spec.consequence (run_good hv hstat htgt fuel initCfg o ws n h 10000000 _ _ hn hi)
      (fun _ h => h) ?_
    rintro evm ⟨herr, hout, hlogs, hst⟩
    refine ⟨by rw [herr]; rfl, by rw [hout]; rfl, hlogs, fun _ slot => ?_⟩
    rw [(storageKey_eq_toBeBytes slot (BitVec.ofNat 256 slot)).mpr (by simp), hst]
    rfl
  obtain ⟨evm, hr, herr, hout, hst⟩ := processMessage_postS (Target.message init deployCall)
    rfl rfl (precompileAddress_message init deployCall) X
    (Target.preState init deployCall) Substate.empty (hspec _ rfl rfl rfl rfl)
  have hsucc : evm.1.error.isNone = true := by rw [herr]; rfl
  refine ⟨_, by show Target.run init deployCall = _; simp only [Target.run, hr]; rfl, ?_, ?_, ?_⟩
  · exact hsucc
  · exact hout
  · intro k
    simp only [hsucc, ↓reduceIte]
    exact (hst rfl).2 k

/-! ## Deployment from a Boolean check -/

/-- The words of the writes `ws` and of `s` agree at every key either names. -/
def keysOk (ws : List (U256 × U256)) (s : List (Nat × Nat)) : Bool :=
  (ws.map Prod.fst ++ s.map fun p => BitVec.ofNat 256 p.1).all fun k =>
    (look ws k).toNat == SolarTV.slotValue s k.toNat

theorem look_eq_zero {ws : List (U256 × U256)} {k : U256} (h : ∀ p ∈ ws, p.1 ≠ k) :
    look ws k = 0 := by
  induction ws with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨a, v⟩ := p
    simp only [look]
    rw [ite_cond_eq_false _ _ (eq_false (h (a, v) (by simp)))]
    exact ih fun q hq => h q (by simp [hq])

theorem foldl_slot_eq {s : List (Nat × Nat)} {slot acc : Nat}
    (h : ∀ p ∈ s, p.1 % 2 ^ 256 ≠ slot % 2 ^ 256) :
    s.foldl (fun acc kv => if kv.1 % 2^256 = slot % 2^256 then kv.2 % 2^256 else acc) acc = acc := by
  induction s generalizing acc with
  | nil => rfl
  | cons p r ih =>
    simp only [List.foldl]
    rw [ite_cond_eq_false _ _ (eq_false (h p (by simp)))]
    exact ih fun q hq => h q (by simp [hq])

theorem slotValue_mod' (s : List (Nat × Nat)) (k : Nat) :
    SolarTV.slotValue s (k % 2 ^ 256) = SolarTV.slotValue s k := by
  unfold SolarTV.slotValue
  simp only [Nat.mod_mod]

theorem keysOk_slot {ws : List (U256 × U256)} {s : List (Nat × Nat)} (h : keysOk ws s = true)
    (slot : Nat) : (look ws (BitVec.ofNat 256 slot)).toNat = SolarTV.slotValue s slot := by
  simp only [keysOk, List.all_eq_true, beq_iff_eq] at h
  by_cases hm : BitVec.ofNat 256 slot ∈ ws.map Prod.fst ++ s.map fun p => BitVec.ofNat 256 p.1
  · rw [h _ hm, BitVec.toNat_ofNat, slotValue_mod']
  · simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and] at hm
    rw [look_eq_zero fun p hp e => hm.1 p hp e]
    unfold SolarTV.slotValue
    rw [foldl_slot_eq]
    · rfl
    · intro p hp e
      apply hm.2 p hp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      exact e

/-- Whether the evaluator runs `init` within the gas of the creation, to the runtime bytes `code`
and the storage `s`. -/
def check (fuel : Nat) (init code : ByteArray) (s : List (Nat × Nat)) : Bool :=
  match run init fuel initCfg with
  | some (o, ws, n) =>
    decide (n ≤ 10000000) && o.toList.map (·.toNat) == code.data.toList.map (·.toNat) && keysOk ws s
  | none => false

/-- **Deployment from the check**: the generic creation frame, with nothing stepped by hand. -/
theorem deploys_of_check {init code : ByteArray} {s : List (Nat × Nat)} (fuel : Nat)
    (h : check fuel init code s = true) : Deploys init code s := by
  unfold check at h
  split at h
  · rename_i o ws n hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hn, ho⟩, hk⟩ := h
    obtain ⟨obs, hrun, hs, hout, hst⟩ := observes fuel hr hn
    exact ⟨obs, hrun, hs, by rw [hout, ho], fun k => by rw [hst, keysOk_slot hk]⟩
  · simp at h

/-- A creation whose run leaves another word at some slot does not deploy `s`. -/
theorem not_deploys_of_slot {init code o : ByteArray} {ws : List (U256 × U256)} {n : Nat}
    {s : List (Nat × Nat)} (fuel : Nat) (h : run init fuel initCfg = some (o, ws, n))
    (hn : n ≤ 10000000) (k : Nat)
    (hk : (look ws (BitVec.ofNat 256 k)).toNat ≠ SolarTV.slotValue s k) :
    ¬ Deploys init code s := by
  rintro ⟨obs', hrun', -, -, hst'⟩
  obtain ⟨obs, hrun, -, -, hst⟩ := observes fuel h hn
  rw [hrun] at hrun'
  cases hrun'
  exact hk (by rw [← hst, hst'])

/-- A creation whose run returns other bytes does not deploy `code`. -/
theorem not_deploys_of_output {init code o : ByteArray} {ws : List (U256 × U256)} {n : Nat}
    {s : List (Nat × Nat)} (fuel : Nat) (h : run init fuel initCfg = some (o, ws, n))
    (hn : n ≤ 10000000) (ho : o.toList.map (·.toNat) ≠ code.data.toList.map (·.toNat)) :
    ¬ Deploys init code s := by
  rintro ⟨obs', hrun', -, hout', -⟩
  obtain ⟨obs, hrun, -, hout, -⟩ := observes fuel h hn
  rw [hrun] at hrun'
  cases hrun'
  exact ho (by rw [← hout, hout'])

/-- info: 'Verify.Lifecycle.Creation.deploys_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys_of_check

/-- Whether the evaluator runs `init` within the gas of the creation to other runtime bytes than
`code` or to another storage than `s`. -/
def refutes (fuel : Nat) (init code : ByteArray) (s : List (Nat × Nat)) : Bool :=
  match run init fuel initCfg with
  | some (o, ws, n) =>
    decide (n ≤ 10000000) && (o.toList.map (·.toNat) != code.data.toList.map (·.toNat) || !keysOk ws s)
  | none => false

theorem keysOk_false {ws : List (U256 × U256)} {s : List (Nat × Nat)} (h : keysOk ws s = false) :
    ∃ k : Nat, (look ws (BitVec.ofNat 256 k)).toNat ≠ SolarTV.slotValue s k := by
  simp only [keysOk, List.all_eq_false, beq_iff_eq] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k.toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hk⟩

/-- **No deployment, from the check**: a creation the evaluator runs to other bytes or another
storage does not deploy them. -/
theorem not_deploys_of_refutes {init code : ByteArray} {s : List (Nat × Nat)} (fuel : Nat)
    (h : refutes fuel init code s = true) : ¬ Deploys init code s := by
  unfold refutes at h
  split at h
  · rename_i o ws n hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_true'] at h
    obtain ⟨hn, ho | hk⟩ := h
    · exact not_deploys_of_output fuel hr hn ho
    · obtain ⟨k, hk⟩ := keysOk_false hk
      exact not_deploys_of_slot fuel hr hn k hk
  · simp at h

/-- The runtime bytes `code` with the word `w` written at `off`, as a constructor patches an
immutable into the copy of its runtime code. -/
def patchWord (code : ByteArray) (off : Nat) (w : U256) : ByteArray :=
  memoryWrite code off (wordBytes w)

/-- info: 'Verify.Lifecycle.Creation.not_deploys_of_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_deploys_of_refutes

end Verify.Lifecycle.Creation
