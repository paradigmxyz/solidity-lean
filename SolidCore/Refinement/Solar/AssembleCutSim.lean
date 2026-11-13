import SolidCore.Refinement.Solar.AssembleLoopSim
import SolidCore.Refinement.Solar.AssembleMem

/-!
# The simulation of a block, cut at GAS

GAS pushes the gas left, so no run with gas to spare shows what it pushes at the run's own gas:
`AssembleLoop.exec_simL` cannot pass it. `execC` runs a block as `exec` does up to the first
GAS, call or creation, and stops there (`CRes.cut`), before it. `exec_simC` is `exec_simL` for
`execC` and a checker that also takes GAS (`blockOkC`): a block's instructions give SolarTV's halt
or next block, as there, or a stop at GAS with EthLib's frame at GAS's offset related to SolarTV's
state, the check of the rest of the block and its invariant. `AssembleCut` runs GAS at the run's
own gas and resumes from there.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide
open SolarTV.EVM.Program

/-! ## A block up to its first GAS, call or creation -/

/-- What a block's instructions give up to the first GAS, call or creation: SolarTV's result, or
that instruction with the rest of the block, the stack and the state before it. -/
inductive CRes where
  | done (r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕
      (Nat × List Word × SolarTV.Machine.State))
  | cut (i : Assemble.Instr) (rest : List Assemble.Instr) (S : List Word) (s : SolarTV.Machine.State)

/-- The effects whose result is not monotone in gas or is the oracle's answer to a message. -/
def cutEffect : SolarTV.Machine.Effect → Bool
  | .gas | .call _ | .create | .create2 | .keccak256 | .log _ | .calldatacopy => true
  | _ => false

/-- The memory operations that run at the frame's own gas: MLOAD and MSTORE, whose growth of
memory only the gas of the run bounds. -/
def cutOp : SolarTV.EVM.Memory.Op → Bool
  | .load | .store => true
  | _ => false

/-- `exec` up to the first GAS, call or creation. -/
def execC (o : SolarTV.Machine.Oracle) (call : SolarTV.Call) (b : Nat) :
    List Assemble.Instr → List Word → SolarTV.Machine.State → CRes
  | [], stack, s => .done (.inr (b + 1, stack, s))
  | .op op :: rest, stack, s =>
    if cutOp op then .cut (.op op) rest stack s
    else match stepOp (context o call s) op stack s.memory with
    | .error _ => .done (.inl (.invalid, s))
    | .ok (stack, memory) => execC o call b rest stack { s with memory }
  | .effect effect arity :: rest, stack, s =>
    if cutEffect effect then .cut (.effect effect arity) rest stack s
    else if stack.length < arity then .done (.inl (.invalid, s))
    else match effect.apply o call (stack.take arity) s with
      | none => .done (.inl (.invalid, s))
      | some (result, s) =>
        let stack := match result with
          | some value => value :: stack.drop arity
          | none => stack.drop arity
        if stack.length > 1024 then .done (.inl (.invalid, s)) else execC o call b rest stack s
  | .jump target :: _, stack, s =>
    if stack.length + 1 > 1024 then .done (.inl (.invalid, s)) else .done (.inr (target, stack, s))
  | .jumpi target :: rest, stack, s =>
    if stack.length + 1 > 1024 then .done (.inl (.invalid, s))
    else match stack with
      | condition :: stack =>
        if condition = 0 then execC o call b rest stack s else .done (.inr (target, stack, s))
      | [] => .done (.inl (.invalid, s))
  | .pushLabel target :: rest, stack, s =>
    if stack.length + 1 > 1024 then .done (.inl (.invalid, s))
    else execC o call b rest (BitVec.ofNat 256 target :: stack) s
  | .jumpDyn :: _, stack, s =>
    match stack with
    | target :: stack => .done (.inr (target.toNat, stack, s))
    | [] => .done (.inl (.invalid, s))
  | .jumpiDyn :: rest, stack, s =>
    match stack with
    | target :: condition :: stack =>
      if condition = 0 then execC o call b rest stack s else .done (.inr (target.toNat, stack, s))
    | _ => .done (.inl (.invalid, s))
  | .jumpTable targets :: _, stack, s =>
    match stack with
    | index :: stack =>
      match targets[index.toNat]? with
      | some target => .done (.inr (target, stack, s))
      | none => .done (.inl (.invalid, s))
    | [] => .done (.inl (.invalid, s))
  | .stop :: _, _, s => .done (.inl (.stop, s))
  | .ret :: rest, stack, s => .cut .ret rest stack s
  | .revert :: rest, stack, s => .cut .revert rest stack s
  | .invalid :: _, _, s => .done (.inl (.invalid, s))

/-- `exec` is `execC` and, at a stop, `exec` from the instruction it stopped at. -/
theorem exec_eq_execC (o : SolarTV.Machine.Oracle) (call : SolarTV.Call) (b : Nat) :
    ∀ (is : List Assemble.Instr) (S : List Word) (s : SolarTV.Machine.State),
      exec o call b is S s = match execC o call b is S s with
        | .done r => r
        | .cut i rest S' s' => exec o call b (i :: rest) S' s'
  | [], _, _ => rfl
  | .op op :: rest, S, s => by
    by_cases hc : cutOp op = true
    · simp only [execC, hc, ite_true]
    · have hc' : cutOp op = false := by simpa using hc
      cases h : stepOp (context o call s) op S s.memory with
      | error _ => simp [exec, execC, h, hc']
      | ok r =>
        obtain ⟨S', m⟩ := r
        simp only [exec, execC, h, hc', Bool.false_eq_true, ite_false]
        exact exec_eq_execC o call b rest _ _
  | .effect e a :: rest, S, s => by
    by_cases hc : cutEffect e = true
    · simp only [execC, hc, ite_true]
    · by_cases hl : S.length < a
      · simp [exec, execC, hc, hl]
      · cases happ : SolarTV.Machine.Effect.apply o call e (S.take a) s with
        | none => simp [exec, execC, hc, hl, happ]
        | some r =>
          obtain ⟨res, s'⟩ := r
          cases res <;>
          · simp only [exec, execC, hc, hl, happ, Bool.false_eq_true, ite_false]
            split_ifs <;> first | rfl | exact exec_eq_execC o call b rest _ _
  | .jump t :: rest, S, s => by
    simp only [exec, execC]
    split_ifs <;> rfl
  | .jumpi t :: rest, S, s => by
    cases S with
    | nil => simp only [exec, execC]; split_ifs <;> rfl
    | cons x S =>
      simp only [exec, execC]
      split_ifs <;> first | rfl | exact exec_eq_execC o call b rest _ _
  | .pushLabel t :: rest, S, s => by
    simp only [exec, execC]
    split_ifs <;> first | rfl | exact exec_eq_execC o call b rest _ _
  | .jumpDyn :: rest, S, s => by cases S <;> simp [exec, execC]
  | .jumpiDyn :: rest, S, s => by
    match S with
    | [] => simp [exec, execC]
    | [_] => simp [exec, execC]
    | x :: y :: S =>
      simp only [exec, execC]
      split_ifs <;> first | rfl | exact exec_eq_execC o call b rest _ _
  | .jumpTable ts :: rest, S, s => by
    cases S with
    | nil => simp [exec, execC]
    | cons x S => cases h : ts[x.toNat]? <;> simp [exec, execC, h]
  | .stop :: rest, S, s => rfl
  | .ret :: rest, S, s => rfl
  | .revert :: rest, S, s => rfl
  | .invalid :: rest, S, s => rfl

/-! ## SolarTV's steps, up to a stop -/

theorem execC_stack {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {op : SolarTV.EVM.Op} {rest : List Assemble.Instr} {S next : List Word} {s : SolarTV.Machine.State}
    (hstep : SolarTV.EVM.step (context o call s) op S = some next) (h1 : S.length ≤ 1024)
    (h2 : next.length ≤ 1024) :
    execC o call b (.op (.stack op) :: rest) S s = execC o call b rest next s := by
  simp [execC, cutOp, stepOp, SolarTV.EVM.stepChecked, hstep, Except.map,
    show ¬ 1024 < S.length by omega, show ¬ 1024 < next.length by omega]

theorem exec_storeC {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {x y : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1023) :
    exec o call b (.op .store :: rest) (x :: y :: S) s =
      exec o call b rest S { s with memory := s.memory.store x.toNat y } := by
  have h1 : ¬ 1024 < S.length + 1 + 1 := by omega
  simp [exec, stepOp, h1]

theorem exec_loadC {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {x : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1024) :
    exec o call b (.op .load :: rest) (x :: S) s =
      exec o call b rest (s.memory.load x.toNat :: S) { s with memory := s.memory.expand x.toNat 32 } := by
  have h1 : ¬ 1024 < S.length + 1 := by omega
  simp [exec, stepOp, h1]

theorem execC_effect0 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {e : SolarTV.Machine.Effect} {w : Word} {S : List Word}
    {s : SolarTV.Machine.State} (he : cutEffect e = false)
    (happ : SolarTV.Machine.Effect.apply o call e [] s = some (some w, s))
    (h : S.length < 1024) :
    execC o call b (.effect e 0 :: rest) S s = execC o call b rest (w :: S) s := by
  simp [execC, he, happ, show ¬ 1024 < S.length + 1 by omega]

theorem execC_effect1 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {e : SolarTV.Machine.Effect} {x w : Word} {S : List Word}
    {s : SolarTV.Machine.State} (he : cutEffect e = false)
    (happ : SolarTV.Machine.Effect.apply o call e [x] s = some (some w, s)) (h : S.length < 1024) :
    execC o call b (.effect e 1 :: rest) (x :: S) s = execC o call b rest (w :: S) s := by
  simp [execC, he, happ, show ¬ 1024 < S.length + 1 by omega]

theorem execC_effect2 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {e : SolarTV.Machine.Effect} {x y : Word} {S : List Word}
    {s s' : SolarTV.Machine.State} (he : cutEffect e = false)
    (happ : SolarTV.Machine.Effect.apply o call e [x, y] s = some (none, s')) (h : S.length ≤ 1024) :
    execC o call b (.effect e 2 :: rest) (x :: y :: S) s = execC o call b rest S s' := by
  simp [execC, he, happ, show ¬ 1024 < S.length by omega]

theorem exec_keccakC {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {x y : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1024) :
    exec o call b (.effect .keccak256 2 :: rest) (x :: y :: S) s =
      exec o call b rest (o.keccak ((s.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S)
        { s with memory := s.memory.expand x.toNat y.toNat } := by
  simp [exec, SolarTV.Machine.Effect.apply, show ¬ 1024 < S.length + 1 by omega]

theorem exec_cdcC {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {d off sz : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length ≤ 1024) :
    exec o call b (.effect .calldatacopy 3 :: rest) (d :: off :: sz :: S) s =
      exec o call b rest S { s with
        memory := s.memory.write d.toNat sz.toNat
          (fun i => SolarTV.Machine.calldataByte call (off.toNat + i)) } := by
  simp [exec, SolarTV.Machine.Effect.apply, show ¬ 1024 < S.length by omega]

theorem exec_logC {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {x y : Word} {tops S : List Word} {s : SolarTV.Machine.State}
    (h : S.length ≤ 1024) :
    exec o call b (.effect (.log tops.length) (tops.length + 2) :: rest) (x :: y :: (tops ++ S)) s =
      exec o call b rest S ⟨s.memory.expand x.toNat y.toNat, s.storage, s.transient,
        s.world ++ [.log tops ((s.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩ := by
  have ht : (x :: y :: (tops ++ S)).take (tops.length + 2) = x :: y :: tops := by simp
  have hd : (x :: y :: (tops ++ S)).drop (tops.length + 2) = S := by simp
  simp only [exec, List.length_cons, List.length_append, ht, hd]
  simp [SolarTV.Machine.Effect.apply, show ¬ 1024 < S.length by omega,
    show ¬ tops.length + S.length + 1 + 1 < tops.length + 2 by omega]
  try rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_bytes]

/-! ## What the simulation uses of the check -/

/-- The facts of the check the simulation of a block uses: those of `GlobL` but the blocks' checks. -/
structure GlobT (p : Assemble.Program) (c : Cert) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 200
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size

/-- `InvL.target` from `GlobT`. -/
theorem InvL.targetT {p : Assemble.Program} {c : Cert} {code : ByteArray}
    (G : GlobT p c code) {call : SolarTV.Call} {t m : Nat} {items : List Item} {k R pc : Nat}
    {S : List Word} {s : SolarTV.Machine.State} {M : ByteArray} {g g' : Nat}
    (I : InvL c code call items k R pc S s M g) (htn : t < p.blocks.length)
    (htgt : isTarget p c t = true) (hm : m ≤ k) (hg : g ≤ g' + 22100 * m) :
    EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R (c.offset t) s M g' where
  seg := (G.target t htn htgt).2.2
  gas := by
    have := I.gas
    have hm' : 22100 * m ≤ 22100 * k := Nat.mul_le_mul_left _ hm
    rw [Nat.mul_add] at this
    omega
  le_top := I.le_top
  mem := I.mem

/-! ## The checker with GAS -/

/-- GAS, with no operands. -/
def isGasI : Assemble.Instr → Bool
  | .effect .gas 0 => true
  | _ => false

theorem isGasI_eq {i : Assemble.Instr} (h : isGasI i = true) : i = .effect .gas 0 := by
  unfold isGasI at h
  split at h
  · rfl
  · cases h

/-- MLOAD and MSTORE, which run at the frame's own gas. -/
def isLoadI : Assemble.Instr → Bool
  | .op .load => true
  | _ => false

def isStoreI : Assemble.Instr → Bool
  | .op .store => true
  | _ => false

def isRetI : Assemble.Instr → Bool
  | .ret => true
  | _ => false

def isRevI : Assemble.Instr → Bool
  | .revert => true
  | _ => false

def isKecI : Assemble.Instr → Bool
  | .effect .keccak256 2 => true
  | _ => false

def isLogI : Assemble.Instr → Bool
  | .effect (.log n) a => decide (n ≤ 4) && decide (a = n + 2)
  | _ => false

def isCdcI : Assemble.Instr → Bool
  | .effect .calldatacopy 3 => true
  | _ => false

/-- MLOAD, MSTORE, RETURN, REVERT, KECCAK256, LOGn and CALLDATACOPY: memory at ranges only the
gas of the run bounds. -/
def isMemCutI (i : Assemble.Instr) : Bool :=
  isLoadI i || isStoreI i || isRetI i || isRevI i || isKecI i || isLogI i || isCdcI i

theorem execC_cut {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {i : Assemble.Instr} {rest : List Assemble.Instr} {S : List Word} {s : SolarTV.Machine.State}
    (h : isMemCutI i = true) : execC o call b (i :: rest) S s = .cut i rest S s := by
  cases i with
  | op op => cases op <;> simp_all [isMemCutI, isLoadI, isStoreI, isRetI, isRevI, isKecI, isLogI, isCdcI, execC, cutOp]
  | ret => rfl
  | revert => rfl
  | effect e a =>
    cases e <;> simp_all [isMemCutI, isLoadI, isStoreI, isRetI, isRevI, isKecI, isLogI, isCdcI] <;>
      simp [execC, cutEffect]
  | _ => simp_all [isMemCutI, isLoadI, isStoreI, isRetI, isRevI, isKecI, isLogI, isCdcI]

/-- The instructions a block's segment stops at. -/
def isCutI (i : Assemble.Instr) : Bool := isGasI i || isMemCutI i

/-- `blockOkL` with GAS: it pushes a data word, for one item of the budget. -/
def blockOkC (p : Assemble.Program) (c : Cert) (mx : List Nat) (b : Nat) :
    Nat → List Word → List Ty → Nat → List Assemble.Instr → Bool
  | h, _, ty, _, [] => fallOkL p c mx b h ty
  | h, known, ty, k, i :: rest =>
    match turnedElse c b i rest with
    | some e =>
      decide (3 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkL p c mx b e (h - 1) ty.tail &&
        fallOkL p c mx b (h - 1) ty.tail
    | none =>
      if dropped p b i rest then
        match i with
        | .stop => true
        | _ => fallOkL p c mx b h ty
      else if isGasI i then
        decide (1 ≤ k) && blockOkC p c mx b (h + 1) [] (some false :: ty) (k - 1) rest
      else if isLoadI i then
        decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 && decide (2 ^ 140 ≤ c.top) &&
          blockOkC p c mx b h [] (some false :: ty.drop 1) (k - 1) rest
      else if isStoreI i then
        decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 && decide (2 ^ 140 ≤ c.top) &&
          blockOkC p c mx b (h - 2) [] (ty.drop 2) (k - 1) rest
      else if isRetI i || isRevI i then decide (2 ≤ h) && isData ty 2
      else if isKecI i then
        c.env && decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 && decide (2 ^ 140 ≤ c.top) &&
          blockOkC p c mx b (h - 1) [] (some false :: ty.drop 2) (k - 1) rest
      else if isLogI i then
        match i with
        | .effect (.log n) _ =>
          decide (1 ≤ k) && decide (n + 2 ≤ h) && isData ty (n + 2) && decide (2 ^ 140 ≤ c.top) &&
            blockOkC p c mx b (h - (n + 2)) [] (ty.drop (n + 2)) (k - 1) rest
        | _ => false
      else if isCdcI i then
        decide (1 ≤ k) && decide (3 ≤ h) && isData ty 3 && decide (2 ^ 140 ≤ c.top) &&
          blockOkC p c mx b (h - 3) [] (ty.drop 3) (k - 1) rest
      else blockStepL p c mx b (fun h known ty k => blockOkC p c mx b h known ty k rest) h known ty k i

/-! ## The budget of memory and gas -/

/-- The price of memory `M` and the gas `g` are at most `G`: what a frame keeps along a run that
pays for each growth of its memory. -/
def MemBudget (G : Nat) (M : ByteArray) (g : Nat) : Prop := memoryGasCost M.size + g ≤ G

/-- Spending gas with memory as it was keeps the budget. -/
theorem MemBudget.spend {G g g' : Nat} {M : ByteArray} (h : MemBudget G M g) (hg : g' ≤ g) :
    MemBudget G M g' := by
  unfold MemBudget at *
  omega

/-- **Paying for a growth of memory keeps the budget**: the grown memory's price exceeds the old one
by the growth's cost, which the frame pays. -/
theorem MemBudget.grow {G g X : Nat} {M M' : ByteArray} (hmod : M.size % 32 = 0) {o sz : Word}
    (hb : MemBudget G M g) (hg : X + (extendMemory M.size [(o, sz)]).cost ≤ g)
    (hM' : M'.size = M.size + (extendMemory M.size [(o, sz)]).expandBy) :
    MemBudget G M' (g - (X + (extendMemory M.size [(o, sz)]).cost)) := by
  have hc := extendMemory_cost M.size [(o, sz)]
  rw [ceil32_of_mod hmod] at hc
  have hm := memoryGasCost_mono (Nat.le_add_right M.size (extendMemory M.size [(o, sz)]).expandBy)
  unfold MemBudget at *
  rw [hM']
  omega

/-- A triple between frames at known gas ends with at most the gas it starts with. -/
theorem gas_le_of_hoareG {code : ByteArray} {msg : Message .fusaka} {pc pc' : Nat}
    {T T' : List Word} {M M' : ByteArray} {gas g : Nat} {st st' : State.TransactionState}
    {ss ss' : Substate} {rd rd' : ByteArray}
    (h : HoareG .fusaka (At code msg pc T M gas st ss rd) (At code msg pc' T' M' g st' ss' rd'))
    (hT : T.length ≤ 1024) : g ≤ gas := by
  let e : Evm .fusaka Nat :=
    Evm.mk pc ⟨T, hT⟩ M code (validJumpDestinations code) gas true msg .empty rd st ss none
  obtain ⟨e', hr, hq⟩ := h e ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hle : e'.gas ≤ e.gas := Reaches.gasHeld_le (fun hs => Step.gasHeld_le hs.1) hr
  rw [hq.2.2.2.2.2.2.1] at hle
  exact hle

/-- `SimOutL` with the budget `Gs` at the next block's entry. -/
def SimOutB (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState) (ss : Substate)
    (b R pc : Nat) (T : List Word) (M : ByteArray) (g Gs : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧
      (t < p.blocks.length → c.need t ≤ S'.length ∧ S'.length ≤ maxH mx t) ∧
      (t = b + 1 ∨ isTarget p c t = true)) ∧
      ∃ pc' T' M' g' st' ss', HoareG .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧
        EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R pc' s' M' g' ∧
        Rel msg ss0 st' ss' s' ∧ MemBudget Gs M' g'

theorem SimOutB.pre {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState}
    {ss ss1 : Substate} {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 Gs : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutB p c mx code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 Gs r) :
    SimOutB p c mx code call msg ss0 st ss b R pc T M g Gs r := by
  match r, h1 with
  | .inl (_, _), hspec => exact SpecG.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hinv, hrel, hb⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hinv, hrel, hb⟩

/-- What a block's instructions give: `SimOutL` for SolarTV's halt or next block, and at a stop, GAS,
with EthLib's frame at its offset, its stack related, the check of the rest and the invariant. -/
def SimOutC (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate)
    (st : State.TransactionState) (ss : Substate) (b R pc : Nat) (T : List Word) (M : ByteArray)
    (g Gs : Nat) : CRes → Prop
  | .done r => SimOutB p c mx code call msg ss0 st ss b R pc T M g Gs r
  | .cut i rest S' s' => isCutI i = true ∧
    ∃ (h : Nat) (known : List Word) (ty : List Ty) (k pc' : Nat) (T' : List Word) (M' : ByteArray)
      (g' : Nat) (st' : State.TransactionState) (ss' : Substate),
      HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc' T' M' g' st' ss' .empty) ∧
      blockOkC p c mx b h known ty k (i :: rest) = true ∧ h ≤ S'.length ∧
      S'.length + c.need b ≤ h + maxH mx b ∧ known <+: S' ∧ SR c ty S' T' ∧
      InvL c code call (lowerInstrs p c b (i :: rest) ++
        lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k R pc' S' s' M' g' ∧
      Rel msg ss0 st' ss' s' ∧ MemBudget Gs M' g'

theorem SimOutC.pre {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 Gs : Nat} {r : CRes}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutC p c mx code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 Gs r) :
    SimOutC p c mx code call msg ss0 st ss b R pc T M g Gs r := by
  match r, h1 with
  | .done _, h1 => exact SimOutB.pre h h1
  | .cut _ _ _ _, ⟨hi, hc, known, ty, k, pc', T', M', g', st', ss', hh, rest'⟩ =>
    exact ⟨hi, hc, known, ty, k, pc', T', M', g', st', ss', Triple.seq h hh, rest'⟩

set_option hygiene false in
/-- The budget after an instruction that leaves memory as it was. -/
local macro "bud_tac" : tactic => `(tactic| first | exact Hb | exact MemBudget.spend Hb (by omega))

set_option hygiene false in
/-- The budget after an instruction that grows memory and pays for it. -/
local macro "bud_mem" : tactic => `(tactic| exact MemBudget.grow hmod Hb (by omega) hM')

set_option hygiene false in
/-- The bound of the stack in lockstep with the height of the check. -/
local macro "hu_tac" : tactic => `(tactic| first | omega | (simp at hu ⊢; omega) | (simp; omega))

open SolarTV.EVM.Program in
/-- EthLib runs the code of a block's instructions from the offset of the next one as SolarTV
runs them, over steps monotone in gas, with gas for the reserve `R` beyond the block. -/
theorem exec_simC {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray} (G : GlobT p c code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (b : Nat) (hb : b < p.blocks.length) (Rv Gs : Nat) :
    ∀ (is : List Assemble.Instr) (h : Nat) (known : List Word) (ty : List Ty) (S T : List Word) (k : Nat)
      (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate),
      blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → known <+: S → SR c ty S T →
      InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k Rv
        pc S s M g → Rel msg ss0 st ss s → MemBudget Gs M g →
      SimOutC p c mx code call msg ss0 st ss b Rv pc T M g Gs (execC o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, _, hR, I, R, Hb => by
    simp only [blockOkC, fallOkL, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have I2 := I.entry
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [execC, SimOutC, SimOutB]
    exact ⟨⟨by omega, fun ht => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
      Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I2, R, Hb⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R, Hb => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOkC, hT, jumpOkL, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, ⟨hfall, hfty⟩, hcost'⟩ := hok
      simp only [lowerInstrs, hT, List.cons_append, List.nil_append] at I
      rcases S with _ | ⟨cond, S'⟩
      · simp at hh; omega
      rcases T with _ | ⟨cond', T'⟩
      · simp at hL
      obtain rfl := (SR.head hR hdat).symm
      have hR' := (SR.uncons.1 hR).2
      simp only [List.length_cons] at hL
      obtain ⟨n0, hd0, hs0⟩ := I.seg.head
      obtain ⟨n1, hd1, hs1⟩ := hs0.head
      obtain ⟨n2, hd2, hseg⟩ := hs1.head
      simp only [Item.expected] at hd0 hd1 hd2
      obtain ⟨hlt0, hcode0, rfl⟩ := op_item hd0
      obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
      have hS := I.stack; have hG := I.gas
      simp only [List.length_cons] at hS hh hu
      obtain ⟨g0, hg0, hisz⟩ := stack_ruleG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
        (op := .iszero) (stack := cond :: T') (next := EvmRules.Evm.iszero cond :: T')
        (r := o.env "returndatasize" s.world []) rfl hlt0 hcode0 rfl (by omega)
        (by simp only [List.length_cons]; omega)
      have hg0u := gas_le_of_hoareG hisz (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
      obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss)
        (gas := g0) (stack := EvmRules.Evm.iszero cond :: T') hd1 (by omega)
        (by simp only [List.length_cons]; omega)
      have hg1u := gas_le_of_hoareG hpush (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
      by_cases hc : cond = 0
      · -- The condition is zero: ISZERO gives one and the code jumps to the else block.
        subst hc
        have hoff := toNat_offset (G.target e hen hetgt).2.1 G.size_lt
        have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) iszero_zero
          (by rw [hoff]; exact (G.target e hen hetgt).1)
        rw [hoff] at hj
        simp only [execC, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega,
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOutC, SimOutB]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr hetgt⟩, c.offset e, T', M, g1 - 10, st,
          ss, Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR',
          I.targetT G hen hetgt (m := 3) (by omega) (by omega), R, by bud_tac⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [execC, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOutC, SimOutB]
        refine ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR',
          ⟨hseg, ?_, I.le_top, I.mem⟩, R, by bud_tac⟩
        have := I.gas
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOkC, hT, hD, ite_true, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [execC, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutC, SimOutB]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
            Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I.entry, R, by bud_tac⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [execC, SimOutC, SimOutB]
          exact SpecG.consequence (stop_of_size_leG (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      by_cases hG : isGasI i = true
      · obtain rfl := isGasI_eq hG
        simp only [execC, cutEffect, ite_true, SimOutC]
        exact ⟨rfl, h, known, ty, k, pc, T, M, g, st, ss, Triple.of_imp fun _ h => h,
          hok, hh, hu, hk, hR, I, R, by bud_tac⟩
      have hG' : isGasI i = false := by simpa using hG
      by_cases hMc : isMemCutI i = true
      · rw [execC_cut hMc]
        simp only [SimOutC]
        exact ⟨by simp [isCutI, hMc], h, known, ty, k, pc, T, M, g, st, ss, Triple.of_imp fun _ h => h,
          hok, hh, hu, hk, hR, I, R, Hb⟩
      have hMc' : isMemCutI i = false := by simpa using hMc
      simp only [isMemCutI, Bool.or_eq_false_iff] at hMc'
      obtain ⟨⟨⟨⟨⟨⟨hnl, hns⟩, hnr⟩, hnv⟩, hnk⟩, hnlog⟩, hncd⟩ := hMc'
      have hok' : blockStepL p c mx b (fun h known ty k => blockOkC p c mx b h known ty k rest) h known ty k i =
          true := by
        simpa only [blockOkC, hT, hD', hG', hnl, hns, hnr, hnv, hnk, hnlog, hncd, Bool.or_false, Bool.false_eq_true, ite_false] using hok
      have I' : InvL c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      clear hok hD hD' hT
      have IH := exec_simC (mx := mx) (o := o) (ss0 := ss0) G hdata hvalue hstatic hself hcaller ho hbenv htx he b hb Rv Gs rest
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      · rcases mop with sop | _ | _ | _ | _ | _ | _
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hg1u := gas_le_of_hoareG hpush (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [execC_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOutC.pre hpush (IH (h + 1) (v :: known.take 1) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega) (by hu_tac)
              ((List.prefix_cons_inj v).2 ((List.take_prefix 1 known).trans hk))
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R (by bud_tac))
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', hlock, known', hkn,
              hok⟩ := stack_simL (ctx := context o call s) hne hok' hh hk hR
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            obtain ⟨hlt, hcode, rfl⟩ := op_item hd
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_ruleG (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            have hg1u := gas_le_of_hoareG hrule (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
            rw [execC_stack hstep (by omega) (by omega)]
            exact SimOutC.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega) (by hu_tac)
              hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R (by bud_tac))
        · -- MLOAD, at the frame's own gas.
          simp [isLoadI] at hnl
        · -- MSTORE, at the frame's own gas.
          simp [isStoreI] at hns
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
      · rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | name | _
        all_goals try (simp [blockStepL] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [execC_effect1 rfl (w := s.storage x) rfl (by omega)]
          have hrule := Logic.sloadG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (key := x) (rest := T') (gas := g) (by decide) hlt hcode rfl
            (by split <;> omega)
          rw [R.storage x] at hrule
          refine SimOutC.pre hrule ?_
          have hreads := fun k : Word => State.TransactionState.recordStorageRead_reads st
            msg.currentTarget msg.currentTarget (U256.toBeBytes x) (U256.toBeBytes k) default
          refine IH h [] _ _ _ (k - 1) s (pc + 1) M _ _ _ hok (by simp; omega) (by hu_tac) (List.nil_prefix)
            (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by split <;> omega))
            ⟨fun k => ?_, ?_, R.logs⟩ (by bud_tac)
          · rw [(hreads k).2.1]
            exact R.storage k
          · rw [(hreads x).1]
            exact R.account
        · -- SSTORE.
          rcases ar with _ | _ | _ | ar
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h2⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨v, S'⟩⟩
          · simp at hh; omega
          · simp at hh; omega
          rcases T with _ | ⟨x', _ | ⟨v', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [execC_effect2 rfl (s' := { s with storage := SolarTV.Machine.update s.storage x v }) rfl
            (by omega)]
          have hcost := sstoreCost_le (st.getStorageOriginal msg.currentTarget (U256.toBeBytes x))
            (st.getStorage msg.currentTarget (U256.toBeBytes x)) v
            (decide (U256.toBeBytes x ∉ ss.accessedStorageKeys.getD msg.currentTarget ∅))
          obtain ⟨st', hnew, hothers, -, hacc, -, -, hrule⟩ := sstore_of_accountG
            (message := msg) (memory := M) (state := st) (substate := ss) (returnData := .empty)
            (key := x) (new := v) (rest := T') (gas := g) (by decide) (by decide) hlt hcode hstatic
            rfl (by simp only [CALL_STIPEND]; omega) (by omega) R.account
          refine SimOutC.pre hrule ?_
          refine IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) M _ _ _ hok (by omega) (by hu_tac) (List.nil_prefix)
            hR' ?_ ⟨fun k => ?_, by rw [hacc]; exact R.account, R.logs⟩ (by bud_tac)
          · exact ⟨hseg, by omega, by omega, I'.le_top, I'.mem⟩
          by_cases hk : k = x
          · subst hk
            rw [hnew]
            simp [SolarTV.Machine.update]
          · rw [hothers _ _ (Or.inr fun he => hk (U256.toBeBytes_inj he)), R.storage k]
            simp [SolarTV.Machine.update, hk]
        · -- CALLDATALOAD.
          rcases ar with _ | _ | ar
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [execC_effect1 rfl (w := SolarTV.Machine.calldataWord call x) rfl (by omega)]
          have hrule := Logic.calldataloadG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (start := x) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [hdata, ← calldataWord_eq] at hrule
          exact SimOutC.pre hrule (IH h [] _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega) (by hu_tac)
            (List.nil_prefix) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
        · -- CALLDATASIZE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [execC_effect0 rfl (w := BitVec.ofNat 256 call.calldata.size) rfl (by omega)]
          have hrule := Logic.calldatasizeG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hdata] at hrule
          exact SimOutC.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
        · -- CALLVALUE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [execC_effect0 rfl (w := BitVec.ofNat 256 call.callvalue) rfl (by omega)]
          have hrule := Logic.callvalueG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hvalue] at hrule
          exact SimOutC.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
        · -- CALLER.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          obtain ⟨hoc, -⟩ := ho henv
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [execC_effect0 rfl (w := o.caller.setWidth 256) rfl (by omega)]
          have hrule := Logic.callerG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hcaller, ← hoc] at hrule
          exact SimOutC.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
        · -- ADDRESS.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [execC_effect0 rfl (w := BitVec.ofNat 256 SolarTV.environment.callee) rfl (by omega)]
          have hrule := Logic.addressG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hself, address_word] at hrule
          exact SimOutC.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
        · -- LOGn.
          rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          simp only [blockStepL, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨hn4, rfl⟩, hk1⟩, hnh⟩, hdat⟩, hin⟩, hlc⟩, hok⟩ := hok'
          simp [isLogI, hn4] at hnlog
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp [isKecI] at hnk
        · -- An environment read of the block or the transaction.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hreads, hsome⟩, hk1⟩, hok⟩ := hok'
          obtain ⟨⟨byte, w⟩, hread⟩ := Option.isSome_iff_exists.1 hsome
          simp only [lowerInstr, hread, Option.map_some, Option.getD_some,
            List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [execC_effect0 rfl (w := BitVec.ofNat 256 w)
            (by simp [SolarTV.Machine.Effect.apply, he hreads name byte w hread]) (by omega)]
          have hrule := env_readG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
            (stack := T) hread hlt hcode hbenv htx (by omega) (by unfold STACK_LIMIT; omega)
          exact SimOutC.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
      · -- JUMP.
        simp only [blockStepL, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hk2, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩ := hok'
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, -⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd1 (by omega) (by omega)
        have hg1u := gas_le_of_hoareG hpush (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (rest := T) hlt2 hcode2 (show 8 ≤ g1 by omega)
          (by rw [hoff]; exact (G.target t htn htgt).1)
        rw [hoff] at hj
        simp only [execC, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutC, SimOutB]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T, M, g1 - 8, st, ss,
          Triple.seq hpush hj, SR.le hty hR,
          I'.targetT G htn htgt (m := 2) (by omega) (by omega), R, by bud_tac⟩
      · -- JUMPI.
        simp only [blockStepL, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩, hok'⟩ := hok'
        rcases S with _ | ⟨cond, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨cond', T'⟩
        · simp at hL
        obtain rfl := (SR.head hR hdat).symm
        have hR' := (SR.uncons.1 hR).2
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, hseg⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := cond :: T') hd1 (by omega) (by simp; omega)
        have hg1u := gas_le_of_hoareG hpush (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
        by_cases hc : cond = 0
        · subst hc
          have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) rfl
          simp only [execC, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            ite_true]
          exact SimOutC.pre (Triple.seq hpush hj) (IH (h - 1) [] _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (by hu_tac) (List.nil_prefix) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R (by bud_tac))
        · have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [execC, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOutC, SimOutB]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T', M, g1 - 10, st,
            ss, Triple.seq hpush hj, SR.le hty hR',
            I'.targetT G htn htgt (m := 2) (by omega) (by omega), R, by bud_tac⟩
      · -- A pushed return label: a PUSH of the block's offset.
        simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨hk1, hmem⟩, ht32⟩, hok⟩ := hok'
        have hmem' : t ∈ c.rets := by simpa using hmem
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, hseg⟩ := I'.seg.head
        simp only [Item.expected] at hd
        have hS := I'.stack; have hG := I'.gas
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd (by omega) (by omega)
        have hg1u := gas_le_of_hoareG hpush (by first | omega | (simp only [List.length_cons] at *; omega) | simp_all)
        have htn : (BitVec.ofNat 256 t).toNat = t := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        simp only [execC, show ¬ S.length + 1 > 1024 by omega, ite_false]
        exact SimOutC.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega) (by hu_tac)
          (List.nil_prefix) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R (by bud_tac))
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          List.all_eq_true] at hok'
        obtain ⟨⟨⟨hk1, h1⟩, hlab⟩, hall⟩ := hok'
        rcases S with _ | ⟨x, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨y, T'⟩
        · simp at hL
        obtain ⟨hw, hR'⟩ := SR.uncons.1 hR
        rw [hlab] at hw
        obtain ⟨hmem, rfl⟩ := hw
        have hj' := hall _ hmem
        simp only [jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩ := hj'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
          hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
        rw [hoff] at hj
        simp only [execC, SimOutC, SimOutB]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st,
          ss, hj, SR.le hty hR', I'.targetT G htn htgt (m := 1) (by omega) (by omega), R, by bud_tac⟩
      · -- A conditional dynamic jump and a jump table: outside the fragment.
        simp [blockStepL] at hok'
      · simp [blockStepL] at hok'
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        simp only [execC, SimOutC, SimOutB]
        exact SpecG.consequence (Logic.stopG hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      · -- RETURN, at the frame's own gas.
        simp [isRetI] at hnr
      · -- REVERT, at the frame's own gas.
        simp [isRevI] at hnv
      · simp [blockStepL] at hok'




/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.exec_simC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exec_simC

end SolidCore.Refinement.Solar.AssembleLoop
