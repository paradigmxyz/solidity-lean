import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Evm.Lemmas
import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# EVM IR to bytecode, for code with loops: the checker

`Assemble.check` bounds every run by a static potential, the items from a block to the end of the
layout, so it accepts only code whose jumps go forward. This file's checker, `checkL`, accepts
code with loops: each block has a budget, a bound on the items one run of it executes (the
certificate's `costs`), and a jump or a fall may go to any labelled block, backward too. The
budget's item count is spent within a block; across blocks a run executes at most `bmax c` items
per block it enters, so a run of SolarTV that enters `n` blocks runs in EthLib with gas for
`22100 * bmax c` per block (`AssembleLoopRun.lean`), and the other gases follow from EthLib's
facts on runs with less gas (`Logic.LessGas`).

Stack heights: the certificate's `needs` bound each block's entry height from below, as in
`Assemble.check`, and `maxs` from above: a jump from a block entered at most `maxH b` high
with `h` words over the `need b` it was entered with lands at most `h + maxH b - need b`
high, which the checker bounds by the target's `maxH`. So the stack stays below 1024 on every
run however many blocks it enters (`maxH t + budget t ≤ 1000`).

The rest is `Assemble.check`'s: the code's linear decoding is the lowered program at the
layout, labels are valid jump destinations, the stack types, memory accesses at constant
offsets below the certificate's bound, and the same fragment of instructions, with SLT, SGT,
ADDRESS and the reads of the block and the transaction `envRead` names (TIMESTAMP, NUMBER,
CHAINID, COINBASE, GASLIMIT, GASPRICE, ORIGIN) besides. ADDRESS needs no hypothesis: it reads
the callee both semantics fix. The reads need the certificate's `reads` flag, and the theorems
then hold under every oracle whose reads are those of EthLib's environment of the call
(`EnvOk`, met by `envOracle` of any oracle). External calls, GAS, RETURNDATASIZE,
RETURNDATACOPY, CALLDATACOPY, CODECOPY, creations and immutables stay outside.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## The checker -/

/-- Block `t`'s budget: a bound on the items one run of it executes, its label included. -/
def budget (c : Cert) (t : Nat) : Nat := c.costs.getD t 0

/-- The largest budget: a bound on the items of one run of any block. -/
def bmax (c : Cert) : Nat := c.costs.foldr max 0

/-- The highest stack block `t` is entered with. -/
def maxH (mx : List Nat) (t : Nat) : Nat := mx.getD t 0

/-- A jump from block `b` to block `t` with a stack of at least `h` words typed `ty`: `t` is a
labelled block, finds the height and the types it needs, and the stack, at most `h` words over
the `need b` block `b` was entered with, fits `t`'s highest entry. -/
def jumpOkL (p : Program) (c : Cert) (mx : List Nat) (b t h : Nat) (ty : List Ty) : Bool :=
  decide (t < p.blocks.length) && isTarget p c t && decide (c.need t ≤ h) && tyLe ty (c.entry t) &&
    decide (h + maxH mx b ≤ maxH mx t + c.need b)

/-- Block `b` falls into the next one with a stack of at least `h` words typed `ty`. -/
def fallOkL (p : Program) (c : Cert) (mx : List Nat) (b h : Nat) (ty : List Ty) : Bool :=
  (decide (p.blocks.length ≤ b + 1) || decide (c.need (b + 1) ≤ h)) && tyLe ty (c.entry (b + 1)) &&
    decide (h + maxH mx b ≤ maxH mx (b + 1) + c.need b)

/-- `Assemble.blockStep` for block `b` of code with loops: the same check of each instruction,
with `jumpOkL` for its jumps, which put no bound on the target's budget, and MLOAD at a constant
offset below the certificate's bound. -/
def blockStepL (p : Program) (c : Cert) (mx : List Nat) (b : Nat)
    (ok : Nat → List Word → List Ty → Nat → Bool) :
    Nat → List Word → List Ty → Nat → Assemble.Instr → Bool
  | h, known, ty, k, .op (.stack op) =>
    match op with
    | .push v => decide (1 ≤ k) && ok (h + 1) (v :: known.take 1) (some false :: ty) (k - 1)
    | .dup i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 1 ≤ h) &&
      ok (h + 1) (dupKnown known i.val) (tyAt ty i.val :: ty) (k - 1)
    | .swap i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 2 ≤ h) &&
      ok h [] (tySwap ty i.val) (k - 1)
    | .pop => decide (1 ≤ k) && decide (1 ≤ h) && ok (h - 1) [] ty.tail (k - 1)
    | op =>
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat [] (some false :: ty.drop need) (k - 1)
      | none => false
  | h, known, ty, k, .op .store =>
    match known with
    | o :: _ => decide (1 ≤ k) && decide (2 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 2 &&
      ok (h - 2) [] (ty.drop 2) (k - 1)
    | [] => false
  | h, known, ty, k, .op .load =>
    match known with
    | o :: _ => decide (1 ≤ k) && decide (1 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 1 &&
      ok h [] (some false :: ty.drop 1) (k - 1)
    | [] => false
  | h, _, ty, k, .effect .callvalue 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .calldatasize 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .caller 0 =>
    c.env && decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .address 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect (.env name) 0 =>
    c.reads && (envRead name).isSome && decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .calldataload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h [] (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h [] (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sstore 2 => decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 &&
    ok (h - 2) [] (ty.drop 2) (k - 1)
  | h, known, ty, k, .effect .keccak256 2 =>
    match known with
    | o :: s :: _ => c.env && decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 && rangeOk c o s &&
      decide (keccak256Cost s ≤ 22100) && ok (h - 1) [] (some false :: ty.drop 2) (k - 1)
    | _ => false
  | h, known, ty, k, .effect (.log n) a =>
    match known with
    | o :: s :: _ => decide (n ≤ 4) && decide (a = n + 2) && decide (1 ≤ k) && decide (n + 2 ≤ h) &&
      isData ty (n + 2) && rangeOk c o s && decide (logCost n s ≤ 22100) &&
      ok (h - (n + 2)) [] (ty.drop (n + 2)) (k - 1)
    | _ => false
  | h, _, ty, k, .jump t => decide (2 ≤ k) && jumpOkL p c mx b t h ty
  | h, _, ty, k, .jumpi t =>
    decide (2 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkL p c mx b t (h - 1) ty.tail &&
      ok (h - 1) [] ty.tail (k - 2)
  | h, _, ty, k, .pushLabel t =>
    decide (1 ≤ k) && c.rets.contains t && decide (t < 2 ^ 32) && ok (h + 1) [] (some true :: ty) (k - 1)
  | h, _, ty, k, .jumpDyn =>
    decide (1 ≤ k) && decide (1 ≤ h) && tyAt ty 0 == some true &&
      c.rets.all fun t => jumpOkL p c mx b t (h - 1) ty.tail
  | _, _, _, _, .stop => true
  | _, known, ty, _, .ret | _, known, ty, _, .revert =>
    match known with
    | o :: s :: _ => isData ty 2 && rangeOk c o s
    | _ => false
  | _, _, _, _, _ => false

/-- `Assemble.blockOk` for code with loops. -/
def blockOkL (p : Program) (c : Cert) (mx : List Nat) (b : Nat) :
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
      else blockStepL p c mx b (fun h known ty k => blockOkL p c mx b h known ty k rest) h known ty k i

/-- Every block checks from the height and the types it needs, within its budget less its
label's item, with its highest entry stack and budget below 1000 words. -/
def blocksOkL (p : Program) (c : Cert) (mx : List Nat) : Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
      decide (maxH mx b + budget c b ≤ 1000) &&
      blockOkL p c mx b (c.need b) [] (c.entry b) (budget c b - labelItems p c b) instrs &&
      blocksOkL p c mx (b + 1) rest

/-- The checker for code with loops. -/
def checkL (p : Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkL p c mx 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32)

/-! ## What the check gives -/

theorem getD_le_foldr_max : ∀ (l : List Nat) (t : Nat), l.getD t 0 ≤ l.foldr max 0
  | [], _ => by simp
  | x :: l, 0 => by simp
  | x :: l, t + 1 => by
    simp only [List.getD_cons_succ, List.foldr_cons]
    exact Nat.le_trans (getD_le_foldr_max l t) (Nat.le_max_right _ _)

theorem budget_le_bmax (c : Cert) (t : Nat) : budget c t ≤ bmax c := getD_le_foldr_max _ _

theorem blocksOkL_get {p : Program} {c : Cert} {mx : List Nat} : ∀ (l : List (List Assemble.Instr)) (b : Nat),
    blocksOkL p c mx b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ budget c (b + k) ∧ c.need (b + k) ≤ maxH mx (b + k) ∧
      maxH mx (b + k) + budget c (b + k) ≤ 1000 ∧
      blockOkL p c mx (b + k) (c.need (b + k)) [] (c.entry (b + k))
        (budget c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOkL, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [and_assoc] using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOkL, Bool.and_eq_true] at h
    have := blocksOkL_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the check the simulation uses at every block. -/
structure GlobL (p : Program) (c : Cert) (mx : List Nat) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 32
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ budget c t ∧
    c.need t ≤ maxH mx t ∧ maxH mx t + budget c t ≤ 1000 ∧
    blockOkL p c mx t (c.need t) [] (c.entry t) (budget c t - labelItems p c t) p.blocks[t] = true

theorem globL_of_checkL {p : Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkL p code c mx = true) :
    GlobL p c mx code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 := by
  simp only [checkL, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, htop⟩, hsize⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨hmod, htop, hsize, fun t ht htgt => ?_, fun t ht => ?_⟩, hseg, hneed⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (c.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p c t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p c ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksOkL_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## The invariants -/

/-- `Assemble.Inv` with a reserve: inside a block, with `k` items of its budget left and gas for
`R` more items of the blocks the run enters after it. -/
structure InvL (c : Cert) (code : ByteArray) (call : SolarTV.Call) (items : List Item)
    (k R pc : Nat) (S : List Word) (s : SolarTV.Machine.State) (M : ByteArray) (g : Nat) : Prop where
  seg : Seg (bytesOf code) c.offset pc items code.size
  stack : S.length + k ≤ 1000
  gas : 22100 * (k + R) + (memoryGasCost c.top - memoryGasCost M.size) ≤ g
  le_top : M.size ≤ c.top
  mem : MemRel s.memory M

/-- At a block's entry, with gas for `R` more items. -/
structure EntryL (c : Cert) (code : ByteArray) (call : SolarTV.Call) (items : List Item)
    (R pc : Nat) (s : SolarTV.Machine.State) (M : ByteArray) (g : Nat) : Prop where
  seg : Seg (bytesOf code) c.offset pc items code.size
  gas : 22100 * R + (memoryGasCost c.top - memoryGasCost M.size) ≤ g
  le_top : M.size ≤ c.top
  mem : MemRel s.memory M

theorem InvL.next {c : Cert} {code : ByteArray} {call : SolarTV.Call} {item : Item}
    {items : List Item} {k R pc next : Nat} {S S' : List Word} {s : SolarTV.Machine.State}
    {M : ByteArray} {g g' : Nat} (I : InvL c code call (item :: items) k R pc S s M g) (hk : 1 ≤ k)
    (hseg : Seg (bytesOf code) c.offset next items code.size) (hS : S'.length ≤ S.length + 1)
    (hg : g ≤ g' + 22100) : InvL c code call items (k - 1) R next S' s M g' where
  seg := hseg
  stack := by have := I.stack; omega
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

theorem InvL.next2 {c : Cert} {code : ByteArray} {call : SolarTV.Call} {i1 i2 : Item}
    {items : List Item} {k R pc next : Nat} {S S' : List Word} {s : SolarTV.Machine.State}
    {M : ByteArray} {g g' : Nat} (I : InvL c code call (i1 :: i2 :: items) k R pc S s M g)
    (hk : 2 ≤ k) (hseg : Seg (bytesOf code) c.offset next items code.size)
    (hS : S'.length ≤ S.length + 1) (hg : g ≤ g' + 44200) :
    InvL c code call items (k - 2) R next S' s M g' where
  seg := hseg
  stack := by have := I.stack; omega
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

/-- A block's end, falling into the next one: the entry invariant with the reserve. -/
theorem InvL.entry {c : Cert} {code : ByteArray} {call : SolarTV.Call} {items : List Item}
    {k R pc : Nat} {S : List Word} {s : SolarTV.Machine.State} {M : ByteArray} {g : Nat}
    (I : InvL c code call items k R pc S s M g) : EntryL c code call items R pc s M g where
  seg := I.seg
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

/-- A jump's target block, at its offset, from the invariant before the `m` items of the jump. -/
theorem InvL.target {p : Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobL p c mx code) {call : SolarTV.Call} {t m : Nat} {items : List Item} {k R pc : Nat}
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

/-! ## EthLib's rules over steps monotone in gas -/

section Rules

variable {code : ByteArray} {msg : Message .fusaka} {pc gas : Nat} {M : ByteArray}
  {st : State.TransactionState} {ss : Substate}

/-- PUSH of a decoded constant, PUSH0 or PUSHn. -/
theorem push_itemG {v next : Nat} {stack : List Word}
    (h : decode (bytesOf code) pc = some (.push v, next)) (hgas : 3 ≤ gas)
    (hstack : stack.length < 1024) :
    ∃ g, gas - 3 ≤ g ∧ HoareG .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg next (BitVec.ofNat 256 v :: stack) M g st ss .empty) := by
  obtain ⟨byte, hb, h⟩ := decode_push h
  obtain ⟨hlt, hcode⟩ := getElem?_bytesOf hb
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨h1, h2, rfl, hle, rfl⟩
  · exact ⟨gas - 2, by omega,
      (SolidCore.Refinement.Evm.Logic.push0GA (by decide) hlt hcode (by omega) hstack).toG⟩
  · have hn : byte - PUSH1 < 32 := by unfold PUSH1 PUSH32 at *; omega
    have hdec := decode_pushByte ⟨byte - PUSH1, hn⟩
    have hbyte : 0x60 + (byte - PUSH1) = byte := by unfold PUSH1 at *; omega
    simp only [hbyte] at hdec
    refine ⟨gas - 3, le_refl _, ?_⟩
    have hle' : pc + 1 + (byte - PUSH1 + 1) ≤ code.size := by rw [← length_bytesOf]; exact hle
    have := push_of_decodeG (fork := .fusaka) (message := msg) (memory := M) (state := st)
      (substate := ss) (returnData := .empty) hlt hcode hdec (by simp)
      (pushData_eq hle') hgas hstack
    simpa [Nat.add_assoc] using this

set_option hygiene false in
/-- A two-operand stack operation. -/
local macro "bin_ruleG" agree:term : tactic => `(tactic| (
  rcases stack with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, le_refl _, ?_⟩
  rw [← $agree x y]
  exact binaryG hlt hcode rfl (instr_stack _ _ rfl) (Nat.le_trans (m := 3) (by decide) hgas)))

set_option hygiene false in
/-- A one-operand stack operation. -/
local macro "un_ruleG" agree:term : tactic => `(tactic| (
  rcases stack with _ | ⟨x, rest⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, le_refl _, ?_⟩
  rw [← $agree x]
  exact unaryG hlt hcode rfl (instr_stack _ _ rfl) (Nat.le_trans (m := 3) (by decide) hgas)))

/-- ADDRESS pushes the word of the callee, `SolarTV.environment.callee`. -/
theorem address_word : (Target.address selfAddress).toU256 =
    BitVec.ofNat 256 SolarTV.environment.callee := by
  decide +kernel

/-- An environment read of the fragment pushes the word `envRead` gives, for 2 gas, from
EthLib's environment of `Target`'s calls. -/
theorem env_readG {name : String} {byte w : Nat} {stack : List Word}
    (he : envRead name = some (byte, w)) (hlt : pc < code.size)
    (hcode : code[pc] = UInt8.ofNat byte) (hblock : msg.blockEnv = Target.blockEnv)
    (htx : msg.txEnv = Target.txEnv) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg (pc + 1) (BitVec.ofNat 256 w :: stack) M (gas - 2) st ss .empty) := by
  unfold envRead at he
  split at he <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at he <;>
    obtain ⟨rfl, rfl⟩ := he
  · exact (push_of_readFrameGA (op := .origin) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, htx]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .gasprice) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, htx]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .coinbase) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, hblock]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .timestamp) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, hblock]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .number) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, hblock]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .gaslimit) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, hblock]; decide +kernel) hgas hstack).toG
  · exact (push_of_readFrameGA (op := .chainid) hlt hcode (ofByte_of_decode rfl (by decide)) rfl
      (fun _ _ hm _ _ => by rw [hm, hblock]; decide +kernel) hgas hstack).toG

/-- `Assemble.stack_rule_cheap` over steps monotone in gas. -/
theorem stack_rule_cheapG {op : SolarTV.EVM.Op} {byte : Nat} {stack next : List Word}
    {r : Word} (hm : low op = false) (hb : opByte op = some byte) (hlt : pc < code.size)
    (hcode : code[pc] = UInt8.ofNat byte)
    (hstep : SolarTV.EVM.step ⟨BitVec.ofNat 256 msg.data.size, r⟩ op stack = some next)
    (hgas : 3 ≤ gas) (hlen : stack.length < 1024) :
    ∃ g, gas - 3 ≤ g ∧ HoareG .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg (pc + 1) next M g st ss .empty) := by
  cases op <;> simp only [opByte, reduceCtorEq, Option.some.injEq] at hb <;> try subst hb
  case mod | mul | div => simp [low] at hm
  case add => bin_ruleG add_agree
  case sub => bin_ruleG sub_agree
  case lt => bin_ruleG lt_agree
  case gt => bin_ruleG gt_agree
  case slt => bin_ruleG slt_agree
  case sgt => bin_ruleG sgt_agree
  case eq => bin_ruleG eq_agree
  case and => bin_ruleG and_agree
  case or => bin_ruleG or_agree
  case xor => bin_ruleG xor_agree
  case byte => bin_ruleG byte_agree
  case shl => bin_ruleG shl_agree
  case shr => bin_ruleG shr_agree
  case iszero => un_ruleG iszero_agree
  case not => un_ruleG not_agree
  case pop =>
    rcases stack with _ | ⟨x, rest⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
      Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, by omega, popG hlt hcode (by omega)⟩
  case calldatasize =>
    simp only [SolarTV.EVM.step, Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, by omega, calldatasizeG hlt hcode (by omega) hlen⟩
  case dup i =>
    split at hb
    · rename_i hi
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [SolarTV.EVM.step, Option.map_eq_some_iff] at hstep
      obtain ⟨x, hx, rfl⟩ := hstep
      exact ⟨_, le_refl _, dupG (⟨i.val, hi⟩ : Fin 16) hlt hcode hx hgas hlen⟩
    · simp at hb
  case swap i =>
    split at hb
    · rename_i hi
      simp only [Option.some.injEq] at hb
      subst hb
      rcases stack with _ | ⟨top, rest⟩
      · simp [SolarTV.EVM.step] at hstep
      · simp only [SolarTV.EVM.step, Option.map_eq_some_iff] at hstep
        obtain ⟨x, hx, rfl⟩ := hstep
        exact ⟨_, le_refl _, swap_of_decodeG hlt hcode (decode_swap ⟨i.val, hi⟩) hx hgas⟩
    · simp at hb

/-- `Assemble.stack_rule` over steps monotone in gas. -/
theorem stack_ruleG {op : SolarTV.EVM.Op} {byte : Nat} {stack next : List Word}
    {r : Word} (hb : opByte op = some byte) (hlt : pc < code.size)
    (hcode : code[pc] = UInt8.ofNat byte)
    (hstep : SolarTV.EVM.step ⟨BitVec.ofNat 256 msg.data.size, r⟩ op stack = some next)
    (hgas : 5 ≤ gas) (hlen : stack.length < 1024) :
    ∃ g, gas - 5 ≤ g ∧ HoareG .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg (pc + 1) next M g st ss .empty) := by
  cases hm : low op
  · obtain ⟨g, hg, H⟩ := stack_rule_cheapG hm hb hlt hcode hstep (Nat.le_trans (by decide) hgas) hlen
    exact ⟨g, by omega, H⟩
  · cases op <;> simp [low] at hm <;> simp only [opByte, Option.some.injEq] at hb <;> subst hb <;>
      rcases stack with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
        Option.some.injEq] at hstep <;> subst hstep <;> refine ⟨_, le_refl _, ?_⟩
    all_goals first
      | (rw [← mul_agree x y]; exact binaryG hlt hcode rfl (instr_stack _ _ rfl) hgas)
      | (rw [← div_agree x y]; exact binaryG hlt hcode rfl (instr_stack _ _ rfl) hgas)
      | (rw [← mod_agree x y]; exact binaryG hlt hcode rfl (instr_stack _ _ rfl) hgas)

end Rules

end SolidCore.Refinement.Solar.AssembleLoop
