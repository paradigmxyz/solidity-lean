import SolidCore.Refinement.Solar.AssembleLoopWithin
import SolidCore.Refinement.Solar.AssembleGasLoop

/-!
# EVM IR to bytecode, for code with loops: constants known across blocks

`checkL` knows a constant on the stack only from the PUSH that put it there to the end of its
block, and forgets it at a SWAP and past a JUMPI. Memory at an offset the code keeps on the stack
from one block to the next (the free memory pointer an `abi.encode` copy loop reuses, say) is then
at an offset it does not know, and the code is outside its fragment. `checkK` is `checkL` with:

* each block entered with the constants a list `kn` of the certificate claims (`entryK`), every
  jump and fall checking that the constants it knows include them (`KLe`), and block 0 entered
  with none;
* SWAP exchanging what it knows of the two words (`kSwap`), ADD of two known words known
  (`kOp`), and a JUMPI that falls through keeping what it knows of the words under its condition.

Everything else is `checkL`'s, so memory is still accessed at constant offsets within the
certificate's bound `c.top`, the reach of every run: the gas bound is `gasBoundL`, memory's price
up to that bound beside 22100 per item. The theorems are `checkL`'s, proved the same way: the
forward direction from a gas bound on (`forward_of_checkK`, `stage_of_checkK_gas`) and every gas
(`within_of_checkK`). `checkL` itself is unchanged.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Constants across blocks -/

/-- The constants the certificate says block `t` is entered with (none past the list). -/
def entryK (kn : List Known) (t : Nat) : Known := kn.getD t []

/-- Every constant `k2` claims, `k1` claims at the same depth. -/
def KLe : Known → Known → Bool
  | _, [] => true
  | k1, none :: k2 => KLe k1.tail k2
  | k1, some v :: k2 => (kAt k1 0 == some v) && KLe k1.tail k2

theorem KR.tail' {k : Known} {S : List Word} (h : KR k S) : KR k.tail S.tail := by
  intro i v hv
  cases k with
  | nil => simp [kAt] at hv
  | cons j k =>
    cases S with
    | nil => simpa using h (i + 1) v (by simpa [kAt] using hv)
    | cons a S => simpa using h (i + 1) v (by simpa [kAt] using hv)

theorem KR.of_le : ∀ {k2 k1 : Known} {S : List Word}, KR k1 S → KLe k1 k2 = true → KR k2 S
  | [], _, S, _, _ => KR.nil S
  | none :: k2, k1, S, h, hle => by
    simp only [KLe] at hle
    have ih := KR.of_le h.tail' hle
    intro i v hv
    cases i with
    | zero => simp [kAt] at hv
    | succ i =>
      have := ih i v (by simpa [kAt] using hv)
      cases S with
      | nil => simp at this
      | cons a S => simpa using this
  | some w :: k2, k1, S, h, hle => by
    simp only [KLe, Bool.and_eq_true, beq_iff_eq] at hle
    have ih := KR.of_le h.tail' hle.2
    intro i v hv
    cases i with
    | zero =>
      have := h 0 w hle.1
      simp [kAt] at hv
      rw [← hv]
      exact this
    | succ i =>
      have := ih i v (by simpa [kAt] using hv)
      cases S with
      | nil => simp at this
      | cons a S => simpa using this

/-- What SWAP `i` leaves known: the two words exchanged. -/
def kSwap (known : Known) (i : Nat) : Known :=
  kAt known (i + 1) :: (List.range (max (known.length - 1) (i + 1))).map fun j =>
    if j = i then kAt known 0 else kAt known (j + 1)

theorem KR.swap {known : Known} {a : Word} {S : List Word} (h : KR known (a :: S)) {i : Nat}
    (hi : i < S.length) : KR (kSwap known i) (S[i] :: S.set i a) := by
  intro j v hv
  cases j with
  | zero =>
    simp only [kSwap, kAt, List.getElem?_cons_zero, Option.join_some] at hv
    have := h (i + 1) v (by simpa [kAt] using hv)
    simpa [List.getElem?_eq_getElem hi] using this
  | succ j =>
    simp only [kSwap, kAt, List.getElem?_cons_succ, List.getElem?_map] at hv
    by_cases hjm : j < max (known.length - 1) (i + 1)
    · rw [List.getElem?_range hjm] at hv
      simp only [Option.map_some, Option.join_some] at hv
      simp only [List.getElem?_cons_succ, List.getElem?_set]
      by_cases hj : j = i
      · subst hj
        simp only [ite_true] at hv
        have := h 0 v hv
        simp at this
        simp [hi, this]
      · simp only [hj, ite_false] at hv
        have := h (j + 1) v hv
        simp only [List.getElem?_cons_succ] at this
        simp [Ne.symm hj, this]
    · have hn : (List.range (max (known.length - 1) (i + 1)))[j]? = none := by
        rw [List.getElem?_eq_none_iff, List.length_range]
        omega
      rw [hn] at hv
      simp at hv

/-- What a stack operation leaves known on top: the sum of two known words for ADD. -/
def kOp : SolarTV.EVM.Op → Known → Option Word
  | .add, known =>
    match kAt known 0, kAt known 1 with
    | some x, some y => some (EvmRules.Evm.add x y)
    | _, _ => none
  | _, _ => none

theorem kOp_spec {op : SolarTV.EVM.Op} {known : Known} {S S' : List Word} {ctx : SolarTV.EVM.Context}
    {v x : Word} (h : KR known S) (hs : SolarTV.EVM.step ctx op S = some (v :: S'))
    (hk : kOp op known = some x) : x = v := by
  cases op <;> simp only [kOp, reduceCtorEq] at hk
  split at hk
  · rename_i a b ha hb
    simp only [Option.some.injEq] at hk
    subst hk
    have h0 := h 0 a ha
    have h1 := h 1 b hb
    rcases S with _ | ⟨a', _ | ⟨b', S⟩⟩
    · simp at h0
    · simp at h1
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1
    simp only [SolarTV.EVM.step, Option.some.injEq, List.cons.injEq] at hs
    exact hs.1
  · simp at hk

theorem KR.cons_opt {j : Option Word} {known : Known} {v : Word} {S : List Word} (h : KR known S)
    (hj : ∀ x, j = some x → x = v) : KR (j :: known) (v :: S) := by
  intro i w hw
  cases i with
  | zero =>
    simp only [kAt, List.getElem?_cons_zero, Option.join_some] at hw
    simp [hj w hw]
  | succ i => simpa using h i w (by simpa [kAt] using hw)

/-! ## The checker -/

/-- `jumpOkL`, and the constants the jump knows include its target's. -/
def jumpOkK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (b t h : Nat) (ty : List Ty)
    (known : Known) : Bool :=
  jumpOkL p c mx b t h ty && KLe known (entryK kn t)

/-- `fallOkL`, and the constants the fall knows include the next block's. -/
def fallOkK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (b h : Nat) (ty : List Ty)
    (known : Known) : Bool :=
  fallOkL p c mx b h ty && KLe known (entryK kn (b + 1))

/-- `blockStepL` with constants across blocks: SWAP and ADD keep what they know, a JUMPI that
falls through keeps what it knows below its condition, and every jump checks its target's
constants. -/
def blockStepK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (b : Nat)
    (ok : Nat → Known → List Ty → Nat → Bool) :
    Nat → Known → List Ty → Nat → Assemble.Instr → Bool
  | h, known, ty, k, .op (.stack op) =>
    match op with
    | .push v => decide (1 ≤ k) && ok (h + 1) (some v :: known) (some false :: ty) (k - 1)
    | .dup i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 1 ≤ h) &&
      ok (h + 1) (kAt known i.val :: known) (tyAt ty i.val :: ty) (k - 1)
    | .swap i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 2 ≤ h) &&
      ok h (kSwap known i.val) (tySwap ty i.val) (k - 1)
    | .pop => decide (1 ≤ k) && decide (1 ≤ h) && ok (h - 1) [] ty.tail (k - 1)
    | op =>
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat (kOp op known :: known.drop need) (some false :: ty.drop need) (k - 1)
      | none => false
  | h, known, ty, k, .op .store =>
    match known with
    | some o :: _ => decide (1 ≤ k) && decide (2 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 2 &&
      ok (h - 2) (known.drop 2) (ty.drop 2) (k - 1)
    | _ => false
  | h, known, ty, k, .op .load =>
    match known with
    | some o :: _ => decide (1 ≤ k) && decide (1 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 1 &&
      ok h (none :: known.drop 1) (some false :: ty.drop 1) (k - 1)
    | _ => false
  | h, _, ty, k, .effect .callvalue 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .calldatasize 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, known, ty, k, .effect .caller 0 =>
    c.env && decide (1 ≤ k) && ok (h + 1) (none :: known) (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .address 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect (.env name) 0 =>
    c.reads && (envRead name).isSome && decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, known, ty, k, .effect .calldataload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h (none :: known.drop 1) (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h [] (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sstore 2 => decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 &&
    ok (h - 2) [] (ty.drop 2) (k - 1)
  | h, known, ty, k, .effect .keccak256 2 =>
    match known with
    | some o :: some s :: _ => c.env && decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 && rangeOk c o s &&
      decide (keccak256Cost s ≤ 22100) && ok (h - 1) [] (some false :: ty.drop 2) (k - 1)
    | _ => false
  | h, known, ty, k, .effect (.log n) a =>
    match known with
    | some o :: some s :: _ => decide (n ≤ 4) && decide (a = n + 2) && decide (1 ≤ k) && decide (n + 2 ≤ h) &&
      isData ty (n + 2) && rangeOk c o s && decide (logCost n s ≤ 22100) &&
      ok (h - (n + 2)) [] (ty.drop (n + 2)) (k - 1)
    | _ => false
  | h, known, ty, k, .jump t => decide (2 ≤ k) && jumpOkK p c mx kn b t h ty known
  | h, known, ty, k, .jumpi t =>
    decide (2 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkK p c mx kn b t (h - 1) ty.tail (known.drop 1) &&
      ok (h - 1) (known.drop 1) ty.tail (k - 2)
  | h, _, ty, k, .pushLabel t =>
    decide (1 ≤ k) && c.rets.contains t && decide (t < 2 ^ 32) && ok (h + 1) [] (some true :: ty) (k - 1)
  | h, known, ty, k, .jumpDyn =>
    decide (1 ≤ k) && decide (1 ≤ h) && tyAt ty 0 == some true &&
      c.rets.all fun t => jumpOkK p c mx kn b t (h - 1) ty.tail (known.drop 1)
  | h, known, ty, k, .jumpiDyn =>
    decide (1 ≤ k) && decide (2 ≤ h) && tyAt ty 0 == some true && isData ty.tail 1 &&
      (c.rets.all fun t => jumpOkK p c mx kn b t (h - 2) ty.tail.tail (known.drop 2)) &&
      ok (h - 2) [] ty.tail.tail (k - 1)
  | _, _, _, _, .stop => true
  | _, known, ty, _, .ret | _, known, ty, _, .revert =>
    match known with
    | some o :: some s :: _ => isData ty 2 && rangeOk c o s
    | _ => false
  | _, _, _, _, _ => false

/-- `blockOkL` for `blockStepK`. -/
def blockOkK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (b : Nat) :
    Nat → Known → List Ty → Nat → List Assemble.Instr → Bool
  | h, known, ty, _, [] => fallOkK p c mx kn b h ty known
  | h, known, ty, k, i :: rest =>
    match turnedElse c b i rest with
    | some e =>
      decide (3 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
        jumpOkK p c mx kn b e (h - 1) ty.tail (known.drop 1) &&
        fallOkK p c mx kn b (h - 1) ty.tail (known.drop 1)
    | none =>
      if dropped p b i rest then
        match i with
        | .stop => true
        | _ => fallOkK p c mx kn b h ty known
      else blockStepK p c mx kn b (fun h known ty k => blockOkK p c mx kn b h known ty k rest) h known ty k i

/-- Every block checks from its entry constants as `blocksOkL` checks it from none. -/
def blocksOkK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) :
    Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
      decide (maxH mx b + budget c b ≤ 1000) &&
      blockOkK p c mx kn b (c.need b) (entryK kn b) (c.entry b) (budget c b - labelItems p c b) instrs &&
      blocksOkK p c mx kn (b + 1) rest

/-- **The checker for code with loops and constants known across blocks.** -/
def checkK (p : Program) (code : ByteArray) (c : Cert) (mx : List Nat) (kn : List Known) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkK p c mx kn 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32) && KLe [] (entryK kn 0)

theorem blocksOkK_get {p : Program} {c : Cert} {mx : List Nat} {kn : List Known} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat),
    blocksOkK p c mx kn b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ budget c (b + k) ∧ c.need (b + k) ≤ maxH mx (b + k) ∧
      maxH mx (b + k) + budget c (b + k) ≤ 1000 ∧
      blockOkK p c mx kn (b + k) (c.need (b + k)) (entryK kn (b + k)) (c.entry (b + k))
        (budget c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOkK, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [and_assoc] using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOkK, Bool.and_eq_true] at h
    have := blocksOkK_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the check the simulation uses at every block. -/
structure GlobK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 32
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ budget c t ∧
    c.need t ≤ maxH mx t ∧ maxH mx t + budget c t ≤ 1000 ∧
    blockOkK p c mx kn t (c.need t) (entryK kn t) (c.entry t) (budget c t - labelItems p c t) p.blocks[t] = true

theorem GlobK.toT {p : Program} {c : Cert} {mx : List Nat} {kn : List Known} {code : ByteArray}
    (G : GlobK p c mx kn code) : GlobLT p c code :=
  ⟨G.top_mod, G.top_le, G.size_lt, G.target⟩

theorem globK_of_checkK {p : Program} {code : ByteArray} {c : Cert} {mx : List Nat} {kn : List Known}
    (h : checkK p code c mx kn = true) :
    GlobK p c mx kn code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 ∧
      KLe [] (entryK kn 0) = true := by
  simp only [checkK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, htop⟩, hsize⟩, hk0⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨hmod, htop, hsize, fun t ht htgt => ?_, fun t ht => ?_⟩, hseg, hneed, hk0⟩
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
  · have := blocksOkK_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## The simulation of a block -/

set_option hygiene false in
/-- The bound of the stack in lockstep with the height of the check. -/
local macro "hu_tac" : tactic => `(tactic| first | omega | (simp at hu ⊢; omega) | (simp; omega))

/-- What a block's instructions from `pc` give: a halt EthLib's frame shows, or the next block,
reached by EthLib with its stack related at the block's types, at most its highest entry stack,
with gas for the reserve `R`, and by a jump to a labelled block or a fall into the next one. -/
def SimOutK (p : Program) (c : Cert) (mx : List Nat) (kn : List Known) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState) (ss : Substate)
    (b R pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧
      (t < p.blocks.length → c.need t ≤ S'.length ∧ S'.length ≤ maxH mx t) ∧
      (t = b + 1 ∨ isTarget p c t = true)) ∧
      ∃ pc' T' M' g' st' ss', HoareG .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧ KR (entryK kn t) S' ∧
        EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R pc' s' M' g' ∧
        Rel msg ss0 st' ss' s'

theorem SimOutK.pre {p : Program} {c : Cert} {mx : List Nat} {kn : List Known} {code : ByteArray} {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutK p c mx kn code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 r) :
    SimOutK p c mx kn code call msg ss0 st ss b R pc T M g r := by
  match r, h1 with
  | .inl (_, _), hspec => exact SpecG.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hkr, hinv, hrel⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hkr, hinv, hrel⟩

theorem blockStepK_stack {p : Program} {c : Cert} {mx : List Nat} {kn : List Known} {bb : Nat} {ok : Nat → Known → List Ty → Nat → Bool}
    {h k : Nat} {known : Known} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    (hd : ∀ i, op ≠ .dup i) (hs : ∀ i, op ≠ .swap i) (hp : op ≠ .pop) :
    blockStepK p c mx kn bb ok h known ty k (.op (.stack op)) =
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat (kOp op known :: known.drop need) (some false :: ty.drop need) (k - 1)
      | none => false := by
  cases op <;> first | rfl | exact absurd rfl (hne _) | exact absurd rfl (hd _) |
    exact absurd rfl (hs _) | exact absurd rfl hp


/-- `stack_sim` for `blockStepK`, with the heights of the check and the stack in lockstep. -/
theorem stack_simK {p : Program} {c : Cert} {mx : List Nat} {kn : List Known} {bb : Nat} {ok : Nat → Known → List Ty → Nat → Bool}
    {h k : Nat} {known : Known} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    {ctx : SolarTV.EVM.Context} {S T : List Word}
    (hok : blockStepK p c mx kn bb ok h known ty k (.op (.stack op)) = true) (hh : h ≤ S.length)
    (hk : KR known S) (hR : SR c ty S T) :
    1 ≤ k ∧ ∃ byte, opByte op = some byte ∧ ∃ h' ty' S' T',
      SolarTV.EVM.step ctx op S = some S' ∧ SolarTV.EVM.step ctx op T = some T' ∧
      SR c ty' S' T' ∧ h' ≤ S'.length ∧ S'.length ≤ S.length + 1 ∧ S'.length + h = h' + S.length ∧
      ∃ known', KR known' S' ∧ ok h' known' ty' (k - 1) = true := by
  have hL := hR.length
  by_cases hd : ∃ i, op = .dup i
  · obtain ⟨i, rfl⟩ := hd
    simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x80 + i.val, by simp [opByte, h16], h + 1, _, _, _, ?_, ?_, SR.dup hR hiS hiT, by simp; omega, by simp, by simp; omega, _,
      hk.dup hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hs : ∃ i, op = .swap i
  · obtain ⟨i, rfl⟩ := hs
    simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    simp only [List.length_cons] at hh hL
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x90 + i.val, by simp [opByte, h16], h, _, _, _, ?_, ?_, SR.swap hR hiS hiT, by simp; omega, by simp, by simp; omega, _,
      hk.swap hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hp : op = .pop
  · subst hp
    simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, h1⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    refine ⟨hk1, _, rfl, h - 1, _, _, _, rfl, rfl, (SR.uncons.1 hR).2, by simp at hh; omega,
      by simp only [List.length_cons]; omega, by simp at hh ⊢; omega, [], KR.nil _, hok⟩
  have hd' : ∀ i, op ≠ .dup i := fun i e => hd ⟨i, e⟩
  have hs' : ∀ i, op ≠ .swap i := fun i e => hs ⟨i, e⟩
  rw [blockStepK_stack hne hd' hs' hp] at hok
  split at hok
  · rename_i need d hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, hneed⟩, hdata⟩, hok⟩ := hok
    obtain ⟨byte, hbyte⟩ := opByte_of_stackNeed hn
    have hS' : ∃ S', SolarTV.EVM.step ctx op S = some S' := by
      cases op <;> simp only [stackNeed, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hn
      all_goals try first
        | exact absurd rfl (hd' _)
        | exact absurd rfl (hs' _)
        | exact absurd rfl hp
      all_goals obtain ⟨rfl, -⟩ := hn
      all_goals rcases S with _ | ⟨a, _ | ⟨b, S⟩⟩ <;> simp_all [SolarTV.EVM.step] <;> omega
    obtain ⟨S', hstep⟩ := hS'
    obtain ⟨v, rfl, hstepT⟩ := step_data hn hd' hs' hp hstep (hR.data hdata) hL
    have hd1 : (need : Int) + d = 1 := by
      cases op <;> simp [stackNeed] at hn <;>
        first | omega | exact absurd rfl (hd' _) | exact absurd rfl (hs' _) | exact absurd rfl hp
    refine ⟨hk1, byte, hbyte, (h + d).toNat, _, _, _, hstep, hstepT,
      SR.cons (τ := some false) rfl (SR.drop need hR), ?_, ?_, ?_, _, (hk.drop need).cons_opt (fun x hx => kOp_spec hk hstep hx), hok⟩
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
  · cases hok


/-- An opcode item at the head of a walk: its byte at the counter, and the walk on from the next
byte. -/
private theorem op_seg {code : ByteArray} {offset : Nat → Nat} {pc e byte : Nat} {items : List Item}
    (h : Seg (bytesOf code) offset pc (.op byte :: items) e) :
    ∃ _ : pc < code.size, code[pc] = UInt8.ofNat byte ∧
      Seg (bytesOf code) offset (pc + 1) items e := by
  obtain ⟨next, hd, hseg⟩ := h.head
  obtain ⟨hlt, hcode, rfl⟩ := op_item hd
  exact ⟨hlt, hcode, hseg⟩

/-- A data word on top of SolarTV's stack is the word on top of EthLib's. -/
private theorem sr_data1 {c : Cert} {ty : List Ty} {S T : List Word} (hR : SR c ty S T)
    (hd : isData ty 1 = true) (hS : 1 ≤ S.length) :
    ∃ x S' T', S = x :: S' ∧ T = x :: T' ∧ SR c ty.tail S' T' := by
  have hL := hR.length
  rcases S with _ | ⟨x, S'⟩ <;> rcases T with _ | ⟨y, T'⟩ <;> simp at hS hL
  obtain rfl := (SR.head hR hd).symm
  exact ⟨x, S', T', rfl, rfl, (SR.uncons.1 hR).2⟩

/-- Two data words on top of SolarTV's stack are the words on top of EthLib's. -/
private theorem sr_data2 {c : Cert} {ty : List Ty} {S T : List Word} (hR : SR c ty S T)
    (hd : isData ty 2 = true) (hS : 2 ≤ S.length) :
    ∃ x y S' T', S = x :: y :: S' ∧ T = x :: y :: T' ∧ SR c (ty.drop 2) S' T' := by
  have hL := hR.length
  rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩ <;> rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩ <;> simp at hS hL
  have htake := hR.data hd
  simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
  obtain ⟨rfl, rfl, -⟩ := htake
  exact ⟨x, y, S', T', rfl, rfl, by simpa using SR.drop 2 hR⟩

/-- A stack with a known second word has at least two. -/
private theorem KR.two_le {j : Option Word} {o : Word} {known : Known} {S : List Word}
    (h : KR (j :: some o :: known) S) : 2 ≤ S.length := by
  obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 (h 1 o (by simp [kAt]))
  omega

open SolarTV.EVM.Program in
/-- EthLib runs the code of a block's instructions from the offset of the next one as SolarTV
runs them, over steps monotone in gas, with gas for the reserve `R` beyond the block, for a
message from any account `a` (CALLER is `a`; the transaction's environment is `Target.txEnv`'s
only when the block reads it). -/
theorem exec_simK {p : Assemble.Program} {c : Cert} {mx : List Nat} {kn : List Known} {code : ByteArray} (G : GlobLT p c code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    {a : Nat} (hcaller : msg.caller = Target.address a) (ho : c.env = true → OracleOkAt a o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : c.reads = true → msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (b : Nat) (hb : b < p.blocks.length) (Rv : Nat) :
    ∀ (is : List Assemble.Instr) (h : Nat) (known : Known) (ty : List Ty) (S T : List Word) (k : Nat)
      (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate),
      blockOkK p c mx kn b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S T →
      InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k Rv
        pc S s M g → Rel msg ss0 st ss s →
      SimOutK p c mx kn code call msg ss0 st ss b Rv pc T M g (exec o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R => by
    simp only [blockOkK, fallOkK, fallOkL, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hok, hkl⟩ := hok
    have I2 := I.entry
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [exec, SimOutK]
    exact ⟨⟨by omega, fun ht => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
      Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, KR.of_le hk hkl, I2, R⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOkK, hT, jumpOkK, jumpOkL, fallOkK, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, hkj⟩, ⟨⟨hfall, hfty⟩, hcost'⟩, hkf⟩ := hok
      simp only [lowerInstrs, hT, List.cons_append, List.nil_append] at I
      obtain ⟨cond, S', T', rfl, rfl, hR'⟩ := sr_data1 hR hdat (by omega)
      obtain ⟨hlt0, hcode0, hs0⟩ := op_seg I.seg
      obtain ⟨n1, hd1, hs1⟩ := hs0.head
      obtain ⟨hlt2, hcode2, hseg⟩ := op_seg hs1
      simp only [Item.expected] at hd1
      have hS := I.stack; have hG := I.gas
      simp only [List.length_cons] at hS hh hu hL
      obtain ⟨g0, hg0, hisz⟩ := stack_ruleG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
        (op := .iszero) (stack := cond :: T') (next := EvmRules.Evm.iszero cond :: T')
        (r := o.env "returndatasize" s.world []) rfl hlt0 hcode0 rfl (by omega)
        (by simp only [List.length_cons]; omega)
      obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss)
        (gas := g0) (stack := EvmRules.Evm.iszero cond :: T') hd1 (by omega)
        (by simp only [List.length_cons]; omega)
      by_cases hc : cond = 0
      · -- The condition is zero: ISZERO gives one and the code jumps to the else block.
        subst hc
        have hoff := toNat_offset (G.target e hen hetgt).2.1 G.size_lt
        have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) iszero_zero
          (by rw [hoff]; exact (G.target e hen hetgt).1)
        rw [hoff] at hj
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega,
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOutK]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr hetgt⟩, c.offset e, T', M, g1 - 10, st,
          ss, Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR',
          KR.of_le (by simpa using hk.drop 1) hkj,
          I.target G hen hetgt (m := 3) (by omega) (by omega), R⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOutK]
        refine ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR',
          KR.of_le (by simpa using hk.drop 1) hkf,
          ⟨hseg, ?_, I.le_top, I.mem⟩, R⟩
        have := I.gas
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOkK, hT, hD, ite_true, fallOkK, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          obtain ⟨hok, hkl⟩ := hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutK]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
            Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, KR.of_le hk hkl, I.entry, R⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [exec, SimOutK]
          exact SpecG.consequence (stop_of_size_leG (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      have hok' : blockStepK p c mx kn b (fun h known ty k => blockOkK p c mx kn b h known ty k rest) h known ty k i =
          true := by
        simpa only [blockOkK, hT, hD', Bool.false_eq_true, ite_false] using hok
      have I' : InvL c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      clear hok hD hD' hT
      have IH := exec_simK (mx := mx) (kn := kn) (o := o) (ss0 := ss0) G hdata hvalue hstatic hself hcaller ho hbenv htx he b hb Rv rest
      -- An effect that pushes one word on both stacks for 2 gas and keeps the rest.
      have push2 : ∀ {e : SolarTV.Machine.Effect} {byte : Nat} {w : Word} {known' : Known},
          SolarTV.Machine.Effect.apply o call e [] s = some (some w, s) → KR known' (w :: S) →
          InvL c code call (.op byte :: (lowerInstrs p c b rest ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g → 1 ≤ k →
          blockOkK p c mx kn b (h + 1) known' (some false :: ty) (k - 1) rest = true →
          (∀ hlt : pc < code.size, code[pc] = UInt8.ofNat byte → 2 ≤ g → T.length < STACK_LIMIT →
            HoareG .fusaka (At code msg pc T M g st ss .empty)
              (At code msg (pc + 1) (w :: T) M (g - 2) st ss .empty)) →
          SimOutK p c mx kn code call msg ss0 st ss b Rv pc T M g
            (exec o call b (.effect e 0 :: rest) S s) := by
        intro e byte w known' happ hkn I' hk1 hok hrule
        obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        rw [exec_effect0 happ (by omega)]
        exact SimOutK.pre (hrule hlt hcode (by omega) (by unfold STACK_LIMIT; omega))
          (IH (h + 1) known' _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok (by simp; omega)
            (by hu_tac) hkn (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      -- The check refuses the instructions outside the fragment.
      all_goals try (simp [blockStepK] at hok'; done)
      · rcases mop with sop | _ | _ | _ | _ | _ | _ <;> try (simp [blockStepK] at hok'; done)
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [exec_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOutK.pre hpush (IH (h + 1) (some v :: known) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega) (by hu_tac)
              (hk.cons_some v)
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R)
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', hlock, known', hkn,
              hok⟩ := stack_simK (ctx := context o call s) hne hok' hh hk hR
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_ruleG (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            rw [exec_stack hstep (by omega) (by omega)]
            exact SimOutK.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega) (by hu_tac)
              hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R)
        · -- MLOAD.
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨hk1, h1⟩, hin⟩, hdat⟩, hok'⟩ := hok'
          obtain ⟨x, S', T', rfl, rfl, hR'⟩ := sr_data1 hR hdat (by omega)
          obtain ⟨rfl, -⟩ := KR.head hk
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := 32) hmod G.top_mod I'.le_top
            (Or.inr hin)
          have hbound : (32 : Word) = 0 ∨ ow.toNat + (32 : Word).toNat ≤ 2 ^ 32 :=
            Or.inr (by have := G.top_le; exact Nat.le_trans hin this)
          have hrule := Logic.mloadG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (start := ow) (rest := T') (gas := g) hlt hcode (by omega)
          rw [load_eq I'.mem] at hrule
          rw [exec_load (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, 32)]).expandBy
          refine SimOutK.pre hrule (IH h _ _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok' (by simp; omega)
            (by hu_tac) ((KR.head hk).2.cons_none _) (SR.cons (τ := some false) rfl (by simpa using hR'))
            ⟨hseg, by simp; omega, ?_, by rw [hM']; omega, memRel_expand I'.mem hbound⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- MSTORE.
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨hk1, h2⟩, hin⟩, hdat⟩, hok'⟩ := hok'
          obtain ⟨x, v, S', T', rfl, rfl, hR'⟩ := sr_data2 hR hdat (by omega)
          obtain ⟨rfl, -⟩ := KR.head hk
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := 32) hmod G.top_mod I'.le_top
            (Or.inr hin)
          obtain ⟨hmem', hsize⟩ := memRel_store (o := ow) (v := v) I'.mem (by have := G.top_le; omega)
          have hext := size_memoryExtend_extendMemory' (memory := M) (start := ow) (length := 32)
            hmod (by decide)
          rw [size_memoryExtend] at hext
          have h32 : (32 : U256).toNat = 32 := rfl
          rw [h32] at hext
          have hM' := hsize.trans hext.symm
          rw [exec_store (by omega)]
          refine SimOutK.pre (Logic.mstoreG (start := ow) (value := v) (rest := T') (memory := M)
            (gas := g) hlt hcode (by omega)) (IH (h - 2) _ _ S' T' (k - 1) _ (pc + 1) _ _ st ss hok'
            (by omega) (by hu_tac) (hk.drop 2) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega, hmem'⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
      · rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | name | _
        all_goals try (simp [blockStepK] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          obtain ⟨x, S', T', rfl, rfl, hR'⟩ := sr_data1 hR hdat (by omega)
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect1 (w := s.storage x) rfl (by omega)]
          have hrule := Logic.sloadG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (key := x) (rest := T') (gas := g) (by decide) hlt hcode rfl
            (by split <;> omega)
          rw [R.storage x] at hrule
          refine SimOutK.pre hrule ?_
          have hreads := fun k : Word => State.TransactionState.recordStorageRead_reads st
            msg.currentTarget msg.currentTarget (U256.toBeBytes x) (U256.toBeBytes k) default
          refine IH h [] _ _ _ (k - 1) s (pc + 1) M _ _ _ hok (by simp; omega) (by hu_tac) (KR.nil _)
            (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by split <;> omega))
            ⟨fun k => ?_, ?_, R.logs⟩
          · rw [(hreads k).2.1]
            exact R.storage k
          · rw [(hreads x).1]
            exact R.account
        · -- SSTORE.
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h2⟩, hdat⟩, hok⟩ := hok'
          obtain ⟨x, v, S', T', rfl, rfl, hR'⟩ := sr_data2 hR hdat (by omega)
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect2 (s' := { s with storage := SolarTV.Machine.update s.storage x v }) rfl
            (by omega)]
          have hcost := sstoreCost_le (st.getStorageOriginal msg.currentTarget (U256.toBeBytes x))
            (st.getStorage msg.currentTarget (U256.toBeBytes x)) v
            (decide (U256.toBeBytes x ∉ ss.accessedStorageKeys.getD msg.currentTarget ∅))
          obtain ⟨st', hnew, hothers, -, hacc, -, -, hrule⟩ := sstore_of_accountG
            (message := msg) (memory := M) (state := st) (substate := ss) (returnData := .empty)
            (key := x) (new := v) (rest := T') (gas := g) (by decide) (by decide) hlt hcode hstatic
            rfl (by simp only [CALL_STIPEND]; omega) (by omega) R.account
          refine SimOutK.pre hrule ?_
          refine IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) M _ _ _ hok (by omega) (by hu_tac) (KR.nil _)
            hR' ?_ ⟨fun k => ?_, by rw [hacc]; exact R.account, R.logs⟩
          · exact ⟨hseg, by omega, by omega, I'.le_top, I'.mem⟩
          by_cases hk : k = x
          · subst hk
            rw [hnew]
            simp [SolarTV.Machine.update]
          · rw [hothers _ _ (Or.inr fun he => hk (U256.toBeBytes_inj he)), R.storage k]
            simp [SolarTV.Machine.update, hk]
        · -- CALLDATALOAD.
          rcases ar with _ | _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          obtain ⟨x, S', T', rfl, rfl, hR'⟩ := sr_data1 hR hdat (by omega)
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect1 (w := SolarTV.Machine.calldataWord call x) rfl (by omega)]
          have hrule := Logic.calldataloadG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (start := x) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [hdata, ← calldataWord_eq] at hrule
          exact SimOutK.pre hrule (IH h _ _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega) (by hu_tac)
            ((hk.drop 1).cons_none _) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLDATASIZE.
          rcases ar with _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.calldata.size) rfl (KR.nil _) I' hok'.1 hok'.2
            fun hlt hcode hg hs => by rw [← hdata]; exact Logic.calldatasizeG hlt hcode hg hs
        · -- CALLVALUE.
          rcases ar with _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.callvalue) rfl (KR.nil _) I' hok'.1 hok'.2
            fun hlt hcode hg hs => by rw [← hvalue]; exact Logic.callvalueG hlt hcode hg hs
        · -- CALLER.
          rcases ar with _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          exact push2 (w := o.caller.setWidth 256) rfl (hk.cons_none _) I' hk1 hok
            fun hlt hcode hg hs => by
              rw [(ho henv).1, ← hcaller]; exact Logic.callerG hlt hcode hg hs
        · -- ADDRESS.
          rcases ar with _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 SolarTV.environment.callee) rfl (KR.nil _) I' hok'.1
            hok'.2 fun hlt hcode hg hs => by
              rw [← address_word, ← hself]; exact Logic.addressG hlt hcode hg hs
        · -- LOGn.
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨hn4, rfl⟩, hk1⟩, hnh⟩, hdat⟩, hin⟩, hlc⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨y, S1⟩⟩
          · exact hk.not_nil.elim
          · exact hk.not_one.elim
          obtain ⟨rfl, hk'⟩ := KR.head hk
          obtain ⟨rfl, -⟩ := KR.head hk'
          rcases T with _ | ⟨x', _ | ⟨y', T1⟩⟩
          · simp at hL
          · simp at hL
          simp only [List.length_cons] at hh hL hu
          obtain ⟨tops, S2, rfl, hlen⟩ : ∃ tops S2, S1 = tops ++ S2 ∧ tops.length = n :=
            ⟨S1.take n, S1.drop n, (List.take_append_drop n S1).symm, by simp; omega⟩
          obtain ⟨tops', T2, rfl, hlen'⟩ : ∃ tops' T2, T1 = tops' ++ T2 ∧ tops'.length = n :=
            ⟨T1.take n, T1.drop n, (List.take_append_drop n T1).symm, by simp; omega⟩
          subst hlen
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.cons.injEq, List.take_left' hlen',
            List.take_left' rfl] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          have hR' : SR c (ty.drop (tops.length + 2)) S2 T2 := by
            simpa using SR.drop (tops.length + 2) hR
          simp only [lowerInstr, hn4, ite_true, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons, List.length_append] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          have hrule := Logic.logG (n := ⟨tops.length, by omega⟩) (message := msg) (memory := M)
            (state := st) (substate := ss) (returnData := .empty) (start := ow) (size := sw)
            (words := tops) (rest := T2) (gas := g) rfl hlt hcode (decode_log ⟨tops.length, by omega⟩) hstatic
            (show logCost tops.length sw + (extendMemory M.size [(ow, sw)]).cost ≤ g by omega)
          dsimp only at hrule
          rw [exec_log (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          obtain ⟨L, hL1, hL2⟩ := R.logs
          refine SimOutK.pre hrule (IH (h - (tops.length + 2)) [] _ S2 T2 (k - 1) _ (pc + 1) _ _ st _
            hok (by omega) (by hu_tac) (KR.nil _) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega,
            memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, ?_⟩)
          · rw [hM']; omega
          · refine ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy)
                ow.toNat sw.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, ?_⟩⟩
            exact read_eq I'.mem
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepK] at hok'; done)
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨henv, hk1⟩, h2⟩, hdat⟩, hin⟩, hkc⟩, hok⟩ := hok'
          obtain ⟨x, y, S', T', rfl, rfl, hR'⟩ := sr_data2 hR hdat hk.two_le
          obtain ⟨rfl, hk'⟩ := KR.head hk
          obtain ⟨rfl, -⟩ := KR.head hk'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          obtain ⟨-, hkec⟩ := ho henv
          have hrule := Logic.keccak256G (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (start := ow) (size := sw) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hrule
          rw [exec_keccak (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          refine SimOutK.pre hrule (IH (h - 1) [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok
            (by simp; omega) (by hu_tac) (KR.nil _) (SR.cons (τ := some false) rfl hR') ⟨hseg, by simp; omega, ?_,
            by rw [hM']; omega, memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- An environment read of the block or the transaction.
          rcases ar with _ | ar <;> try (simp [blockStepK] at hok'; done)
          simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hreads, hsome⟩, hk1⟩, hok⟩ := hok'
          obtain ⟨⟨byte, w⟩, hread⟩ := Option.isSome_iff_exists.1 hsome
          simp only [lowerInstr, hread, Option.map_some, Option.getD_some,
            List.singleton_append] at I'
          exact push2 (w := BitVec.ofNat 256 w)
            (by simp [SolarTV.Machine.Effect.apply, he hreads name byte w hread]) (KR.nil _) I' hk1 hok
            fun hlt hcode hg hs => env_readG hread hlt hcode hbenv (htx hreads) hg hs
      · -- JUMP.
        simp only [blockStepK, jumpOkK, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hk2, ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hkj⟩⟩ := hok'
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨hlt2, hcode2, -⟩ := op_seg hs1
        simp only [Item.expected] at hd1
        have hS := I'.stack; have hG := I'.gas
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd1 (by omega) (by omega)
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (rest := T) hlt2 hcode2 (show 8 ≤ g1 by omega)
          (by rw [hoff]; exact (G.target t htn htgt).1)
        rw [hoff] at hj
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutK]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T, M, g1 - 8, st, ss,
          Triple.seq hpush hj, SR.le hty hR, KR.of_le hk hkj,
          I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- JUMPI.
        simp only [blockStepK, jumpOkK, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hkj⟩⟩, hok'⟩ := hok'
        obtain ⟨cond, S', T', rfl, rfl, hR'⟩ := sr_data1 hR hdat (by omega)
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨hlt2, hcode2, hseg⟩ := op_seg hs1
        simp only [Item.expected] at hd1
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := cond :: T') hd1 (by omega) (by simp; omega)
        by_cases hc : cond = 0
        · subst hc
          have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) rfl
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            ite_true]
          exact SimOutK.pre (Triple.seq hpush hj) (IH (h - 1) (known.drop 1) _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (by hu_tac) (by simpa using hk.drop 1) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R)
        · have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOutK]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T', M, g1 - 10, st,
            ss, Triple.seq hpush hj, SR.le hty hR', KR.of_le (by simpa using hk.drop 1) hkj,
            I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- A pushed return label: a PUSH of the block's offset.
        simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨hk1, hmem⟩, ht32⟩, hok⟩ := hok'
        have hmem' : t ∈ c.rets := by simpa using hmem
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, hseg⟩ := I'.seg.head
        simp only [Item.expected] at hd
        have hS := I'.stack; have hG := I'.gas
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd (by omega) (by omega)
        have htn : (BitVec.ofNat 256 t).toNat = t := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false]
        exact SimOutK.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega) (by hu_tac)
          (KR.nil _) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R)
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
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
        simp only [jumpOkK, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hkj⟩ := hj'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
          hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
        rw [hoff] at hj
        simp only [exec, SimOutK]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st,
          ss, hj, SR.le hty hR', KR.of_le (by simpa using hk.drop 1) hkj,
          I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
      · -- A conditional dynamic jump to a return label (the label on top, the condition below):
        -- a JUMPI to the label's offset, or on to the next item.
        simp only [blockStepK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          List.all_eq_true] at hok'
        obtain ⟨⟨⟨⟨⟨hk1, h2⟩, hlab⟩, hdat⟩, hall⟩, hok⟩ := hok'
        rcases S with _ | ⟨x, S1⟩
        · simp at hh; omega
        rcases T with _ | ⟨y, T1⟩
        · simp at hL
        obtain ⟨hw, hR1⟩ := SR.uncons.1 hR
        rw [hlab] at hw
        obtain ⟨hmem, rfl⟩ := hw
        obtain ⟨cond, S', T', rfl, rfl, hR'⟩ := sr_data1 hR1 hdat (by simp at hh; omega)
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        by_cases hc : cond = 0
        · subst hc
          have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty)
            (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T') hlt hcode
            (show 10 ≤ g by omega) rfl
          simp only [exec, ↓reduceIte]
          exact SimOutK.pre hj (IH (h - 2) [] _ S' T' (k - 1) s (pc + 1) M (g - 10) st ss hok
            (by omega) (by hu_tac) (KR.nil _) hR' (I'.next hk1 hseg (by simp; omega) (by omega)) R)
        · have hj' := hall _ hmem
          simp only [jumpOkK, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hj'
          obtain ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hkj⟩ := hj'
          have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
          have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty)
            (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T') hlt hcode
            (show 10 ≤ g by omega) hc (by rw [hoff]; exact (G.target _ htn htgt).1)
          rw [hoff] at hj
          simp only [exec, hc, ↓reduceIte, SimOutK]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset x.toNat, T', M,
            g - 10, st, ss, hj, SR.le hty hR', KR.of_le (by simpa using hk.drop 2) hkj,
            I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        simp only [exec, SimOutK]
        exact SpecG.consequence (Logic.stopG hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      -- RETURN and REVERT: two known data words, a range within the certificate's bound.
      all_goals
        rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepK] at hok'; done)
        simp only [blockStepK, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        obtain ⟨x, y, S', T', rfl, rfl, -⟩ := sr_data2 hR hdat hk.two_le
        obtain ⟨rfl, hk'⟩ := KR.head hk
        obtain ⟨rfl, -⟩ := KR.head hk'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
      · simp only [exec, SolarTV.EVM.Program.output, SimOutK, Bool.false_eq_true, ↓reduceIte]
        exact SpecG.consequence (return_postSG (ss := ss) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl (R.slot hself)) (fun _ h => h)
          (fun _ h => ⟨ss, h, R.logs⟩)
      · simp only [exec, SolarTV.EVM.Program.output, SimOutK, ↓reduceIte]
        exact SpecG.consequence (revert_postSG (ss := ss) (by decide) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h) (fun _ h => ⟨ss, h, R.logs⟩)


/-! ## The run, from a gas bound on and at every gas -/

open SolarTV.EVM.Program in
/-- EthLib runs the code from a block's offset as SolarTV runs the program from that block, over
steps monotone in gas, with gas for `fuel` blocks of the run: to SolarTV's result when it ends within
them, and with the measure lowered by `fuel` when it does not. -/
theorem run_simK {p : Assemble.Program} {c : Cert} {mx : List Nat} {kn : List Known} {code : ByteArray}
    (G : GlobK p c mx kn code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      b ≤ p.blocks.length → (b < p.blocks.length → c.need b ≤ S.length ∧ S.length ≤ maxH mx b) →
      SR c (c.entry b) S T → KR (entryK kn b) S →
      EntryL c code call (lowerFrom p c b (p.blocks.drop b)) (fuel * bmax c) pc s M g →
      Rel msg ss0 st ss s →
      (∀ r, SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = some r →
        SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)) ∧
      (SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = none →
        Triple (StepG .fusaka) (At code msg pc T M g st ss .empty)
          (fun z => 2 * ((p.blocks.length + 2) * z.gas) + fuel ≤ meas p c g b))
  | 0, b, S, T, s, pc, M, g, st, ss, _, _, _, _, _, _ => by
    refine ⟨fun r hr => by simp [SolarTV.Machine.iterate] at hr, fun _ evm hp => ⟨evm, Reaches.refl _, ?_⟩⟩
    obtain ⟨-, -, -, -, -, -, hg, -⟩ := hp
    rw [hg]
    unfold meas
    omega
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hle, hneed, hR, hkr, E, R => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
      obtain ⟨hn, hm⟩ := hneed hb
      have hbm := budget_le_bmax c b
      have hfm : (fuel + 1) * bmax c = fuel * bmax c + bmax c := Nat.succ_mul _ _
      obtain ⟨pc1, g1, hlabel, hg1, I1⟩ : ∃ pc1 g1, HoareG .fusaka (At code msg pc T M g st ss .empty)
          (At code msg pc1 T M g1 st ss .empty) ∧ g1 + (if isTarget p c b then 1 else 0) ≤ g ∧
          InvL c code call (lowerInstrs p c b p.blocks[b] ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) (budget c b - labelItems p c b)
            (fuel * bmax c) pc1 S s M g1 := by
        have E' := E
        rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at E'
        have hG := E'.gas
        rw [hfm] at hG
        by_cases ht : isTarget p c b = true
        · have hl : labelItems p c b = 1 := by simp [labelItems, ht]
          rw [hl] at hL ⊢
          simp only [ht, ite_true, List.singleton_append] at E'
          obtain ⟨next, hd, hseg⟩ := E'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          exact ⟨pc + 1, g - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
            ⟨hseg, by omega, by omega, E'.le_top, E'.mem⟩⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
            ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
      have hsim := exec_simK (o := o) (kn := kn) G.toT hdata hvalue hstatic hself hcaller ho hbenv (fun _ => htx) he b hb (fuel * bmax c)
        p.blocks[b] (c.need b) (entryK kn b) (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
        hkr hR I1 R
      simp only [SolarTV.Machine.iterate, block, hblk]
      generalize exec o call b p.blocks[b] S s = x at hsim
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', hkr', E', R'⟩ := hsim
        have IH := run_simK G hdata hvalue hstatic hself hcaller ho hbenv htx he fuel t S' T' s' pc' M' g' st' ss'
          htle hneedt hR' hkr' E' R'
        refine ⟨fun r hr => SpecG.seq (Triple.seq hlabel hh) (IH.1 r hr), fun hr evm hp => ?_⟩
        obtain ⟨e1, r1, he1⟩ := hlabel evm hp
        obtain ⟨mid, r2, hmid⟩ := hh e1 he1
        obtain ⟨z, r3, hz⟩ := IH.2 hr mid hmid
        refine ⟨z, (r1.trans r2).trans r3, ?_⟩
        have hgm := reaches_gas_le r2
        rw [hmid.2.2.2.2.2.2.1, he1.2.2.2.2.2.2.1] at hgm
        have := meas_step (c := c) (g := g) (g' := g') hb htle (by omega) hj
        omega
    · obtain rfl : b = p.blocks.length := by omega
      have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
      simp only [SolarTV.Machine.iterate, block, hblk, ite_true]
      refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
      simp only [Option.some.injEq] at hr
      subst hr
      have hseg := E.seg
      rw [lowerFrom_nil p c (by omega)] at hseg
      have hpc := hseg.nil_end
      exact SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h


/-- **The forward assembly theorem for code with loops and constants known across blocks.** -/
theorem forward_of_checkK {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {kn : List Known}
    (hc : checkK p code c mx kn = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hneed0, hk0⟩ := globK_of_checkK hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine run_of_rel_with code call r.2 r.1 gas fun st R => ?_
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; unfold gasBoundL at hg; omega, by simp,
      memRel_initial⟩
  have hsim := run_simK (msg := Final.Target.messageWith gas code call) (ss0 := Substate.empty) G
    rfl (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho rfl rfl he n 0 [] [] _ 0
    .empty gas st Substate.empty (Nat.zero_le _) (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _) (KR.of_le (KR.nil _) hk0)
    E0 R
  exact SpecG.toSpec (hsim.1 r hit)

/-- The forward stage at one gas, for the calls whose run ends within `n call` blocks. -/
theorem stage_of_checkK_gas {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {kn : List Known}
    (hc : checkK p code c mx kn = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (ends : ∃ r, SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) (obs : SolarTV.Observable)
    (hrun : (SolarTV.evmirSem o).run p call = some obs) :
    Final.Target.runWith gas code call = some obs := by
  obtain ⟨r, hit⟩ := ends
  have hres : (SolarTV.evmirSem o).run p call = some (SolarTV.Machine.observe call r.2 r.1) := by
    change (SolarTV.EVM.Program.layer.result o p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨n, hit⟩]
    rfl
  rw [hres] at hrun
  cases hrun
  exact forward_of_checkK hc o ho he call n r hit hg


open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Final
  SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at every gas, for code with loops.** For every program and code the checker
of code with loops accepts, under every oracle whose caller and hash are EthLib's when the program
reads them and whose reads of the block and the transaction are EthLib's when the program reads
them (`EnvOk`, which the certificate's `reads` states), at every gas: every result the bytecode
gives on a call is the result SolarTV's EVM IR semantics gives, or a failure that leaves the
storage and logs nothing. -/
theorem within_of_checkK {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {kn : List Known}
    (hc : checkK p code c mx kn = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (scope : SolarTV.Call → Prop) (gas : Nat)
    (he : c.reads = true → EnvOk o := by intro h; exact absurd h (by decide)) :
    Within (SolarTV.evmirSem o) (ethLibWith gas) p code scope := by
  obtain ⟨G, hseg, hneed0, hk0⟩ := globK_of_checkK hc
  intro call _ obs hrun
  change Target.runWith gas code call = some obs at hrun
  cases hs : obs.success
  · exact Or.inr ⟨rfl, Target.runWith_failure hrun hs⟩
  left
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hs
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  -- The run, the reserve and the fuel.
  set msg := Final.Target.messageWith gas code call with hmsg
  have hcode : msg.code = code := rfl
  have hgas : msg.gas = gas := rfl
  have R := rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  generalize hW : p.blocks.length + 2 = W
  generalize hn : 2 * (W * gas) + W + p.blocks.length + 1 = n
  generalize hK : 22100 * (n * bmax c) + memoryGasCost c.top = K
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty (gas + K) :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; omega, by simp, memRel_initial⟩
  have hsim := run_simK (msg := msg) (ss0 := ss') G rfl (by simp [msg, Final.Target.messageWith,
    Target.message]) rfl rfl rfl ho rfl rfl he n 0 [] [] _ 0 .empty (gas + K) st' ss' (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _) (KR.of_le (KR.nil _) hk0) E0 R
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas K
  cases hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) with
  | none =>
    exfalso
    obtain ⟨z, hz, hmeas⟩ := hsim.2 hit _ hp
    obtain ⟨m, -, rfl, -⟩ := reaches_low hz K _ rfl within hrf hok
    have h1 : W * K ≤ W * (m.gas + K) := Nat.mul_le_mul_left _ (by simp)
    simp only [gas_addGas] at hmeas h1
    unfold meas at hmeas
    rw [hW] at hmeas
    have h2 : W * (gas + K) = W * gas + W * K := Nat.mul_add _ _ _
    split at hmeas <;> omega
  | some r =>
    rcases r with ⟨halt, sF⟩
    have hres : (SolarTV.evmirSem o).run p call = some (SolarTV.Machine.observe call sF halt) := by
      change (SolarTV.EVM.Program.layer.result o p call).map _ = _
      rw [SolarTV.EVM.Program.layer.result_of_ends ⟨n, hit⟩]
      rfl
    rw [hres]
    obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ :=
      SpecG.low (hsim.1 _ hit) hp within hrf hok
    have hss' : ss'.logs.toList = [] := by
      by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
      · rw [(hmove htr).2]
        simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
      · rw [(hcases htr).2]
        simp [Substate.empty]
    have hlogs := logs_of_match hL2
    have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
    have herr' : evm.error = errorOf (SolarTV.Machine.observe call sF halt) := herr
    have hout' : evm.output.toList.map (·.toNat) = (SolarTV.Machine.observe call sF halt).output := hout
    have hst' : (SolarTV.Machine.observe call sF halt).success = true →
        evm.substate.logs = ssF.logs ∧ ∀ slot,
          (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
            (SolarTV.Machine.observe call sF halt).storage slot :=
      fun h => ⟨hlogsF, hst h⟩
    have hok2 : (SolarTV.Machine.observe call sF halt).success = true →
        (SolarTV.Machine.observe call sF halt).logs = SolarTV.Machine.logs sF := by
      cases halt <;> simp [SolarTV.Machine.observe]
    clear herr hout hst hres hsim hit
    generalize SolarTV.Machine.observe call sF halt = X at *
    have hsucc : evm.error.isNone = X.success := by
      rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
    symm
    congr 1
    cases X with
    | mk success output logs storage =>
      simp only at hsucc hout' hok2 hst' ⊢
      obtain rfl : success = true := by rw [← hsucc, hok]; rfl
      rw [SolarTV.Observable.mk.injEq]
      refine ⟨hsucc, hout', ?_, funext fun slot => ?_⟩
      · simp only [hsucc, ↓reduceIte]
        rw [(hst' rfl).1, hL1', hlogs, hok2 rfl]
        rfl
      · simp only [hsucc, ↓reduceIte]
        exact (hst' rfl).2 slot


/--
info: 'SolidCore.Refinement.Solar.AssembleLoop.stage_of_checkK_gas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_checkK_gas

/--
info: 'SolidCore.Refinement.Solar.AssembleLoop.within_of_checkK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms within_of_checkK

end SolidCore.Refinement.Solar.AssembleLoop
