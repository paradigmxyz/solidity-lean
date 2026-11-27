import SolidCore.Refinement.Solar.AssembleGasLoop
import SolidCore.Refinement.Solar.AssembleCheckFast
import SolarTV.CutPoint

/-!
# EVM IR to bytecode with head blocks: entry heights from the run

`AssembleLoop.checkL` bounds each block's entry stack from above by a static height (`maxH`), which
every jump must keep: a jump from block `b` with `h` words over the `need b` it was entered with lands at
most `h + maxH b - need b` high, at most the target's `maxH`. A recursive call raises the stack at the
function's entry by a frame (its return label and the words it keeps) each time the function calls
itself, so no static height of the entry block survives that jump: the entry height grows with the
depth of recursion, by the frame's words per call.

The depth is what the recursion's measure bounds. The relations of a recursive function's EVM IR
stages (tools/certify/rec_cuts.py) bound, at each of the function's cut points (its entry and the
points it resumes at after a recursive call), the stack below the frame together with the measure:
`T.length + w * arg ≤ 984`. That bounds the entry height at every depth at once (the stack below
the frame holds the frames already pushed, the measure the ones still to come), and it is a fact of
the run that the stage proofs prove: every configuration of the final EVM IR at a cut point is
related to one of the stage before it (`reach_cut`, read off the cut-point simulation).

`checkR` is `checkL` with a list of head blocks: a jump or a fall into a head keeps no static
height, and the bound at a head's entry is instead a hypothesis on the run (`HeadsOk`: every
configuration the final EVM IR reaches at a head is at most the head's `maxH` high). Everything
else is `checkL`'s: the decoding, the labels, the entry heights from below and the stack types at
every jump (heads included), memory at constant offsets, budgets, and every block's
`maxH b + budget b ≤ 1000`, heads included, so the stack stays below 1024 on every run however
deep it recurses. `forward_of_checkR` and `stage_of_checkR_gas` are `forward_of_checkL` and
`stage_of_checkL_gas` under `HeadsOk`, proved the same way: the simulation of a block is
`AssembleLoopSim`'s with the head-aware height check, and the run's simulation carries that the
configuration is reached from the call's first one. With no heads, `checkR` asks what `checkL` does.

NOTE: `checkR` is the height half of recursion only. Its entry heights from below (`need`) and
its entry words' types stay static and are checked at every jump, heads included. A recursive call
pushes its frame over the caller's, so the caller's return label is deeper than any static entry
type of the function's blocks reaches, and the point the caller resumes at after the call needs it
typed as a label again: no recursive program passes that check. `checkF` (the frames, below the
heads' bound) is the other half: the stack below a block of the recursive function is a stack of
frames, each the words one call site keeps with that site's return label above them
(`FrB`, one constructor per kind of call site, as rec_cuts.py's `Fr`), so a return types the
caller's words by the label it returns to rather than by static types. `forward_of_checkF` and
`stage_of_checkF_gas` are `forward_of_checkR` and `stage_of_checkR_gas` for it.
-/

namespace SolidCore.Refinement.Solar.AssembleRec

open SolidCore.Refinement.Solar.Assemble
open SolidCore.Refinement.Solar.AssembleLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## The checker -/

/-- The height check of a jump or a fall from block `b` to block `t` with `h` words on the stack, `nb`
the height `b` needs: a head keeps no static height (the run's hypothesis bounds its entry), any
other target's highest entry bounds the stack, as in `jumpOkL`. -/
def heightOk (mx hd : List Nat) (b t h nb : Nat) : Bool :=
  hd.contains t || decide (h + maxH mx b ≤ maxH mx t + nb)

theorem heightOk_le {mx hd : List Nat} {b t h nb : Nat} (hok : heightOk mx hd b t h nb = true)
    (hn : hd.contains t = false) : h + maxH mx b ≤ maxH mx t + nb := by
  unfold heightOk at hok
  rw [hn, Bool.false_or] at hok
  exact of_decide_eq_true hok

/-- `jumpOkL` with the height check of `heightOk`. -/
def jumpOkR (p : Program) (c : Cert) (mx hd : List Nat) (b t h : Nat) (ty : List Ty) : Bool :=
  decide (t < p.blocks.length) && isTarget p c t && decide (c.need t ≤ h) && tyLe ty (c.entry t) &&
    heightOk mx hd b t h (c.need b)

/-- `fallOkL` with the height check of `heightOk`. -/
def fallOkR (p : Program) (c : Cert) (mx hd : List Nat) (b h : Nat) (ty : List Ty) : Bool :=
  (decide (p.blocks.length ≤ b + 1) || decide (c.need (b + 1) ≤ h)) && tyLe ty (c.entry (b + 1)) &&
    heightOk mx hd b (b + 1) h (c.need b)

/-- `Assemble.blockStep` for block `b` of code with loops: the same check of each instruction,
with `jumpOkR` for its jumps, which put no bound on the target's budget, and MLOAD at a constant
offset below the certificate's bound. -/
def blockStepR (p : Program) (c : Cert) (mx hd : List Nat) (b : Nat)
    (ok : Nat → Known → List Ty → Nat → Bool) :
    Nat → Known → List Ty → Nat → Assemble.Instr → Bool
  | h, known, ty, k, .op (.stack op) =>
    match op with
    | .push v => decide (1 ≤ k) && ok (h + 1) (some v :: known) (some false :: ty) (k - 1)
    | .dup i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 1 ≤ h) &&
      ok (h + 1) (kAt known i.val :: known) (tyAt ty i.val :: ty) (k - 1)
    | .swap i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 2 ≤ h) &&
      ok h [] (tySwap ty i.val) (k - 1)
    | .pop => decide (1 ≤ k) && decide (1 ≤ h) && ok (h - 1) [] ty.tail (k - 1)
    | op =>
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat (none :: known.drop need) (some false :: ty.drop need) (k - 1)
      | none => false
  | h, known, ty, k, .op .store =>
    match known with
    | some o :: _ => decide (1 ≤ k) && decide (2 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 2 &&
      ok (h - 2) (known.drop 2) (ty.drop 2) (k - 1)
    | _ => false
  | h, known, ty, k, .op .load =>
    match known with
    | some o :: _ => decide (1 ≤ k) && decide (1 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 1 &&
      ok h [] (some false :: ty.drop 1) (k - 1)
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
  | h, _, ty, k, .jump t => decide (2 ≤ k) && jumpOkR p c mx hd b t h ty
  | h, _, ty, k, .jumpi t =>
    decide (2 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkR p c mx hd b t (h - 1) ty.tail &&
      ok (h - 1) [] ty.tail (k - 2)
  | h, _, ty, k, .pushLabel t =>
    decide (1 ≤ k) && c.rets.contains t && decide (t < 2 ^ 32) && ok (h + 1) [] (some true :: ty) (k - 1)
  | h, _, ty, k, .jumpDyn =>
    decide (1 ≤ k) && decide (1 ≤ h) && tyAt ty 0 == some true &&
      c.rets.all fun t => jumpOkR p c mx hd b t (h - 1) ty.tail
  | _, _, _, _, .stop => true
  | _, known, ty, _, .ret | _, known, ty, _, .revert =>
    match known with
    | some o :: some s :: _ => isData ty 2 && rangeOk c o s
    | _ => false
  | _, _, _, _, _ => false

/-- `Assemble.blockOk` for code with loops. -/
def blockOkR (p : Program) (c : Cert) (mx hd : List Nat) (b : Nat) :
    Nat → Known → List Ty → Nat → List Assemble.Instr → Bool
  | h, _, ty, _, [] => fallOkR p c mx hd b h ty
  | h, known, ty, k, i :: rest =>
    match turnedElse c b i rest with
    | some e =>
      decide (3 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkR p c mx hd b e (h - 1) ty.tail &&
        fallOkR p c mx hd b (h - 1) ty.tail
    | none =>
      if dropped p b i rest then
        match i with
        | .stop => true
        | _ => fallOkR p c mx hd b h ty
      else blockStepR p c mx hd b (fun h known ty k => blockOkR p c mx hd b h known ty k rest) h known ty k i

/-- Every block checks from the height and the types it needs, within its budget less its
label's item, with its highest entry stack and budget below 1000 words. -/
def blocksOkR (p : Program) (c : Cert) (mx hd : List Nat) : Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
      decide (maxH mx b + budget c b ≤ 1000) &&
      blockOkR p c mx hd b (c.need b) [] (c.entry b) (budget c b - labelItems p c b) instrs &&
      blocksOkR p c mx hd (b + 1) rest

/-- The checker for code with loops. -/
def checkR (p : Program) (code : ByteArray) (c : Cert) (mx hd : List Nat) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkR p c mx hd 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32)


/-! ## What the check gives -/

theorem blocksOkR_get {p : Program} {c : Cert} {mx hd : List Nat} : ∀ (l : List (List Assemble.Instr)) (b : Nat),
    blocksOkR p c mx hd b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ budget c (b + k) ∧ c.need (b + k) ≤ maxH mx (b + k) ∧
      maxH mx (b + k) + budget c (b + k) ≤ 1000 ∧
      blockOkR p c mx hd (b + k) (c.need (b + k)) [] (c.entry (b + k))
        (budget c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOkR, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [and_assoc] using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOkR, Bool.and_eq_true] at h
    have := blocksOkR_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the check the simulation uses at every block. -/
structure GlobR (p : Program) (c : Cert) (mx hd : List Nat) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 32
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ budget c t ∧
    c.need t ≤ maxH mx t ∧ maxH mx t + budget c t ≤ 1000 ∧
    blockOkR p c mx hd t (c.need t) [] (c.entry t) (budget c t - labelItems p c t) p.blocks[t] = true

theorem GlobR.toT {p : Program} {c : Cert} {mx hd : List Nat} {code : ByteArray} (G : GlobR p c mx hd code) :
    GlobLT p c code :=
  ⟨G.top_mod, G.top_le, G.size_lt, G.target⟩

theorem globR_of_checkR {p : Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    (h : checkR p code c mx hd = true) :
    GlobR p c mx hd code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 := by
  simp only [checkR, Bool.and_eq_true, decide_eq_true_eq] at h
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
  · have := blocksOkR_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## The simulation of a block

`AssembleLoopSim`'s, with the height check of `heightOk`. -/

set_option hygiene false in
/-- The bound of the stack in lockstep with the height of the check. -/
local macro "hu_tac" : tactic => `(tactic| first | omega | (simp at hu ⊢; omega) | (simp; omega))

/-- What a block's instructions from `pc` give: a halt EthLib's frame shows, or the next block,
reached by EthLib with its stack related at the block's types, at most its highest entry stack,
with gas for the reserve `R`, and by a jump to a labelled block or a fall into the next one. -/
def SimOutR (p : Program) (c : Cert) (mx hd : List Nat) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState) (ss : Substate)
    (b R pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧
      (t < p.blocks.length → c.need t ≤ S'.length ∧ (hd.contains t = false → S'.length ≤ maxH mx t)) ∧
      (t = b + 1 ∨ isTarget p c t = true)) ∧
      ∃ pc' T' M' g' st' ss', HoareG .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧
        EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R pc' s' M' g' ∧
        Rel msg ss0 st' ss' s'

theorem SimOutR.pre {p : Program} {c : Cert} {mx hd : List Nat} {code : ByteArray} {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutR p c mx hd code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 r) :
    SimOutR p c mx hd code call msg ss0 st ss b R pc T M g r := by
  match r, h1 with
  | .inl (_, _), hspec => exact SpecG.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hinv, hrel⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hinv, hrel⟩

theorem blockStepR_stack {p : Program} {c : Cert} {mx hd : List Nat} {bb : Nat} {ok : Nat → Known → List Ty → Nat → Bool}
    {h k : Nat} {known : Known} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    (hdup : ∀ i, op ≠ .dup i) (hs : ∀ i, op ≠ .swap i) (hp : op ≠ .pop) :
    blockStepR p c mx hd bb ok h known ty k (.op (.stack op)) =
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat (none :: known.drop need) (some false :: ty.drop need) (k - 1)
      | none => false := by
  cases op <;> first | rfl | exact absurd rfl (hne _) | exact absurd rfl (hdup _) |
    exact absurd rfl (hs _) | exact absurd rfl hp


/-- `stack_sim` for `blockStepR`, with the heights of the check and the stack in lockstep. -/
theorem stack_simR {p : Program} {c : Cert} {mx hd : List Nat} {bb : Nat} {ok : Nat → Known → List Ty → Nat → Bool}
    {h k : Nat} {known : Known} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    {ctx : SolarTV.EVM.Context} {S T : List Word}
    (hok : blockStepR p c mx hd bb ok h known ty k (.op (.stack op)) = true) (hh : h ≤ S.length)
    (hk : KR known S) (hR : SR c ty S T) :
    1 ≤ k ∧ ∃ byte, opByte op = some byte ∧ ∃ h' ty' S' T',
      SolarTV.EVM.step ctx op S = some S' ∧ SolarTV.EVM.step ctx op T = some T' ∧
      SR c ty' S' T' ∧ h' ≤ S'.length ∧ S'.length ≤ S.length + 1 ∧ S'.length + h = h' + S.length ∧
      ∃ known', KR known' S' ∧ ok h' known' ty' (k - 1) = true := by
  have hL := hR.length
  by_cases hd : ∃ i, op = .dup i
  · obtain ⟨i, rfl⟩ := hd
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x80 + i.val, by simp [opByte, h16], h + 1, _, _, _, ?_, ?_, SR.dup hR hiS hiT, by simp; omega, by simp, by simp; omega, _,
      hk.dup hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hs : ∃ i, op = .swap i
  · obtain ⟨i, rfl⟩ := hs
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    simp only [List.length_cons] at hh hL
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x90 + i.val, by simp [opByte, h16], h, _, _, _, ?_, ?_, SR.swap hR hiS hiT, by simp; omega, by simp, by simp; omega, [],
      KR.nil _, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hp : op = .pop
  · subst hp
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, h1⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    refine ⟨hk1, _, rfl, h - 1, _, _, _, rfl, rfl, (SR.uncons.1 hR).2, by simp at hh; omega,
      by simp only [List.length_cons]; omega, by simp at hh ⊢; omega, [], KR.nil _, hok⟩
  have hd' : ∀ i, op ≠ .dup i := fun i e => hd ⟨i, e⟩
  have hs' : ∀ i, op ≠ .swap i := fun i e => hs ⟨i, e⟩
  rw [blockStepR_stack hne hd' hs' hp] at hok
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
      SR.cons (τ := some false) rfl (SR.drop need hR), ?_, ?_, ?_, _, (hk.drop need).cons_none _, hok⟩
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
  · cases hok


/-- An opcode item at the head of a walk: its byte at the counter, and the walk on from the next
byte. -/
theorem op_seg {code : ByteArray} {offset : Nat → Nat} {pc e byte : Nat} {items : List Item}
    (h : Seg (bytesOf code) offset pc (.op byte :: items) e) :
    ∃ _ : pc < code.size, code[pc] = UInt8.ofNat byte ∧
      Seg (bytesOf code) offset (pc + 1) items e := by
  obtain ⟨next, hd, hseg⟩ := h.head
  obtain ⟨hlt, hcode, rfl⟩ := op_item hd
  exact ⟨hlt, hcode, hseg⟩

/-- A data word on top of SolarTV's stack is the word on top of EthLib's. -/
theorem sr_data1 {c : Cert} {ty : List Ty} {S T : List Word} (hR : SR c ty S T)
    (hd : isData ty 1 = true) (hS : 1 ≤ S.length) :
    ∃ x S' T', S = x :: S' ∧ T = x :: T' ∧ SR c ty.tail S' T' := by
  have hL := hR.length
  rcases S with _ | ⟨x, S'⟩ <;> rcases T with _ | ⟨y, T'⟩ <;> simp at hS hL
  obtain rfl := (SR.head hR hd).symm
  exact ⟨x, S', T', rfl, rfl, (SR.uncons.1 hR).2⟩

/-- Two data words on top of SolarTV's stack are the words on top of EthLib's. -/
theorem sr_data2 {c : Cert} {ty : List Ty} {S T : List Word} (hR : SR c ty S T)
    (hd : isData ty 2 = true) (hS : 2 ≤ S.length) :
    ∃ x y S' T', S = x :: y :: S' ∧ T = x :: y :: T' ∧ SR c (ty.drop 2) S' T' := by
  have hL := hR.length
  rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩ <;> rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩ <;> simp at hS hL
  have htake := hR.data hd
  simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
  obtain ⟨rfl, rfl, -⟩ := htake
  exact ⟨x, y, S', T', rfl, rfl, by simpa using SR.drop 2 hR⟩

/-- A stack with a known second word has at least two. -/
theorem kr_two_le {j : Option Word} {o : Word} {known : Known} {S : List Word}
    (h : KR (j :: some o :: known) S) : 2 ≤ S.length := by
  obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 (h 1 o (by simp [kAt]))
  omega


open SolarTV.EVM.Program in
/-- EthLib runs the code of a block's instructions from the offset of the next one as SolarTV
runs them, over steps monotone in gas, with gas for the reserve `R` beyond the block, for a
message from any account `a` (CALLER is `a`; the transaction's environment is `Target.txEnv`'s
only when the block reads it). -/
theorem exec_simR {p : Assemble.Program} {c : Cert} {mx hd : List Nat} {code : ByteArray} (G : GlobLT p c code)
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
      blockOkR p c mx hd b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S T →
      InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k Rv
        pc S s M g → Rel msg ss0 st ss s →
      SimOutR p c mx hd code call msg ss0 st ss b Rv pc T M g (exec o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, _, hR, I, R => by
    simp only [blockOkR, fallOkR, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have I2 := I.entry
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [exec, SimOutR]
    exact ⟨⟨by omega, fun ht => ⟨by omega, fun hn => by have := heightOk_le hok.2 hn; omega⟩, by simp⟩, pc, T, M, g, st, ss,
      Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I2, R⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOkR, hT, jumpOkR, fallOkR, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, ⟨hfall, hfty⟩, hcost'⟩ := hok
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
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOutR]
        exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr hetgt⟩, c.offset e, T', M, g1 - 10, st,
          ss, Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR',
          I.target G hen hetgt (m := 3) (by omega) (by omega), R⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOutR]
        refine ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost' hn; omega⟩, by simp⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR',
          ⟨hseg, ?_, I.le_top, I.mem⟩, R⟩
        have := I.gas
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOkR, hT, hD, ite_true, fallOkR, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutR]
          exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hok.2 hn; omega⟩, by simp⟩, pc, T, M, g, st, ss,
            Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I.entry, R⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [exec, SimOutR]
          exact SpecG.consequence (stop_of_size_leG (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      have hok' : blockStepR p c mx hd b (fun h known ty k => blockOkR p c mx hd b h known ty k rest) h known ty k i =
          true := by
        simpa only [blockOkR, hT, hD', Bool.false_eq_true, ite_false] using hok
      have I' : InvL c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      clear hok hD hD' hT
      have IH := exec_simR (mx := mx) (hd := hd) (o := o) (ss0 := ss0) G hdata hvalue hstatic hself hcaller ho hbenv htx he b hb Rv rest
      -- An effect that pushes one word on both stacks for 2 gas and keeps the rest.
      have push2 : ∀ {e : SolarTV.Machine.Effect} {byte : Nat} {w : Word} {known' : Known},
          SolarTV.Machine.Effect.apply o call e [] s = some (some w, s) → KR known' (w :: S) →
          InvL c code call (.op byte :: (lowerInstrs p c b rest ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g → 1 ≤ k →
          blockOkR p c mx hd b (h + 1) known' (some false :: ty) (k - 1) rest = true →
          (∀ hlt : pc < code.size, code[pc] = UInt8.ofNat byte → 2 ≤ g → T.length < STACK_LIMIT →
            HoareG .fusaka (At code msg pc T M g st ss .empty)
              (At code msg (pc + 1) (w :: T) M (g - 2) st ss .empty)) →
          SimOutR p c mx hd code call msg ss0 st ss b Rv pc T M g
            (exec o call b (.effect e 0 :: rest) S s) := by
        intro e byte w known' happ hkn I' hk1 hok hrule
        obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        rw [exec_effect0 happ (by omega)]
        exact SimOutR.pre (hrule hlt hcode (by omega) (by unfold STACK_LIMIT; omega))
          (IH (h + 1) known' _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok (by simp; omega)
            (by hu_tac) hkn (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      -- The check refuses the instructions outside the fragment.
      all_goals try (simp [blockStepR] at hok'; done)
      · rcases mop with sop | _ | _ | _ | _ | _ | _ <;> try (simp [blockStepR] at hok'; done)
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [exec_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOutR.pre hpush (IH (h + 1) (some v :: known) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega) (by hu_tac)
              (hk.cons_some v)
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R)
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', hlock, known', hkn,
              hok⟩ := stack_simR (ctx := context o call s) hne hok' hh hk hR
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_ruleG (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            rw [exec_stack hstep (by omega) (by omega)]
            exact SimOutR.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega) (by hu_tac)
              hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R)
        · -- MLOAD.
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutR.pre hrule (IH h [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok' (by simp; omega)
            (by hu_tac) (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'))
            ⟨hseg, by simp; omega, ?_, by rw [hM']; omega, memRel_expand I'.mem hbound⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- MSTORE.
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutR.pre (Logic.mstoreG (start := ow) (value := v) (rest := T') (memory := M)
            (gas := g) hlt hcode (by omega)) (IH (h - 2) _ _ S' T' (k - 1) _ (pc + 1) _ _ st ss hok'
            (by omega) (by hu_tac) (hk.drop 2) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega, hmem'⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
      · rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | name | _
        all_goals try (simp [blockStepR] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutR.pre hrule ?_
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
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutR.pre hrule ?_
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
          rcases ar with _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          exact SimOutR.pre hrule (IH h _ _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega) (by hu_tac)
            ((hk.drop 1).cons_none _) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLDATASIZE.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.calldata.size) rfl (KR.nil _) I' hok'.1 hok'.2
            fun hlt hcode hg hs => by rw [← hdata]; exact Logic.calldatasizeG hlt hcode hg hs
        · -- CALLVALUE.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.callvalue) rfl (KR.nil _) I' hok'.1 hok'.2
            fun hlt hcode hg hs => by rw [← hvalue]; exact Logic.callvalueG hlt hcode hg hs
        · -- CALLER.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          exact push2 (w := o.caller.setWidth 256) rfl (hk.cons_none _) I' hk1 hok
            fun hlt hcode hg hs => by
              rw [(ho henv).1, ← hcaller]; exact Logic.callerG hlt hcode hg hs
        · -- ADDRESS.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 SolarTV.environment.callee) rfl (KR.nil _) I' hok'.1
            hok'.2 fun hlt hcode hg hs => by
              rw [← address_word, ← hself]; exact Logic.addressG hlt hcode hg hs
        · -- LOGn.
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutR.pre hrule (IH (h - (tops.length + 2)) [] _ S2 T2 (k - 1) _ (pc + 1) _ _ st _
            hok (by omega) (by hu_tac) (KR.nil _) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega,
            memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, ?_⟩)
          · rw [hM']; omega
          · refine ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy)
                ow.toNat sw.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, ?_⟩⟩
            exact read_eq I'.mem
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨henv, hk1⟩, h2⟩, hdat⟩, hin⟩, hkc⟩, hok⟩ := hok'
          obtain ⟨x, y, S', T', rfl, rfl, hR'⟩ := sr_data2 hR hdat (kr_two_le hk)
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
          refine SimOutR.pre hrule (IH (h - 1) [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok
            (by simp; omega) (by hu_tac) (KR.nil _) (SR.cons (τ := some false) rfl hR') ⟨hseg, by simp; omega, ?_,
            by rw [hM']; omega, memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- An environment read of the block or the transaction.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hreads, hsome⟩, hk1⟩, hok⟩ := hok'
          obtain ⟨⟨byte, w⟩, hread⟩ := Option.isSome_iff_exists.1 hsome
          simp only [lowerInstr, hread, Option.map_some, Option.getD_some,
            List.singleton_append] at I'
          exact push2 (w := BitVec.ofNat 256 w)
            (by simp [SolarTV.Machine.Effect.apply, he hreads name byte w hread]) (KR.nil _) I' hk1 hok
            fun hlt hcode hg hs => env_readG hread hlt hcode hbenv (htx hreads) hg hs
      · -- JUMP.
        simp only [blockStepR, jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hk2, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩ := hok'
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
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutR]
        exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr htgt⟩, c.offset t, T, M, g1 - 8, st, ss,
          Triple.seq hpush hj, SR.le hty hR,
          I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- JUMPI.
        simp only [blockStepR, jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩, hok'⟩ := hok'
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
          exact SimOutR.pre (Triple.seq hpush hj) (IH (h - 1) [] _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (by hu_tac) (KR.nil _) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R)
        · have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOutR]
          exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr htgt⟩, c.offset t, T', M, g1 - 10, st,
            ss, Triple.seq hpush hj, SR.le hty hR',
            I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- A pushed return label: a PUSH of the block's offset.
        simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
        exact SimOutR.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega) (by hu_tac)
          (KR.nil _) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R)
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
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
        simp only [jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩ := hj'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
          hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
        rw [hoff] at hj
        simp only [exec, SimOutR]
        exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st,
          ss, hj, SR.le hty hR', I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        simp only [exec, SimOutR]
        exact SpecG.consequence (Logic.stopG hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      -- RETURN and REVERT: two known data words, a range within the certificate's bound.
      all_goals
        rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
        simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        obtain ⟨x, y, S', T', rfl, rfl, -⟩ := sr_data2 hR hdat (kr_two_le hk)
        obtain ⟨rfl, hk'⟩ := KR.head hk
        obtain ⟨rfl, -⟩ := KR.head hk'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
      · simp only [exec, SolarTV.EVM.Program.output, SimOutR, Bool.false_eq_true, ↓reduceIte]
        exact SpecG.consequence (return_postSG (ss := ss) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl (R.slot hself)) (fun _ h => h)
          (fun _ h => ⟨ss, h, R.logs⟩)
      · simp only [exec, SolarTV.EVM.Program.output, SimOutR, ↓reduceIte]
        exact SpecG.consequence (revert_postSG (ss := ss) (by decide) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h) (fun _ h => ⟨ss, h, R.logs⟩)


/-! ## The run -/

open SolarTV.EVM.Program in
/-- `run_simL` for the checker with heads: EthLib runs the code from a block's offset as SolarTV runs
the program from that block, over steps monotone in gas, with gas for `fuel` blocks of the run, for
the configurations of a set `reach` closed under the program's steps, at whose heads the stack is
at most the head's highest entry (`hhead`). -/
theorem run_simR {p : Assemble.Program} {c : Cert} {mx hd : List Nat} {code : ByteArray}
    (G : GlobR p c mx hd code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (reach : Nat × List Word × SolarTV.Machine.State → Prop)
    (hclosed : ∀ x y, reach x → block o call p x = some (.inr y) → reach y)
    (hhead : ∀ x, reach x → x.1 < p.blocks.length → hd.contains x.1 = true →
      x.2.1.length ≤ maxH mx x.1) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      reach (b, S, s) → b ≤ p.blocks.length →
      (b < p.blocks.length → c.need b ≤ S.length ∧ (hd.contains b = false → S.length ≤ maxH mx b)) →
      SR c (c.entry b) S T →
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
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hreach, hle, hneed, hR, E, R => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
      obtain ⟨hn, hm'⟩ := hneed hb
      -- The entry height: a static one, or at a head the run's.
      have hm : S.length ≤ maxH mx b := by
        cases hc : hd.contains b
        · exact hm' hc
        · exact hhead (b, S, s) hreach hb hc
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
          obtain ⟨next, hd', hseg⟩ := E'.seg.head
          simp only [Item.expected] at hd'
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd'
          exact ⟨pc + 1, g - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
            ⟨hseg, by omega, by omega, E'.le_top, E'.mem⟩⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
            ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
      have hsim := exec_simR (o := o) G.toT hdata hvalue hstatic hself hcaller ho hbenv (fun _ => htx) he b hb
        (fuel * bmax c) p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
        (KR.nil _) hR I1 R
      have hstep : block o call p (b, S, s) = some (exec o call b p.blocks[b] S s) := by
        simp only [block, hblk]
      simp only [SolarTV.Machine.iterate, block, hblk]
      generalize exec o call b p.blocks[b] S s = x at hsim hstep
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', E', R'⟩ := hsim
        have IH := run_simR G hdata hvalue hstatic hself hcaller ho hbenv htx he reach hclosed hhead
          fuel t S' T' s' pc' M' g' st' ss' (hclosed _ _ hreach hstep) htle hneedt hR' E' R'
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

/-! ## The run's heads -/

section Steps

variable {σ ρ : Type} {step : SolarTV.CutPoint.Step σ ρ}

/-- A step after `k` steps to a configuration is the `k + 1`-th. -/
theorem steps_snoc : ∀ (k : Nat) {x0 x y : σ}, SolarTV.CutPoint.steps step k x0 = some (.inr x) →
    step x = some (.inr y) → SolarTV.CutPoint.steps step (k + 1) x0 = some (.inr y)
  | 0, x0, x, y, h, hs => by
    simp only [SolarTV.CutPoint.steps, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    simp only [SolarTV.CutPoint.steps, hs]
  | k + 1, x0, x, y, h, hs => by
    simp only [SolarTV.CutPoint.steps] at h ⊢
    cases e : step x0 with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r => rw [e] at h; cases h
      | inr z =>
        rw [e] at h
        simp only
        exact steps_snoc k h hs

end Steps

/-- What the final EVM IR's run must give the checker at its heads: every configuration it reaches
from the call's first one at a head is at most the head's highest entry high. -/
def HeadsOk (o : SolarTV.Machine.Oracle) (call : SolarTV.Call) (p : Assemble.Program)
    (mx hd : List Nat) : Prop :=
  ∀ k x, SolarTV.CutPoint.steps (SolarTV.EVM.Program.block o call p) k
      (0, [], SolarTV.Machine.State.initial call) = some (.inr x) →
    x.1 < p.blocks.length → hd.contains x.1 = true → x.2.1.length ≤ maxH mx x.1

/-! ## What the check gives -/

/-- **The forward assembly theorem for code with recursion**: `forward_of_checkL` under the run's
bound at its heads. -/
theorem forward_of_checkR {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    (hc : checkR p code c mx hd = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (heads : HeadsOk o call p mx hd) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hneed0⟩ := globR_of_checkR hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine run_of_rel_with code call r.2 r.1 gas fun st R => ?_
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; unfold gasBoundL at hg; omega, by simp,
      memRel_initial⟩
  let reach : Nat × List Word × SolarTV.Machine.State → Prop := fun x =>
    ∃ k, SolarTV.CutPoint.steps (SolarTV.EVM.Program.block o call p) k
      (0, [], SolarTV.Machine.State.initial call) = some (.inr x)
  have hclosed : ∀ x y, reach x → SolarTV.EVM.Program.block o call p x = some (.inr y) → reach y :=
    fun _ _ ⟨k, hk⟩ hs => ⟨k + 1, steps_snoc k hk hs⟩
  have hhead : ∀ x, reach x → x.1 < p.blocks.length → hd.contains x.1 = true →
      x.2.1.length ≤ maxH mx x.1 := fun x ⟨k, hk⟩ => heads k x hk
  have hsim := run_simR (msg := Final.Target.messageWith gas code call) (ss0 := Substate.empty) G
    rfl (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho rfl rfl he reach hclosed
    hhead n 0 [] [] _ 0 .empty gas st Substate.empty ⟨0, rfl⟩ (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], fun _ => by simp⟩) (SR.nil c _) E0 R
  exact SpecG.toSpec (hsim.1 r hit)

/-- The forward stage at one gas, for the calls whose run ends within `n call` blocks and keeps
the bound at its heads: `stage_of_checkL_gas` for code with recursion. -/
theorem stage_of_checkR_gas {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    (hc : checkR p code c mx hd = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) (heads : HeadsOk o call p mx hd) (n : Nat)
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
  exact forward_of_checkR hc o ho he call heads n r hit hg

/-! ## The fast form -/

/-- `checkR` with the walk on the code's suffixes and without the labels' check
(`AssembleLoop.checkLS`). -/
def checkRS (p : Program) (code : ByteArray) (c : Cert) (mx hd : List Nat) : Bool :=
  walkS c.offset (bytesOf code) 0 (lower p c) && blocksOkR p c mx hd 0 p.blocks &&
    decide (c.need 0 = 0) && decide (c.top % 32 = 0) && decide (c.top ≤ 2 ^ 32) &&
    decide (code.size < 2 ^ 32)

theorem checkR_of_checkRS {p : Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    (h : checkRS p code c mx hd = true) : checkR p code c mx hd = true := by
  have hw := walkS_drop (bytesOf code) c.offset (lower p c) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  simp only [checkRS, hw, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hwalk, hb⟩, h0⟩, h32⟩, htop⟩, hsize⟩ := h
  simp only [checkR, hwalk, hb, labelsValid_of_walk hwalk, h0, h32, htop, hsize, Bool.and_self]

/-! ## The heads' bound from the stage proofs

A cut-point simulation (`CutPoint.Sim`) relates the two programs' configurations at their cut points
segment by segment. Read on its second program, it says that every configuration that program reaches
at a cut point, after at least one step from a related one, is related to one of the first program's:
the relation is an invariant of the second program's cut points. For a recursive function's last EVM IR
stage, whose relations bound the stack at its cut points by the measure, that is `HeadsOk` at heads
that are cut points. -/

section Reach

open SolarTV.CutPoint

variable {σ ρ τ ρ' : Type} {step : Step σ ρ} {cut : σ → Bool} {step' : Step τ ρ'} {cut' : τ → Bool}

/-- A segment that does not run out of fuel stops at the first cut point its steps reach: every cut
point `z` reached in `i ≥ 1` steps comes at or after the segment's own cut point `y`, which is reached
in `j ≤ i` steps. -/
theorem seg_first : ∀ (k : Nat) (x : τ), seg step' cut' k x ≠ .fuel → ∀ (i : Nat) (z : τ), 1 ≤ i →
    steps step' i x = some (.inr z) → cut' z = true →
    ∃ y j, seg step' cut' k x = .cut y ∧ 1 ≤ j ∧ j ≤ i ∧ steps step' j x = some (.inr y) ∧
      steps step' (i - j) y = some (.inr z)
  | 0, _, h, _, _, _, _, _ => absurd rfl h
  | k + 1, x, h, i, z, hi, hz, hc => by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [seg] at h ⊢
    simp only [steps] at hz
    cases e : step' x with
    | none => rw [e] at hz; cases hz
    | some v =>
      cases v with
      | inl r => rw [e] at hz; cases hz
      | inr y0 =>
        simp only [e] at h hz ⊢
        by_cases c0 : cut' y0 = true
        · simp only [c0, ↓reduceIte]
          exact ⟨y0, 1, rfl, le_refl _, by omega, by simp only [steps, e], by simpa using hz⟩
        · simp only [c0, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · simp only [steps, Option.some.injEq, Sum.inr.injEq] at hz
            subst hz
            exact absurd hc c0
          · obtain ⟨y, j, hs, hj1, hji, hj, hrest⟩ := seg_first k y0 h i z hpos hz hc
            refine ⟨y, j + 1, hs, by omega, by omega, by simp only [steps, e]; exact hj, ?_⟩
            rwa [show i + 1 - (j + 1) = i - j by omega]

/-- **The relation is an invariant of the second program's cut points**: from related
configurations, every cut point the second program reaches in `n ≥ 1` steps is related to some
configuration of the first. -/
theorem reach_cut {Ag : ρ → ρ' → Prop} {Rel : σ → τ → Prop}
    (S : Sim step cut step' cut' Ag Rel) :
    ∀ (n : Nat) (x : σ) (x' : τ), Rel x x' → ∀ z, 1 ≤ n → steps step' n x' = some (.inr z) →
      cut' z = true → ∃ y, Rel y z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x x' hxx z hn hz hc
    obtain ⟨k, k', hseg⟩ := S.segment x x' hxx
    have hne : seg step' cut' k' x' ≠ .fuel := by
      intro e
      rw [e] at hseg
      generalize seg step cut k x = a at hseg
      cases a <;> simp [SegRel] at hseg
    obtain ⟨y', j, hs, hj1, hjn, -, hrest⟩ := seg_first k' x' hne n z hn hz hc
    rw [hs] at hseg
    obtain ⟨y, hy⟩ : ∃ y, Rel y y' := by
      cases e : seg step cut k x with
      | cut y => rw [e] at hseg; exact ⟨y, hseg⟩
      | done _ => rw [e] at hseg; simp [SegRel] at hseg
      | stuck => rw [e] at hseg; simp [SegRel] at hseg
      | fuel => rw [e] at hseg; simp [SegRel] at hseg
    rcases Nat.eq_zero_or_pos (n - j) with h0 | hpos
    · rw [h0] at hrest
      simp only [steps, Option.some.injEq, Sum.inr.injEq] at hrest
      subst hrest
      exact ⟨y, hy⟩
    · exact IH (n - j) (by omega) y y' hy z hpos hrest hc

end Reach

/--
info: 'SolidCore.Refinement.Solar.AssembleRec.stage_of_checkR_gas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_checkR_gas

/--
info: 'SolidCore.Refinement.Solar.AssembleRec.reach_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reach_cut

/-! ## Frames: the stack below a recursive function's blocks

A recursive call pushes the callee's frame (its return label and arguments) over the words the
caller keeps, and those over the caller's own frame, so the words below any block of the function
are a stack of frames, as deep as the recursion. Each frame starts at a call site, and its return
label is the label that call site pushed. That call site fixes what the frame keeps below the callee:
how many words, their types, and, for a call from the function itself, where among them the caller's
own return label is, whose frame continues below.

`FrB c F L R RT` is that relation between SolarTV's stack `R` below a frame whose return label is
`L` and EthLib's `RT`: `L` is one of the call sites' labels; the words its call keeps are at the call's
types (labels at their offsets, data equal); and, for a call from the function, the caller's label
among them heads the same relation over the rest. It has one constructor per kind of call site, as
the stage relations of tools/certify/rec_cuts.py have (their `Fr`).

`checkF` is `checkR` with these frames: inside the function (its `Frames.blocks`), the checker knows
which stack words are the frame's own return label (every word it types a label, `LabsAre`), and that
the words below the height it tracks are the frame's, untouched (`XI`). Its dynamic jump is a return:
to the frame's label, whatever call pushed it, with the words that call kept below the results
typed by the frame relation instead of the static types. A call (`pushLabel t; jump f` at the end of a
block) into the function starts a frame of `t`'s call site over the words the caller keeps, which
the checker types statically. A block of the function is entered only by a call, a return or a jump
from a block of the same frame that keeps its height. -/

/-- A recursive function's frames: the function's blocks, and for each label a call to it pushes
(its call site), the types of the words that call keeps below the callee's frame and, for a call
from the function itself, where among them the caller's own return label is. -/
structure Frames where
  blocks : List Nat
  calls : List (Nat × List Ty × Option Nat)
  deriving Repr

namespace Frames

/-- The labels the call sites push. -/
def labs (F : Frames) : List Nat := F.calls.map (·.1)

def site (F : Frames) (t : Nat) : Option (List Ty × Option Nat) :=
  (F.calls.find? (·.1 == t)).map (·.2)

/-- The types of the words the call site of `t` keeps below the callee. -/
def keep (F : Frames) (t : Nat) : List Ty := ((F.site t).map (·.1)).getD []

/-- Where the caller's own return label is among the words the call site of `t` keeps; none for a
call from outside the function. -/
def pos (F : Frames) (t : Nat) : Option Nat := (F.site t).bind (·.2)

/-- Whether block `b` is one of the function's. -/
def isFrame (F : Frames) (b : Nat) : Bool := F.blocks.contains b

end Frames

/-- SolarTV's stack `R` and EthLib's `RT` below a frame whose return label is `L`. -/
inductive FrB (c : Cert) (F : Frames) : Word → List Word → List Word → Prop
  /-- A frame a call from outside the function pushed: below it, the words that call keeps at its
  types, and the rest of the caller's stack, unrelated. -/
  | outer {L : Word} {R RT : List Word} (hl : L.toNat ∈ F.labs) (hp : F.pos L.toNat = none)
      (hlen : (F.keep L.toNat).length ≤ R.length) (hR : SR c (F.keep L.toNat) R RT) :
      FrB c F L R RT
  /-- A frame a call from the function itself pushed: below it, the words that call keeps at its
  types, with the caller's own return label `L'` at `j` among them, over the caller's frames. -/
  | inner {L L' : Word} {R RT : List Word} {j : Nat} (hl : L.toNat ∈ F.labs)
      (hp : F.pos L.toNat = some j) (hlen : (F.keep L.toNat).length ≤ R.length)
      (hR : SR c (F.keep L.toNat) R RT) (hj : j < (F.keep L.toNat).length) (hL' : R[j]? = some L')
      (below : FrB c F L' (R.drop (F.keep L.toNat).length) (RT.drop (F.keep L.toNat).length)) :
      FrB c F L R RT

theorem FrB.base {c : Cert} {F : Frames} {L : Word} {R RT : List Word} (h : FrB c F L R RT) :
    L.toNat ∈ F.labs ∧ (F.keep L.toNat).length ≤ R.length ∧ SR c (F.keep L.toNat) R RT := by
  cases h with
  | outer hl _ hlen hR => exact ⟨hl, hlen, hR⟩
  | inner hl _ hlen hR _ _ _ => exact ⟨hl, hlen, hR⟩

/-- Every word the types `ty` call a label among the top `h` of `S` is the frame's label `L`. -/
def LabsAre (ty : List Ty) (h : Nat) (L : Word) (S : List Word) : Prop :=
  ∀ i (hi : i < h) (hS : i < S.length), tyAt ty i = some true → S[i] = L

/-- What a block of the function is entered with: every label its entry types is its frame's label
`L`, and below the words it needs, the frames. -/
def FrIn (c : Cert) (F : Frames) (b : Nat) (S T : List Word) : Prop :=
  ∃ L, LabsAre (c.entry b) (c.need b) L S ∧ FrB c F L (S.drop (c.need b)) (T.drop (c.need b))

/-- In a block of the function (`fb`), below the height `h` the check tracks the stacks are the
frame's `R` and `RT`, untouched, and every label of the top `h` words is the frame's `L`. -/
def XI (fb : Bool) (L : Word) (R RT : List Word) (h : Nat) (ty : List Ty) (S T : List Word) : Prop :=
  fb = true → S.drop h = R ∧ T.drop h = RT ∧ LabsAre ty h L S

/-! ## The checker with frames -/

/-- A jump or a fall into block `t` with `h` words from a block of the function when `fb`: a block of
the function only from a block of the same frame, with the words it needs the frame's. -/
def frameOk (F : Frames) (c : Cert) (fb : Bool) (t h : Nat) : Bool :=
  !F.isFrame t || (fb && decide (c.need t = h))

def jumpOkF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (fb : Bool) (b t h : Nat)
    (ty : List Ty) : Bool :=
  jumpOkR p c mx hd b t h ty && frameOk F c fb t h

def fallOkF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (fb : Bool) (b h : Nat)
    (ty : List Ty) : Bool :=
  fallOkR p c mx hd b h ty && frameOk F c fb (b + 1) h

/-- The types of the top `n` words, exactly `n` of them. -/
def tyPad (ty : List Ty) (n : Nat) : List Ty := List.ofFn (n := n) fun i => tyAt ty i.val

/-- The only label the types `ty` give among the top `need` words is at `n + j`, for `pos = some j`. -/
def labsAt (ty : List Ty) (need n : Nat) (pos : Option Nat) : Bool :=
  (List.range need).all fun i => tyAt ty i != some true || pos.any fun j => i == n + j

/-- A return from block `b` with `h` words typed `ty`, the frame's label on top, to the label `t` of a
call site: the results (the `h - 1` words below the label) and below them the words the call kept, at
the call's types, meet `t`'s entry; into a block of the function, the words `t` needs end where the
call's kept words do, and the only label they type is the caller's. -/
def retOk (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (b h : Nat) (ty : List Ty)
    (t : Nat) : Bool :=
  decide (t < p.blocks.length) && isTarget p c t && decide (c.need t ≤ h - 1 + (F.keep t).length) &&
    tyLe (tyPad ty.tail (h - 1) ++ F.keep t) (c.entry t) && heightOk mx hd b t (h - 1) (c.need b) &&
    (!F.isFrame t || (decide (c.need t = h - 1 + (F.keep t).length) && (F.pos t).isSome &&
      labsAt (c.entry t) (c.need t) (h - 1) (F.pos t)))

/-- A call into block `f` of the function, with `h` words typed `ty` after the label `t` it pushed:
`t` is a call site's, the callee's only label is its own on top, and the words below the callee's
are the ones `t`'s call keeps, at its types; for a call from the function itself, exactly the
frame's tracked words, with the frame's label where the call site says. -/
def calleeOk (c : Cert) (F : Frames) (fb : Bool) (h : Nat) (ty : List Ty) (t f : Nat) : Bool :=
  F.labs.contains t && decide (1 ≤ c.need f) && labsAt (c.entry f) (c.need f) 0 (some 0) &&
    decide (c.need f + (F.keep t).length ≤ h) && tyLe (ty.drop (c.need f)) (F.keep t) &&
    match F.pos t with
    | none => true
    | some j => fb && decide (c.need f + (F.keep t).length = h) && decide (j < (F.keep t).length) &&
        tyAt ty (c.need f + j) == some true

/-- The last two instructions of a block when they are a call: `pushLabel t; jump f`. -/
def callOf : Assemble.Instr → List Assemble.Instr → Option (Nat × Nat)
  | .pushLabel t, [.jump f] => some (t, f)
  | _, _ => none

/-- A call `pushLabel t; jump f` ending block `b`, from `h` words typed `ty`, with `k` items left. -/
def callOk (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (fb : Bool) (b h : Nat)
    (ty : List Ty) (k t f : Nat) : Bool :=
  decide (1 ≤ k) && c.rets.contains t && decide (t < 2 ^ 32) &&
    (if f = b + 1 then fallOkR p c mx hd b (h + 1) (some true :: ty)
     else decide (3 ≤ k) && jumpOkR p c mx hd b f (h + 1) (some true :: ty)) &&
    (!F.isFrame f || calleeOk c F fb (h + 1) (some true :: ty) t f)

/-- The instructions a block of the function runs besides its jumps: stack operations and ends. -/
def stackOnly : Assemble.Instr → Bool
  | .op (.stack _) | .stop | .ret | .revert => true
  | _ => false

/-- `blockStepR` with frames: jumps by `jumpOkF`, and a dynamic jump in a block of the function a
return to the frame's label (`retOk`); elsewhere, as `blockStepR`, into no block of the function. -/
def blockStepF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (fb : Bool) (b : Nat)
    (ok : Nat → Known → List Ty → Nat → Bool) :
    Nat → Known → List Ty → Nat → Assemble.Instr → Bool
  | h, _, ty, k, .jump t => decide (2 ≤ k) && jumpOkF p c mx hd F fb b t h ty
  | h, _, ty, k, .jumpi t =>
    decide (2 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkF p c mx hd F fb b t (h - 1) ty.tail &&
      ok (h - 1) [] ty.tail (k - 2)
  | h, _, ty, k, .jumpDyn =>
    decide (1 ≤ k) && decide (1 ≤ h) && tyAt ty 0 == some true &&
      (if fb then F.labs.all (retOk p c mx hd F b h ty)
       else c.rets.all fun t => jumpOkR p c mx hd b t (h - 1) ty.tail && !F.isFrame t)
  | h, known, ty, k, i => (!fb || stackOnly i) && blockStepR p c mx hd b ok h known ty k i

/-- `blockOkR` with frames. -/
def blockOkF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (fb : Bool) (b : Nat) :
    Nat → Known → List Ty → Nat → List Assemble.Instr → Bool
  | h, _, ty, _, [] => fallOkF p c mx hd F fb b h ty
  | h, known, ty, k, i :: rest =>
    match turnedElse c b i rest with
    | some e =>
      decide (3 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOkF p c mx hd F fb b e (h - 1) ty.tail &&
        fallOkF p c mx hd F fb b (h - 1) ty.tail
    | none =>
      if dropped p b i rest then
        match i with
        | .stop => true
        | _ => fallOkF p c mx hd F fb b h ty
      else
        match callOf i rest with
        | some (t, f) => callOk p c mx hd F fb b h ty k t f
        | none => blockStepF p c mx hd F fb b
            (fun h known ty k => blockOkF p c mx hd F fb b h known ty k rest) h known ty k i

/-- Every block checks, a block of the function with its frame. -/
def blocksOkF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) :
    Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
      decide (maxH mx b + budget c b ≤ 1000) &&
      blockOkF p c mx hd F (F.isFrame b) b (c.need b) [] (c.entry b) (budget c b - labelItems p c b)
        instrs &&
      blocksOkF p c mx hd F (b + 1) rest

/-- The checker for code with recursion: `checkR` with frames, the first block outside the
function. -/
def checkF (p : Program) (code : ByteArray) (c : Cert) (mx hd : List Nat) (F : Frames) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkF p c mx hd F 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32) && !F.isFrame 0

theorem blocksOkF_get {p : Program} {c : Cert} {mx hd : List Nat} {F : Frames} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat),
    blocksOkF p c mx hd F b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ budget c (b + k) ∧ c.need (b + k) ≤ maxH mx (b + k) ∧
      maxH mx (b + k) + budget c (b + k) ≤ 1000 ∧
      blockOkF p c mx hd F (F.isFrame (b + k)) (b + k) (c.need (b + k)) [] (c.entry (b + k))
        (budget c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOkF, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [and_assoc] using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOkF, Bool.and_eq_true] at h
    have := blocksOkF_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the check the simulation uses at every block. -/
structure GlobF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 32
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ budget c t ∧
    c.need t ≤ maxH mx t ∧ maxH mx t + budget c t ≤ 1000 ∧
    blockOkF p c mx hd F (F.isFrame t) t (c.need t) [] (c.entry t) (budget c t - labelItems p c t)
      p.blocks[t] = true

theorem GlobF.toT {p : Program} {c : Cert} {mx hd : List Nat} {F : Frames} {code : ByteArray}
    (G : GlobF p c mx hd F code) : GlobLT p c code :=
  ⟨G.top_mod, G.top_le, G.size_lt, G.target⟩

theorem globF_of_checkF {p : Program} {code : ByteArray} {c : Cert} {mx hd : List Nat} {F : Frames}
    (h : checkF p code c mx hd F = true) :
    GlobF p c mx hd F code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 ∧
      F.isFrame 0 = false := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, htop⟩, hsize⟩, hf0⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨hmod, htop, hsize, fun t ht htgt => ?_, fun t ht => ?_⟩, hseg, hneed, hf0⟩
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
  · have := blocksOkF_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## Frames through a block -/

theorem labsAre_cons {ty : List Ty} {h : Nat} {L x : Word} {S : List Word} {τ : Ty}
    (hl : LabsAre ty h L S) (hx : τ = some true → x = L) : LabsAre (τ :: ty) (h + 1) L (x :: S) := by
  intro i hi hS ht
  cases i with
  | zero => exact hx (by simpa [tyAt] using ht)
  | succ i =>
    simp only [List.getElem_cons_succ]
    exact hl i (by omega) (by simp at hS; omega) (by simpa [tyAt] using ht)

theorem labsAre_tail {ty : List Ty} {h : Nat} {L x : Word} {S : List Word}
    (hl : LabsAre ty h L (x :: S)) : LabsAre ty.tail (h - 1) L S := by
  intro i hi hS ht
  have := hl (i + 1) (by omega) (by simp; omega) (by rw [← tyAt_tail]; exact ht)
  simpa using this

theorem tyAt_drop (ty : List Ty) (n i : Nat) : tyAt (ty.drop n) i = tyAt ty (n + i) := by
  simp [tyAt, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem labsAre_drop {ty : List Ty} {h : Nat} {L : Word} {S : List Word} (n : Nat) (hn : n ≤ h)
    (hl : LabsAre ty h L S) : LabsAre (ty.drop n) (h - n) L (S.drop n) := by
  intro i hi hS ht
  simp only [List.length_drop] at hS
  rw [tyAt_drop] at ht
  have := hl (n + i) (by omega) (by omega) ht
  simpa [List.getElem_drop] using this

theorem labsAre_le {ty σ : List Ty} {h h' : Nat} {L : Word} {S : List Word} (hl : LabsAre ty h L S)
    (hle : tyLe ty σ = true) (hh : h' ≤ h) : LabsAre σ h' L S := by
  intro i hi hS ht
  refine hl i (by omega) hS ?_
  simp only [tyLe, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hle
  by_cases hiσ : i < σ.length
  · rcases hle i hiσ with he | he
    · rw [he] at ht; cases ht
    · rw [← he]; exact ht
  · have : tyAt σ i = none := by simp [tyAt, List.getD_eq_getElem?_getD, hiσ]
    rw [this] at ht; cases ht

theorem labsAre_dup {ty : List Ty} {h : Nat} {L : Word} {S : List Word} {i : Nat}
    (hl : LabsAre ty h L S) (hi : i + 1 ≤ h) (hiS : i < S.length) :
    LabsAre (tyAt ty i :: ty) (h + 1) L (S[i] :: S) :=
  labsAre_cons hl fun ht => hl i (by omega) hiS ht

theorem labsAre_swap {ty : List Ty} {h : Nat} {L a : Word} {S : List Word} {i : Nat}
    (hl : LabsAre ty h L (a :: S)) (hi : i + 2 ≤ h) (hiS : i < S.length) :
    LabsAre (tySwap ty i) h L (S[i] :: S.set i a) := by
  intro j hj hS ht
  rw [tyAt_tySwap] at ht
  rcases j with _ | j
  · simp only [ite_true] at ht
    have := hl (i + 1) (by omega) (by simp; omega) ht
    simpa using this
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_right_cancel_iff] at ht
    simp only [List.getElem_cons_succ, List.getElem_set]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true] at ht ⊢
      have := hl 0 (by omega) (by simp) ht
      simpa using this
    · simp only [hji, ite_false, Ne.symm hji] at ht ⊢
      have := hl (j + 1) (by omega) (by simp at hS ⊢; omega) ht
      simpa using this

theorem drop_set_lt {α : Type} (l : List α) (i n : Nat) (a : α) (h : i < n) :
    (l.set i a).drop n = l.drop n := by
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    simp only [List.getElem_drop, List.getElem_set]
    split <;> first | omega | rfl

theorem XI.cons {fb : Bool} {L : Word} {R RT : List Word} {h : Nat} {ty : List Ty} {S T : List Word}
    {τ : Ty} {x y : Word} (X : XI fb L R RT h ty S T) (hx : τ = some true → x = L) :
    XI fb L R RT (h + 1) (τ :: ty) (x :: S) (y :: T) := fun hfb => by
  obtain ⟨h1, h2, h3⟩ := X hfb
  exact ⟨by simpa using h1, by simpa using h2, labsAre_cons h3 hx⟩

theorem XI.tail {fb : Bool} {L : Word} {R RT : List Word} {h : Nat} {ty : List Ty} {S T : List Word}
    {x y : Word} (X : XI fb L R RT h ty (x :: S) (y :: T)) (h1 : 1 ≤ h) :
    XI fb L R RT (h - 1) ty.tail S T := fun hfb => by
  obtain ⟨e1, e2, e3⟩ := X hfb
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  exact ⟨by simpa using e1, by simpa using e2, labsAre_tail e3⟩

theorem XI.off {L : Word} {R RT : List Word} {h : Nat} {ty : List Ty} {S T : List Word} :
    XI false L R RT h ty S T := fun hfb => absurd hfb (by decide)

/-- `stack_simR` with the frame: the words below the height the check tracks stay, and a word a stack
operation types a label is one the frame's label already was. -/
theorem stack_simF {p : Program} {c : Cert} {mx hd : List Nat} {bb : Nat}
    {ok : Nat → Known → List Ty → Nat → Bool}
    {h k : Nat} {known : Known} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    {ctx : SolarTV.EVM.Context} {S T : List Word}
    (hok : blockStepR p c mx hd bb ok h known ty k (.op (.stack op)) = true) (hh : h ≤ S.length)
    (hk : KR known S) (hR : SR c ty S T) {fb : Bool} {L : Word} {R0 RT0 : List Word}
    (X : XI fb L R0 RT0 h ty S T) :
    1 ≤ k ∧ ∃ byte, opByte op = some byte ∧ ∃ h' ty' S' T',
      SolarTV.EVM.step ctx op S = some S' ∧ SolarTV.EVM.step ctx op T = some T' ∧
      SR c ty' S' T' ∧ h' ≤ S'.length ∧ S'.length ≤ S.length + 1 ∧ S'.length + h = h' + S.length ∧
      XI fb L R0 RT0 h' ty' S' T' ∧
      ∃ known', KR known' S' ∧ ok h' known' ty' (k - 1) = true := by
  have hL := hR.length
  by_cases hd : ∃ i, op = .dup i
  · obtain ⟨i, rfl⟩ := hd
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x80 + i.val, by simp [opByte, h16], h + 1, _, _, _, ?_, ?_, SR.dup hR hiS hiT,
      by simp; omega, by simp, by simp; omega, fun hfb => ?_, _, hk.dup hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
    · obtain ⟨e1, e2, e3⟩ := X hfb
      exact ⟨by simpa using e1, by simpa using e2, labsAre_dup e3 hi hiS⟩
  by_cases hs : ∃ i, op = .swap i
  · obtain ⟨i, rfl⟩ := hs
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    simp only [List.length_cons] at hh hL
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x90 + i.val, by simp [opByte, h16], h, _, _, _, ?_, ?_, SR.swap hR hiS hiT,
      by simp; omega, by simp, by simp; omega, fun hfb => ?_, [], KR.nil _, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
    · obtain ⟨e1, e2, e3⟩ := X hfb
      refine ⟨?_, ?_, labsAre_swap e3 hi hiS⟩
      · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        simp only [List.drop_succ_cons] at e1 ⊢
        rw [drop_set_lt _ _ _ _ (by omega)]; exact e1
      · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        simp only [List.drop_succ_cons] at e2 ⊢
        rw [drop_set_lt _ _ _ _ (by omega)]; exact e2
  by_cases hp : op = .pop
  · subst hp
    simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, h1⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    refine ⟨hk1, _, rfl, h - 1, _, _, _, rfl, rfl, (SR.uncons.1 hR).2, by simp at hh; omega,
      by simp only [List.length_cons]; omega, by simp at hh ⊢; omega, X.tail h1, [], KR.nil _, hok⟩
  have hd' : ∀ i, op ≠ .dup i := fun i e => hd ⟨i, e⟩
  have hs' : ∀ i, op ≠ .swap i := fun i e => hs ⟨i, e⟩
  rw [blockStepR_stack hne hd' hs' hp] at hok
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
    have hh' : (h + d).toNat = h - need + 1 := by omega
    refine ⟨hk1, byte, hbyte, (h + d).toNat, _, _, _, hstep, hstepT,
      SR.cons (τ := some false) rfl (SR.drop need hR), ?_, ?_, ?_, fun hfb => ?_, _,
      (hk.drop need).cons_none _, hok⟩
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
    · obtain ⟨e1, e2, e3⟩ := X hfb
      rw [hh']
      refine ⟨?_, ?_, labsAre_cons (labsAre_drop need hneed e3) (fun h => absurd h (by decide))⟩
      · simp only [List.drop_succ_cons, List.drop_drop]
        rw [show need + (h - need) = h by omega]; exact e1
      · simp only [List.drop_succ_cons, List.drop_drop]
        rw [show need + (h - need) = h by omega]; exact e2
  · cases hok


/-! ## The simulation of a block with frames -/

/-- `SimOutR` with frames: a block of the function is entered with its frame (`FrIn`). -/
def SimOutF (p : Program) (c : Cert) (mx hd : List Nat) (F : Frames) (code : ByteArray)
    (call : SolarTV.Call) (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState)
    (ss : Substate) (b R pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧
      (t < p.blocks.length → c.need t ≤ S'.length ∧ (hd.contains t = false → S'.length ≤ maxH mx t)) ∧
      (t = b + 1 ∨ isTarget p c t = true)) ∧
      ∃ pc' T' M' g' st' ss', HoareG .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧
        (F.isFrame t = true → FrIn c F t S' T') ∧
        EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R pc' s' M' g' ∧
        Rel msg ss0 st' ss' s'

theorem SimOutF.pre {p : Program} {c : Cert} {mx hd : List Nat} {F : Frames} {code : ByteArray}
    {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutF p c mx hd F code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 r) :
    SimOutF p c mx hd F code call msg ss0 st ss b R pc T M g r := by
  match r, h1 with
  | .inl (_, _), hspec => exact SpecG.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hfr, hinv, hrel⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hfr, hinv, hrel⟩

/-- A jump or a fall from a block of the frame into one, the stacks as they are. -/
theorem frIn_jump {c : Cert} {F : Frames} {fb : Bool} {Lf : Word} {R0 RT0 : List Word} {h : Nat}
    {ty : List Ty} {S T : List Word} {t : Nat} (hF : fb = true → FrB c F Lf R0 RT0)
    (X : XI fb Lf R0 RT0 h ty S T) (hok : frameOk F c fb t h = true)
    (hty : tyLe ty (c.entry t) = true) : F.isFrame t = true → FrIn c F t S T := by
  intro hft
  simp only [frameOk, hft, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hfb, hn⟩ := hok
  obtain ⟨e1, e2, e3⟩ := X hfb
  exact ⟨Lf, labsAre_le e3 hty (by omega), by rw [hn, e1, e2]; exact hF hfb⟩

theorem tyPad_length (ty : List Ty) (n : Nat) : (tyPad ty n).length = n := by simp [tyPad]

theorem tyAt_tyPad_lt {ty : List Ty} {n i : Nat} (kt : List Ty) (hi : i < n) :
    tyAt (tyPad ty n ++ kt) i = tyAt ty i := by
  have hl : i < (tyPad ty n).length := by rw [tyPad_length]; exact hi
  unfold tyAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
  simp [tyPad, hi, tyAt]

theorem tyAt_tyPad_ge {ty : List Ty} {n i : Nat} (kt : List Ty) (hi : n ≤ i) :
    tyAt (tyPad ty n ++ kt) i = tyAt kt (i - n) := by
  have hl : (tyPad ty n).length ≤ i := by rw [tyPad_length]; exact hi
  unfold tyAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hl, tyPad_length,
    List.getD_eq_getElem?_getD]

/-- The results' types over the frame's below them. -/
theorem SR.pad_append {c : Cert} {ty kt : List Ty} {S T : List Word} {n : Nat} (hR : SR c ty S T)
    (hk : SR c kt (S.drop n) (T.drop n)) : SR c (tyPad ty n ++ kt) S T := by
  refine ⟨hR.1, fun i h1 h2 => ?_⟩
  by_cases hi : i < n
  · rw [tyAt_tyPad_lt kt hi]; exact hR.2 i h1 h2
  · rw [tyAt_tyPad_ge kt (by omega)]
    have := hk.2 (i - n) (by simp; omega) (by simp; omega)
    simpa [List.getElem_drop, show n + (i - n) = i by omega] using this

/-- A return to the frame's label, a call site of the function's own: the caller's frame. -/
theorem frIn_ret {c : Cert} {F : Frames} {Lf : Word} {R0 RT0 : List Word} {n : Nat}
    {S1 T1 : List Word} (hF : FrB c F Lf R0 RT0) (hS : S1.drop n = R0) (hT : T1.drop n = RT0)
    (hneed : c.need Lf.toNat = n + (F.keep Lf.toNat).length)
    (hpos : (F.pos Lf.toNat).isSome = true)
    (hlabs : labsAt (c.entry Lf.toNat) (c.need Lf.toNat) n (F.pos Lf.toNat) = true) :
    FrIn c F Lf.toNat S1 T1 := by
  cases hF with
  | outer _ hp _ _ => rw [hp] at hpos; cases hpos
  | @inner _ L' _ _ j _ hp hlen _ hj hL' below =>
    refine ⟨L', fun i hi hiS ht => ?_, ?_⟩
    · simp only [labsAt, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
        hp, Option.any_some, beq_iff_eq] at hlabs
      rcases hlabs i hi with h0 | rfl
      · exact absurd ht h0
      · rw [← hS] at hL'
        rw [List.getElem?_drop, List.getElem?_eq_getElem hiS] at hL'
        exact Option.some.inj hL'
    · rw [hneed, ← List.drop_drop, ← List.drop_drop, hS, hT]
      exact below

/-- A call from a block of the function or from outside it into the function's block `f`: the
callee's frame. -/
theorem frIn_call {c : Cert} {F : Frames} {fb : Bool} {Lf : Word} {R0 RT0 : List Word} {h : Nat}
    {ty : List Ty} {S T : List Word} {t f : Nat} (hF : fb = true → FrB c F Lf R0 RT0)
    (X : XI fb Lf R0 RT0 h ty S T) (hR : SR c (some true :: ty) (BitVec.ofNat 256 t :: S)
      (BitVec.ofNat 256 (c.offset t) :: T)) (hh : h ≤ S.length) (ht32 : t < 2 ^ 32)
    (hok : calleeOk c F fb (h + 1) (some true :: ty) t f = true) :
    FrIn c F f (BitVec.ofNat 256 t :: S) (BitVec.ofNat 256 (c.offset t) :: T) := by
  have htn : (BitVec.ofNat 256 t).toNat = t := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [calleeOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
  obtain ⟨⟨⟨⟨⟨hl, h1⟩, hlabs⟩, hle⟩, hty⟩, hpos⟩ := hok
  have hlab : LabsAre (c.entry f) (c.need f) (BitVec.ofNat 256 t) (BitVec.ofNat 256 t :: S) := by
    intro i hi hS ht
    simp only [labsAt, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Option.any_some, beq_iff_eq, Nat.zero_add] at hlabs
    rcases hlabs i hi with h0 | rfl
    · exact absurd ht h0
    · rfl
  have hkR : SR c (F.keep t) ((BitVec.ofNat 256 t :: S).drop (c.need f))
      ((BitVec.ofNat 256 (c.offset t) :: T).drop (c.need f)) := SR.le hty (SR.drop _ hR)
  have hlen : (F.keep t).length ≤ ((BitVec.ofNat 256 t :: S).drop (c.need f)).length := by
    simp; omega
  refine ⟨_, hlab, ?_⟩
  cases hp : F.pos t with
  | none =>
    exact FrB.outer (by rw [htn]; exact hl) (by rw [htn]; exact hp) (by rw [htn]; exact hlen)
      (by rw [htn]; exact hkR)
  | some j =>
    rw [hp] at hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpos
    obtain ⟨⟨⟨hfb, hsum⟩, hj⟩, hlj⟩ := hpos
    obtain ⟨e1, e2, e3⟩ := X hfb
    obtain ⟨m, hm⟩ : ∃ m, c.need f + j = m + 1 := ⟨c.need f + j - 1, by omega⟩
    have hmS : m < S.length := by omega
    have hLf : S[m] = Lf := e3 m (by omega) hmS (by rw [hm, tyAt] at hlj; simpa [tyAt] using hlj)
    refine FrB.inner (L' := Lf) (j := j) (by rw [htn]; exact hl) (by rw [htn]; exact hp)
      (by rw [htn]; exact hlen) (by rw [htn]; exact hkR) (by rw [htn]; exact hj) ?_ ?_
    · rw [List.getElem?_drop, hm, List.getElem?_cons_succ, List.getElem?_eq_getElem hmS, hLf]
    · rw [htn, List.drop_drop, List.drop_drop, hsum]
      simp only [List.drop_succ_cons]
      rw [e1, e2]
      exact hF hfb

theorem callOf_some {i : Assemble.Instr} {rest : List Assemble.Instr} {t f : Nat}
    (h : callOf i rest = some (t, f)) : i = .pushLabel t ∧ rest = [.jump f] := by
  unfold callOf at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h

theorem drop_cons_pred {α : Type} {x : α} {S : List α} {h : Nat} (h1 : 1 ≤ h) :
    (x :: S).drop h = S.drop (h - 1) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  simp

open SolarTV.EVM.Program in
/-- `exec_simR` with frames: in a block of the function (`fb`), from the frame `FrB c F Lf R0 RT0` below
the height the check tracks, a block of the function the block jumps to, falls into, calls or returns
to is entered with its frame (`FrIn`). -/
theorem exec_simF {p : Assemble.Program} {c : Cert} {mx hd : List Nat} {F : Frames} {code : ByteArray}
    (G : GlobLT p c code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    {a : Nat} (hcaller : msg.caller = Target.address a) (ho : c.env = true → OracleOkAt a o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : c.reads = true → msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (b : Nat) (hb : b < p.blocks.length) (Rv : Nat) (fb : Bool) (Lf : Word) (R0 RT0 : List Word)
    (hF : fb = true → FrB c F Lf R0 RT0) :
    ∀ (is : List Assemble.Instr) (h : Nat) (known : Known) (ty : List Ty) (S T : List Word) (k : Nat)
      (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate),
      blockOkF p c mx hd F fb b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S T →
      InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k Rv
        pc S s M g → Rel msg ss0 st ss s → XI fb Lf R0 RT0 h ty S T →
      SimOutF p c mx hd F code call msg ss0 st ss b Rv pc T M g (exec o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, _, hR, I, R, X => by
    simp only [blockOkF, fallOkF, fallOkR, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hfall, hfty⟩, hcost⟩, hfr⟩ := hok
    have I2 := I.entry
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [exec, SimOutF]
    exact ⟨⟨by omega, fun ht => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, by simp⟩,
      pc, T, M, g, st, ss, Triple.of_imp fun _ h => h, SR.le hfty hR, frIn_jump hF X hfr hfty, I2, R⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R, X => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOkF, hT, jumpOkF, jumpOkR, fallOkF, fallOkR, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, hefr⟩, ⟨⟨hfall, hfty⟩, hcost'⟩, hffr⟩ := hok
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
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOutF]
        exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr hetgt⟩, c.offset e, T', M, g1 - 10, st,
          ss, Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR', frIn_jump hF (X.tail h1) hefr hety,
          I.target G hen hetgt (m := 3) (by omega) (by omega), R⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOutF]
        refine ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost' hn; omega⟩, by simp⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR', frIn_jump hF (X.tail h1) hffr hfty,
          ⟨hseg, ?_, I.le_top, I.mem⟩, R⟩
        have := I.gas
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOkF, hT, hD, ite_true, fallOkF, fallOkR, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          obtain ⟨⟨⟨hfall, hfty⟩, hcost⟩, hfr⟩ := hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutF]
          exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, by simp⟩, pc, T, M, g, st, ss,
            Triple.of_imp fun _ h => h, SR.le hfty hR, frIn_jump hF X hfr hfty, I.entry, R⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [exec, SimOutF]
          exact SpecG.consequence (stop_of_size_leG (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      have I' : InvL c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      rcases hC : callOf i rest with _ | ⟨t0, f0⟩
      rotate_left
      · -- A call: pushLabel t0; jump f0, the label a PUSH of its block's offset.
        obtain ⟨rfl, rfl⟩ := callOf_some hC
        have hok' : callOk p c mx hd F fb b h ty k t0 f0 = true := by
          simpa only [blockOkF, hT, hD', hC, Bool.false_eq_true, ite_false] using hok
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok'
        obtain ⟨⟨⟨⟨hk1, hmem⟩, ht32⟩, hjmp⟩, hcallee⟩ := hok'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd1, hseg⟩ := I'.seg.head
        simp only [Item.expected] at hd1
        have hS := I'.stack; have hG := I'.gas
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd1 (by omega) (by omega)
        have htn : (BitVec.ofNat 256 t0).toNat = t0 := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hR1 : SR c (some true :: ty) (BitVec.ofNat 256 t0 :: S)
            (BitVec.ofNat 256 (c.offset t0) :: T) :=
          SR.cons ⟨by rw [htn]; exact hmem, by rw [htn]⟩ hR
        have hfr : F.isFrame f0 = true → FrIn c F f0 (BitVec.ofNat 256 t0 :: S)
            (BitVec.ofNat 256 (c.offset t0) :: T) := by
          intro hf
          simp only [hf, Bool.not_true, Bool.false_or] at hcallee
          exact frIn_call hF X hR1 hh ht32 hcallee
        have I1 := I'.next (S' := BitVec.ofNat 256 t0 :: S) (g' := g1) hk1 hseg (by simp) (by omega)
        simp only [exec, List.length_cons, show ¬ S.length + 1 > 1024 by omega,
          show ¬ S.length + 1 + 1 > 1024 by omega, ite_false]
        refine SimOutF.pre hpush ?_
        by_cases hf : f0 = b + 1
        · -- The jump to the next block, left out: the code falls into the callee.
          subst hf
          simp only [ite_true, fallOkR, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hjmp
          obtain ⟨⟨hfall, hfty⟩, hcost⟩ := hjmp
          have hdr : dropped p b (.jump (b + 1)) [] = true := by simp [dropped]
          simp only [lowerInstrs, turnedElse, hdr, ite_true, List.nil_append] at I1
          have hS1 := I1.stack
          simp only [SimOutF]
          exact ⟨⟨by omega, fun _ => ⟨by simp only [List.length_cons]; omega,
            fun hn => by have := heightOk_le hcost hn; simp only [List.length_cons]; omega⟩, by simp⟩,
            next, _, M, g1, st, ss, Triple.of_imp fun _ h => h, SR.le hfty hR1, hfr, I1.entry, R⟩
        · simp only [hf, ite_false, jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hjmp
          obtain ⟨hk3, ⟨⟨⟨⟨htn', htgt⟩, hneed⟩, hty⟩, hcost⟩⟩ := hjmp
          have hdr : dropped p b (.jump f0) [] = false := by simp [dropped, hf]
          simp only [lowerInstrs, turnedElse, hdr, Bool.false_eq_true, ite_false, lowerInstr,
            List.cons_append, List.nil_append, List.append_nil] at I1
          obtain ⟨n1, hd2, hs1⟩ := I1.seg.head
          obtain ⟨hlt2, hcode2, -⟩ := op_seg hs1
          simp only [Item.expected] at hd2
          have hS1 := I1.stack; have hG1 := I1.gas
          have hoff := toNat_offset (G.target f0 htn' htgt).2.1 G.size_lt
          obtain ⟨g2, hg2, hpush2⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss)
            (gas := g1) (stack := BitVec.ofNat 256 (c.offset t0) :: T) hd2 (by omega)
            (by simp only [List.length_cons]; omega)
          have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (rest := BitVec.ofNat 256 (c.offset t0) :: T) hlt2 hcode2
            (show 8 ≤ g2 by omega) (by rw [hoff]; exact (G.target f0 htn' htgt).1)
          rw [hoff] at hj
          simp only [SimOutF]
          exact ⟨⟨by omega, fun _ => ⟨by simp only [List.length_cons]; omega,
            fun hn => by have := heightOk_le hcost hn; simp only [List.length_cons]; omega⟩,
            Or.inr htgt⟩, c.offset f0, _, M, g2 - 8, st, ss, Triple.seq hpush2 hj, SR.le hty hR1, hfr,
            I1.target G htn' htgt (m := 2) (by omega) (by omega), R⟩
      have hokF : blockStepF p c mx hd F fb b (fun h known ty k => blockOkF p c mx hd F fb b h known ty k rest)
          h known ty k i = true := by
        simpa only [blockOkF, hT, hD', hC, Bool.false_eq_true, ite_false] using hok
      clear hok hD hD' hT hC
      have IH := exec_simF (mx := mx) (hd := hd) (F := F) (o := o) (ss0 := ss0) G hdata hvalue hstatic
        hself hcaller ho hbenv htx he b hb Rv fb Lf R0 RT0 hF rest
      -- An effect that pushes one word on both stacks for 2 gas and keeps the rest.
      have push2 : ∀ {e : SolarTV.Machine.Effect} {byte : Nat} {w : Word} {known' : Known},
          SolarTV.Machine.Effect.apply o call e [] s = some (some w, s) → KR known' (w :: S) →
          InvL c code call (.op byte :: (lowerInstrs p c b rest ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g → 1 ≤ k →
          blockOkF p c mx hd F fb b (h + 1) known' (some false :: ty) (k - 1) rest = true →
          XI fb Lf R0 RT0 (h + 1) (some false :: ty) (w :: S) (w :: T) →
          (∀ hlt : pc < code.size, code[pc] = UInt8.ofNat byte → 2 ≤ g → T.length < STACK_LIMIT →
            HoareG .fusaka (At code msg pc T M g st ss .empty)
              (At code msg (pc + 1) (w :: T) M (g - 2) st ss .empty)) →
          SimOutF p c mx hd F code call msg ss0 st ss b Rv pc T M g
            (exec o call b (.effect e 0 :: rest) S s) := by
        intro e byte w known' happ hkn I' hk1 hok hX hrule
        obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        rw [exec_effect0 happ (by omega)]
        exact SimOutF.pre (hrule hlt hcode (by omega) (by unfold STACK_LIMIT; omega))
          (IH (h + 1) known' _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok (by simp; omega)
            (by hu_tac) hkn (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R hX)
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      -- The check refuses the instructions outside the fragment.
      all_goals try (simp [blockStepF, blockStepR] at hokF; done)
      · have hok' : blockStepR p c mx hd b (fun h known ty k => blockOkF p c mx hd F fb b h known ty k rest)
            h known ty k (.op mop) = true := by
          simp only [blockStepF, Bool.and_eq_true] at hokF; exact hokF.2
        have hso : fb = true → stackOnly (.op mop) = true := by
          intro hfb
          simp only [blockStepF, hfb, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hokF
          exact hokF.1
        rcases mop with sop | _ | _ | _ | _ | _ | _ <;> try (simp [blockStepR] at hok'; done)
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [exec_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOutF.pre hpush (IH (h + 1) (some v :: known) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega) (by hu_tac)
              (hk.cons_some v)
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R
              (X.cons fun h => absurd h (by decide)))
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', hlock, X', known',
              hkn, hok⟩ := stack_simF (ctx := context o call s) hne hok' hh hk hR X
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨hlt, hcode, hseg⟩ := op_seg I'.seg
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_ruleG (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            rw [exec_stack hstep (by omega) (by omega)]
            exact SimOutF.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega)
              (by hu_tac) hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R X')
        · -- MLOAD.
          obtain rfl : fb = false := by cases fb; rfl; exact absurd (hso rfl) (by simp [stackOnly])
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutF.pre hrule (IH h [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok' (by simp; omega)
            (by hu_tac) (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'))
            ⟨hseg, by simp; omega, ?_, by rw [hM']; omega, memRel_expand I'.mem hbound⟩
            ⟨R.storage, R.account, R.logs⟩ XI.off)
          rw [hM']; omega
        · -- MSTORE.
          obtain rfl : fb = false := by cases fb; rfl; exact absurd (hso rfl) (by simp [stackOnly])
          rcases known with _ | ⟨_ | ow, known'⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutF.pre (Logic.mstoreG (start := ow) (value := v) (rest := T') (memory := M)
            (gas := g) hlt hcode (by omega)) (IH (h - 2) _ _ S' T' (k - 1) _ (pc + 1) _ _ st ss hok'
            (by omega) (by hu_tac) (hk.drop 2) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega, hmem'⟩
            ⟨R.storage, R.account, R.logs⟩ XI.off)
          rw [hM']; omega
      · have hok' : blockStepR p c mx hd b (fun h known ty k => blockOkF p c mx hd F fb b h known ty k rest)
            h known ty k (.effect e ar) = true := by
          simp only [blockStepF, Bool.and_eq_true] at hokF; exact hokF.2
        obtain rfl : fb = false := by
          cases fb
          · rfl
          · simp [blockStepF, stackOnly] at hokF
        rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | name | _
        all_goals try (simp [blockStepR] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutF.pre hrule ?_
          have hreads := fun k : Word => State.TransactionState.recordStorageRead_reads st
            msg.currentTarget msg.currentTarget (U256.toBeBytes x) (U256.toBeBytes k) default
          refine IH h [] _ _ _ (k - 1) s (pc + 1) M _ _ _ hok (by simp; omega) (by hu_tac) (KR.nil _)
            (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by split <;> omega))
            ⟨fun k => ?_, ?_, R.logs⟩ XI.off
          · rw [(hreads k).2.1]
            exact R.storage k
          · rw [(hreads x).1]
            exact R.account
        · -- SSTORE.
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutF.pre hrule ?_
          refine IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) M _ _ _ hok (by omega) (by hu_tac) (KR.nil _)
            hR' ?_ ⟨fun k => ?_, by rw [hacc]; exact R.account, R.logs⟩ XI.off
          · exact ⟨hseg, by omega, by omega, I'.le_top, I'.mem⟩
          by_cases hk : k = x
          · subst hk
            rw [hnew]
            simp [SolarTV.Machine.update]
          · rw [hothers _ _ (Or.inr fun he => hk (U256.toBeBytes_inj he)), R.storage k]
            simp [SolarTV.Machine.update, hk]
        · -- CALLDATALOAD.
          rcases ar with _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
          exact SimOutF.pre hrule (IH h _ _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega) (by hu_tac)
            ((hk.drop 1).cons_none _) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R XI.off)
        · -- CALLDATASIZE.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.calldata.size) rfl (KR.nil _) I' hok'.1 hok'.2 XI.off
            fun hlt hcode hg hs => by rw [← hdata]; exact Logic.calldatasizeG hlt hcode hg hs
        · -- CALLVALUE.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 call.callvalue) rfl (KR.nil _) I' hok'.1 hok'.2 XI.off
            fun hlt hcode hg hs => by rw [← hvalue]; exact Logic.callvalueG hlt hcode hg hs
        · -- CALLER.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          exact push2 (w := o.caller.setWidth 256) rfl (hk.cons_none _) I' hk1 hok XI.off
            fun hlt hcode hg hs => by
              rw [(ho henv).1, ← hcaller]; exact Logic.callerG hlt hcode hg hs
        · -- ADDRESS.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          exact push2 (w := BitVec.ofNat 256 SolarTV.environment.callee) rfl (KR.nil _) I' hok'.1
            hok'.2 XI.off fun hlt hcode hg hs => by
              rw [← address_word, ← hself]; exact Logic.addressG hlt hcode hg hs
        · -- LOGn.
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
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
          refine SimOutF.pre hrule (IH (h - (tops.length + 2)) [] _ S2 T2 (k - 1) _ (pc + 1) _ _ st _
            hok (by omega) (by hu_tac) (KR.nil _) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega,
            memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, ?_⟩ XI.off)
          · rw [hM']; omega
          · refine ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy)
                ow.toNat sw.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, ?_⟩⟩
            exact read_eq I'.mem
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar <;> try (simp [blockStepR] at hok'; done)
          rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨henv, hk1⟩, h2⟩, hdat⟩, hin⟩, hkc⟩, hok⟩ := hok'
          obtain ⟨x, y, S', T', rfl, rfl, hR'⟩ := sr_data2 hR hdat (kr_two_le hk)
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
          refine SimOutF.pre hrule (IH (h - 1) [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok
            (by simp; omega) (by hu_tac) (KR.nil _) (SR.cons (τ := some false) rfl hR') ⟨hseg, by simp; omega, ?_,
            by rw [hM']; omega, memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, R.logs⟩ XI.off)
          rw [hM']; omega
        · -- An environment read of the block or the transaction.
          rcases ar with _ | ar <;> try (simp [blockStepR] at hok'; done)
          simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hreads, hsome⟩, hk1⟩, hok⟩ := hok'
          obtain ⟨⟨byte, w⟩, hread⟩ := Option.isSome_iff_exists.1 hsome
          simp only [lowerInstr, hread, Option.map_some, Option.getD_some,
            List.singleton_append] at I'
          exact push2 (w := BitVec.ofNat 256 w)
            (by simp [SolarTV.Machine.Effect.apply, he hreads name byte w hread]) (KR.nil _) I' hk1 hok XI.off
            fun hlt hcode hg hs => env_readG hread hlt hcode hbenv (htx hreads) hg hs
      · -- JUMP.
        simp only [blockStepF, jumpOkF, jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hokF
        obtain ⟨hk2, ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hfr⟩⟩ := hokF
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
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutF]
        exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr htgt⟩,
          c.offset t, T, M, g1 - 8, st, ss, Triple.seq hpush hj, SR.le hty hR, frIn_jump hF X hfr hty,
          I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- JUMPI.
        simp only [blockStepF, jumpOkF, jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hokF
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hfr⟩⟩, hok'⟩ := hokF
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
          exact SimOutF.pre (Triple.seq hpush hj) (IH (h - 1) [] _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (by hu_tac) (KR.nil _) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R (X.tail h1))
        · have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOutF]
          exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩, Or.inr htgt⟩,
            c.offset t, T', M, g1 - 10, st, ss, Triple.seq hpush hj, SR.le hty hR',
            frIn_jump hF (X.tail h1) hfr hty, I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- A pushed return label outside the function: a PUSH of the block's offset.
        have hok' : blockStepR p c mx hd b (fun h known ty k => blockOkF p c mx hd F fb b h known ty k rest)
            h known ty k (.pushLabel t) = true := by
          simp only [blockStepF, Bool.and_eq_true] at hokF; exact hokF.2
        obtain rfl : fb = false := by
          cases fb
          · rfl
          · simp [blockStepF, stackOnly] at hokF
        simp only [blockStepR, Bool.and_eq_true, decide_eq_true_eq] at hok'
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
        exact SimOutF.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega)
          (by hu_tac) (KR.nil _) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R XI.off)
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStepF, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hokF
        obtain ⟨⟨⟨hk1, h1⟩, hlab⟩, hdyn⟩ := hokF
        rcases S with _ | ⟨x, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨y, T'⟩
        · simp at hL
        obtain ⟨hw, hR'⟩ := SR.uncons.1 hR
        rw [hlab] at hw
        obtain ⟨hmem, rfl⟩ := hw
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        cases fb with
        | false =>
          -- Outside the function: to any pushed label, none of the function's.
          simp only [Bool.false_eq_true, ite_false, List.all_eq_true, Bool.and_eq_true,
            Bool.not_eq_true'] at hdyn
          obtain ⟨hj', hnf⟩ := hdyn _ hmem
          simp only [jumpOkR, Bool.and_eq_true, decide_eq_true_eq] at hj'
          obtain ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩ := hj'
          have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
          have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
            hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
          rw [hoff] at hj
          simp only [exec, SimOutF]
          exact ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩,
            Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st, ss, hj, SR.le hty hR',
            fun hf => absurd hf (by rw [hnf]; decide), I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
        | true =>
          -- A return: to the frame's label, the results over the words its call kept.
          simp only [ite_true, List.all_eq_true] at hdyn
          have hall := hdyn
          obtain ⟨e1, e2, e3⟩ := X rfl
          have hxL : x = Lf := by
            have := e3 0 (by omega) (by simp) (by simpa [tyAt] using hlab)
            simpa using this
          subst hxL
          have hFr := hF rfl
          obtain ⟨hlabs, hklen, hkR⟩ := hFr.base
          have hr := hall _ hlabs
          simp only [retOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
            Bool.not_eq_true'] at hr
          obtain ⟨⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩, hfrm⟩ := hr
          have hS1 : S'.drop (h - 1) = R0 := by rw [← drop_cons_pred h1]; exact e1
          have hT1 : T'.drop (h - 1) = RT0 := by rw [← drop_cons_pred h1]; exact e2
          have hlenR : R0.length = S'.length - (h - 1) := by rw [← hS1]; simp
          have hSR : SR c (c.entry x.toNat) S' T' :=
            SR.le hty (SR.pad_append hR' (by rw [hS1, hT1]; exact hkR))
          have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
          have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
            hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
          rw [hoff] at hj
          simp only [exec, SimOutF]
          refine ⟨⟨by omega, fun _ => ⟨by omega, fun hn => by have := heightOk_le hcost hn; omega⟩,
            Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st, ss, hj, hSR, fun hf => ?_,
            I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
          rcases hfrm with h0 | ⟨⟨hn, hs⟩, hla⟩
          · rw [hf] at h0; cases h0
          · exact frIn_ret hFr hS1 hT1 hn hs hla
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        simp only [exec, SimOutF]
        exact SpecG.consequence (Logic.stopG hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      -- RETURN and REVERT: two known data words, a range within the certificate's bound.
      all_goals
        simp only [blockStepF, stackOnly, Bool.or_true, Bool.true_and] at hokF
        have hok' := hokF
        rcases known with _ | ⟨_ | ow, _ | ⟨_ | sw, known'⟩⟩ <;> try (simp [blockStepR] at hok'; done)
        simp only [blockStepR, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        obtain ⟨x, y, S', T', rfl, rfl, -⟩ := sr_data2 hR hdat (kr_two_le hk)
        obtain ⟨rfl, hk'⟩ := KR.head hk
        obtain ⟨rfl, -⟩ := KR.head hk'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨hlt, hcode, -⟩ := op_seg I'.seg
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
      · simp only [exec, SolarTV.EVM.Program.output, SimOutF, Bool.false_eq_true, ↓reduceIte]
        exact SpecG.consequence (return_postSG (ss := ss) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl (R.slot hself)) (fun _ h => h)
          (fun _ h => ⟨ss, h, R.logs⟩)
      · simp only [exec, SolarTV.EVM.Program.output, SimOutF, ↓reduceIte]
        exact SpecG.consequence (revert_postSG (ss := ss) (by decide) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h) (fun _ h => ⟨ss, h, R.logs⟩)
/-! ## The run -/

open SolarTV.EVM.Program in
/-- `run_simR` with frames: `run_simL` for the checker with heads: EthLib runs the code from a block's offset as SolarTV runs
the program from that block, over steps monotone in gas, with gas for `fuel` blocks of the run, for
the configurations of a set `reach` closed under the program's steps, at whose heads the stack is
at most the head's highest entry (`hhead`). -/
theorem run_simF {p : Assemble.Program} {c : Cert} {mx hd : List Nat} {F : Frames} {code : ByteArray}
    (G : GlobF p c mx hd F code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (reach : Nat × List Word × SolarTV.Machine.State → Prop)
    (hclosed : ∀ x y, reach x → block o call p x = some (.inr y) → reach y)
    (hhead : ∀ x, reach x → x.1 < p.blocks.length → hd.contains x.1 = true →
      x.2.1.length ≤ maxH mx x.1) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      reach (b, S, s) → b ≤ p.blocks.length →
      (b < p.blocks.length → c.need b ≤ S.length ∧ (hd.contains b = false → S.length ≤ maxH mx b)) →
      SR c (c.entry b) S T → (b < p.blocks.length → F.isFrame b = true → FrIn c F b S T) →
      EntryL c code call (lowerFrom p c b (p.blocks.drop b)) (fuel * bmax c) pc s M g →
      Rel msg ss0 st ss s →
      (∀ r, SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = some r →
        SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)) ∧
      (SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = none →
        Triple (StepG .fusaka) (At code msg pc T M g st ss .empty)
          (fun z => 2 * ((p.blocks.length + 2) * z.gas) + fuel ≤ meas p c g b))
  | 0, b, S, T, s, pc, M, g, st, ss, _, _, _, _, _, _, _ => by
    refine ⟨fun r hr => by simp [SolarTV.Machine.iterate] at hr, fun _ evm hp => ⟨evm, Reaches.refl _, ?_⟩⟩
    obtain ⟨-, -, -, -, -, -, hg, -⟩ := hp
    rw [hg]
    unfold meas
    omega
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hreach, hle, hneed, hR, hfr, E, R => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
      obtain ⟨hn, hm'⟩ := hneed hb
      -- The entry height: a static one, or at a head the run's.
      have hm : S.length ≤ maxH mx b := by
        cases hc : hd.contains b
        · exact hm' hc
        · exact hhead (b, S, s) hreach hb hc
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
          obtain ⟨next, hd', hseg⟩ := E'.seg.head
          simp only [Item.expected] at hd'
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd'
          exact ⟨pc + 1, g - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
            ⟨hseg, by omega, by omega, E'.le_top, E'.mem⟩⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
            ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
      have hsim : SimOutF p c mx hd F code call msg ss0 st ss b (fuel * bmax c) pc1 T M g1
          (exec o call b p.blocks[b] S s) := by
        cases hfb : F.isFrame b with
        | false =>
          rw [hfb] at hblock
          exact exec_simF (F := F) (o := o) G.toT hdata hvalue hstatic hself hcaller ho hbenv
            (fun _ => htx) he b hb (fuel * bmax c) false 0 [] [] (fun h => absurd h (by decide))
            p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
            (KR.nil _) hR I1 R XI.off
        | true =>
          rw [hfb] at hblock
          obtain ⟨Lf, hlab, hFr⟩ := hfr hb hfb
          exact exec_simF (F := F) (o := o) G.toT hdata hvalue hstatic hself hcaller ho hbenv
            (fun _ => htx) he b hb (fuel * bmax c) true Lf (S.drop (c.need b)) (T.drop (c.need b))
            (fun _ => hFr) p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn
            (by omega) (KR.nil _) hR I1 R (fun _ => ⟨rfl, rfl, hlab⟩)
      have hstep : block o call p (b, S, s) = some (exec o call b p.blocks[b] S s) := by
        simp only [block, hblk]
      simp only [SolarTV.Machine.iterate, block, hblk]
      generalize exec o call b p.blocks[b] S s = x at hsim hstep
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', hfr', E', R'⟩ := hsim
        have IH := run_simF G hdata hvalue hstatic hself hcaller ho hbenv htx he reach hclosed hhead
          fuel t S' T' s' pc' M' g' st' ss' (hclosed _ _ hreach hstep) htle hneedt hR' (fun _ => hfr') E' R'
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



/-! ## What the check with frames gives -/

/-- **The forward assembly theorem for code with recursion, with frames**: `forward_of_checkR` for
`checkF`, whose dynamic jumps in the recursive function return through the frames. -/
theorem forward_of_checkF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    {F : Frames} (hc : checkF p code c mx hd F = true) (o : SolarTV.Machine.Oracle)
    (ho : c.env = true → OracleOk o) (he : c.reads = true → EnvOk o) (call : SolarTV.Call)
    (heads : HeadsOk o call p mx hd) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hneed0, hf0⟩ := globF_of_checkF hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine run_of_rel_with code call r.2 r.1 gas fun st R => ?_
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; unfold gasBoundL at hg; omega, by simp,
      memRel_initial⟩
  let reach : Nat × List Word × SolarTV.Machine.State → Prop := fun x =>
    ∃ k, SolarTV.CutPoint.steps (SolarTV.EVM.Program.block o call p) k
      (0, [], SolarTV.Machine.State.initial call) = some (.inr x)
  have hclosed : ∀ x y, reach x → SolarTV.EVM.Program.block o call p x = some (.inr y) → reach y :=
    fun _ _ ⟨k, hk⟩ hs => ⟨k + 1, steps_snoc k hk hs⟩
  have hhead : ∀ x, reach x → x.1 < p.blocks.length → hd.contains x.1 = true →
      x.2.1.length ≤ maxH mx x.1 := fun x ⟨k, hk⟩ => heads k x hk
  have hsim := run_simF (msg := Final.Target.messageWith gas code call) (ss0 := Substate.empty) G
    rfl (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho rfl rfl he reach hclosed
    hhead n 0 [] [] _ 0 .empty gas st Substate.empty ⟨0, rfl⟩ (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], fun _ => by simp⟩) (SR.nil c _)
    (fun _ hf => absurd hf (by rw [hf0]; decide)) E0 R
  exact SpecG.toSpec (hsim.1 r hit)

/-- The forward stage at one gas, for the calls whose run ends within `n` blocks and keeps the
bound at its heads: `stage_of_checkR_gas` for `checkF`. -/
theorem stage_of_checkF_gas {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx hd : List Nat}
    {F : Frames} (hc : checkF p code c mx hd F = true) (o : SolarTV.Machine.Oracle)
    (ho : c.env = true → OracleOk o) (he : c.reads = true → EnvOk o) (call : SolarTV.Call)
    (heads : HeadsOk o call p mx hd) (n : Nat)
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
  exact forward_of_checkF hc o ho he call heads n r hit hg

/-- `checkF` with the walk on the code's suffixes and without the labels' check. -/
def checkFS (p : Program) (code : ByteArray) (c : Cert) (mx hd : List Nat) (F : Frames) : Bool :=
  walkS c.offset (bytesOf code) 0 (lower p c) && blocksOkF p c mx hd F 0 p.blocks &&
    decide (c.need 0 = 0) && decide (c.top % 32 = 0) && decide (c.top ≤ 2 ^ 32) &&
    decide (code.size < 2 ^ 32) && !F.isFrame 0

theorem checkF_of_checkFS {p : Program} {code : ByteArray} {c : Cert} {mx hd : List Nat} {F : Frames}
    (h : checkFS p code c mx hd F = true) : checkF p code c mx hd F = true := by
  have hw := walkS_drop (bytesOf code) c.offset (lower p c) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  simp only [checkFS, hw, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hwalk, hb⟩, h0⟩, h32⟩, htop⟩, hsize⟩, hf0⟩ := h
  simp only [checkF, hwalk, hb, labelsValid_of_walk hwalk, h0, h32, htop, hsize, hf0, Bool.and_self]

/--
info: 'SolidCore.Refinement.Solar.AssembleRec.stage_of_checkF_gas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_checkF_gas

/--
info: 'SolidCore.Refinement.Solar.AssembleRec.checkF_of_checkFS' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms checkF_of_checkFS

end SolidCore.Refinement.Solar.AssembleRec
