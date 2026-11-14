import SolidCore.Refinement.Solar.AssembleCut
import SolidCore.Refinement.Solar.AssembleCtxTrack

/-!
# EVM IR to bytecode, block by block in each of a block's contexts

\`AssembleCut.checkC\` gives each block one entry height and one stack type, and checks a dynamic
jump against every block a return label names. An internal function called from two stack
heights, or with different words under its frame, has no such type: after its return each caller
needs the words it left under the frame typed as it left them, which the callee's one type cannot
say for both. This checker, \`checkX\`, checks each block once in each of its *contexts* (\`Ctx\`):
an entry height range and types for the whole stack the context knows, what the words are as
labels (\`AssembleCtxTrack.Lab\`), and the context each successor enters in. A return label is
then known as the label it is (\`exits\`), so a dynamic jump enters the one context its caller
named, at the caller's height and types.

Soundness reuses the checker with GAS: in context \`j\`, block \`b\` is checked by
\`AssembleCut.blockOkC\` under a certificate (\`certAt\`) that has \`b\`'s entry from the context
and each successor's from the context it enters in (every other block's entry asks for nothing).
\`AssembleCut.seg\` runs the block against the bytecode under that certificate, and
\`AssembleCtxTrack.exits_sound\` says which block, and so which context, SolarTV's run of it
enters, with the words there known as the context needs them. The invariant at a block entry
(\`EntX\`) is \`AssembleCut.EntT\` under some certificate of the same layout, with the entry of a
context of that block. \`withinRun_of_checkX\` is \`AssembleCut.withinRun_of_checkC\`'s statement,
unchanged in shape, for every program the context checker accepts.
-/

namespace SolidCore.Refinement.Solar.AssembleCtx

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop SolidCore.Refinement.Solar.AssembleCut
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Certificates with contexts -/

/-- One context of a block: the least and the greatest height it is entered at, the types of the
words on top of its stack, what they are as labels, and the context (by its index among the
successor's) each block it leaves to enters in, and the blocks its labels may name. A jump to its
own block stays in it. -/
structure Ctx where
  need : Nat
  max : Nat
  types : List Ty := []
  labs : List Lab := []
  succ : List (Nat × Nat) := []
  /-- The blocks a label on its stack, or one the block pushes, may name. -/
  rets : List Nat := []
  deriving Repr

/-- The context that asks for nothing. -/
def trivialCtx : Ctx := { need := 0, max := 4096 }

/-- A certificate with contexts: the layout and the flags of \`base\` (its \`needs\` and \`types\`
are unused), and each block's contexts. -/
structure CtxCert where
  base : Cert
  ctxs : List (List Ctx)
  deriving Repr

def CtxCert.at (cx : CtxCert) (t j : Nat) : Ctx := (cx.ctxs.getD t []).getD j trivialCtx

def CtxCert.count (cx : CtxCert) (t : Nat) : Nat := (cx.ctxs.getD t []).length

/-- The context block \`t\` is entered in from block \`b\` in context \`j\`. -/
def exitCtx (cx : CtxCert) (b j t : Nat) : Option Nat :=
  if t = b then some j else (cx.at b j).succ.lookup t

/-- What block \`b\` in context \`j\` asks of block \`t\`'s entry. -/
def pick (cx : CtxCert) (b j t : Nat) : Ctx :=
  match exitCtx cx b j t with
  | some j' => cx.at t j'
  | none => trivialCtx

/-- The certificate block \`b\` is checked under in context \`j\`, over blocks below \`n\`. -/
def certAt (cx : CtxCert) (n b j : Nat) : Cert :=
  { cx.base with
    needs := (List.range n).map fun t => (pick cx b j t).need
    types := (List.range n).map fun t => (pick cx b j t).types
    rets := (cx.at b j).rets }

def maxsAt (cx : CtxCert) (n b j : Nat) : List Nat := (List.range n).map fun t => (pick cx b j t).max

/-- Every word \`W\` knows as a label, \`L\` knows as one of fewer blocks. -/
def labLe (L W : List Lab) : Bool :=
  (List.range W.length).all fun i =>
    match labAt W i with
    | none => true
    | some ws =>
      match labAt L i with
      | some ts => ts.all fun t => ws.contains t
      | none => false

/-- Every word the types call a label is one the context knows as a label of the blocks `R`. -/
def labsCover (ty : List Ty) (L : List Lab) (R : List Nat) : Bool :=
  (List.range ty.length).all fun i => tyAt ty i != some true ||
    match labAt L i with
    | some ts => ts.all fun t => R.contains t
    | none => false

/-- The block's check under a certificate, as \`AssembleCut.blocksOkC\` checks each block. -/
def blockCtxOk (p : Assemble.Program) (c : Cert) (mx : List Nat) (b : Nat)
    (instrs : List Assemble.Instr) : Bool :=
  decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
    decide (maxH mx b + budget c b ≤ 1000) &&
    blockOkC p c mx b (c.need b) [] (c.entry b) (budget c b - labelItems p c b) instrs

/-- Each block the run of block \`b\` in context \`j\` may leave to below \`n\` enters a context of it
that the words there meet. -/
def exitsOk (n : Nat) (cx : CtxCert) (b j : Nat) : Option (List (Nat × List Lab)) → Bool
  | none => false
  | some E => E.all fun e => decide (n ≤ e.1) ||
      match exitCtx cx b j e.1 with
      | some j' => decide (j' < cx.count e.1) && labLe e.2 (cx.at e.1 j').labs
      | none => false

/-- Block \`b\` in context \`j\`. -/
def ctxOk (p : Assemble.Program) (cx : CtxCert) (b j : Nat) (instrs : List Assemble.Instr) : Bool :=
  blockCtxOk p (certAt cx (p.blocks.length + 1) b j) (maxsAt cx (p.blocks.length + 1) b j) b instrs &&
    exitsOk p.blocks.length cx b j (exits b (cx.at b j).labs instrs) &&
    labsCover (cx.at b j).types (cx.at b j).labs (cx.at b j).rets

/-- Every block in every one of its contexts. -/
def blocksX (p : Assemble.Program) (cx : CtxCert) : Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    (List.range (cx.count b)).all (fun j => ctxOk p cx b j instrs) && blocksX p cx (b + 1) rest

/-- **The checker with contexts**, for programs that make no call: the layout of \`checkC\`, the
first block's first context at height zero, and every block in each of its contexts. -/
def checkX (p : Assemble.Program) (code : ByteArray) (cx : CtxCert) : Bool :=
  (walk (bytesOf code) cx.base.offset 0 (lower p cx.base)).isSome && labelsValid p cx.base code &&
    decide (cx.base.top % 32 = 0) && decide (cx.base.top ≤ 2 ^ 200) && decide (code.size < 2 ^ 32) &&
    !cx.base.calls && decide (0 < cx.count 0) && decide ((cx.at 0 0).need = 0) &&
    blocksX p cx 0 p.blocks

/-! ## Certificates of one layout -/

/-- Two certificates of one layout and memory bound. -/
def Same (c1 c2 : Cert) : Prop :=
  c1.offsets = c2.offsets ∧ c1.turned = c2.turned ∧ c1.top = c2.top

theorem Same.offset {c1 c2 : Cert} (h : Same c1 c2) : c1.offset = c2.offset := by
  funext t; simp [Cert.offset, h.1]

theorem turnedElse_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (b : Nat) (i : Assemble.Instr)
    (rest : List Assemble.Instr) : turnedElse c1 b i rest = turnedElse c2 b i rest := by
  unfold turnedElse; rw [h]

theorem lowerInstrs_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (p : Assemble.Program) (b : Nat) :
    ∀ l, lowerInstrs p c1 b l = lowerInstrs p c2 b l
  | [] => rfl
  | i :: rest => by
    simp only [lowerInstrs, turnedElse_congr h b i rest, lowerInstrs_congr h p b rest]

theorem bodies_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (p : Assemble.Program) :
    ∀ b l, bodies p c1 b l = bodies p c2 b l
  | _, [] => rfl
  | b, x :: l => by simp only [bodies, lowerInstrs_congr h p b x, bodies_congr h p (b + 1) l]

theorem isTarget_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (p : Assemble.Program) (t : Nat) :
    isTarget p c1 t = isTarget p c2 t := by
  simp only [isTarget, bodies_congr h p 0 p.blocks]

theorem lowerFrom_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (p : Assemble.Program) :
    ∀ b l, lowerFrom p c1 b l = lowerFrom p c2 b l
  | _, [] => rfl
  | b, x :: l => by
    simp only [lowerFrom, lowerBlock, isTarget_congr h p b, lowerInstrs_congr h p b x,
      lowerFrom_congr h p (b + 1) l]

theorem meas_congr {c1 c2 : Cert} (h : c1.turned = c2.turned) (p : Assemble.Program) (g b : Nat) :
    AssembleLoop.meas p c1 g b = AssembleLoop.meas p c2 g b := by
  simp only [AssembleLoop.meas, isTarget_congr h p b]

theorem SR_congr {c1 c2 : Cert} (h : Same c1 c2) {ty : List Ty} {S T : List Word}
    (hR : SR c1 ty S T)
    (hl : ∀ i (hi : i < S.length), tyAt ty i = some true → S[i].toNat ∈ c2.rets) : SR c2 ty S T := by
  refine ⟨hR.1, fun i h1 h2 => ?_⟩
  have hw := hR.2 i h1 h2
  have hl' := hl i h1
  generalize tyAt ty i = τ at hw hl' ⊢
  cases τ with
  | none => trivial
  | some bb =>
    cases bb with
    | false => exact hw
    | true =>
      obtain ⟨-, hy⟩ := hw
      exact ⟨hl' rfl, by rw [← h.offset]; exact hy⟩

theorem labsCover_mem {ty : List Ty} {L : List Lab} {R : List Nat} {S : List Word}
    (h : labsCover ty L R = true) (hL : LabOk L S) :
    ∀ i (hi : i < S.length), tyAt ty i = some true → S[i].toNat ∈ R := by
  intro i hi ht
  have hit : i < ty.length := by
    by_contra hc
    simp [tyAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at ht
  simp only [labsCover, List.all_eq_true, List.mem_range] at h
  have := h i hit
  simp only [ht, bne_self_eq_false, Bool.false_or] at this
  cases hl : labAt L i with
  | none => simp [hl] at this
  | some ts =>
    simp only [hl, List.all_eq_true] at this
    have h2 := this _ (hL i ts hl S[i] (List.getElem?_eq_getElem hi))
    simpa using h2

theorem globT_congr {p : Assemble.Program} {code : ByteArray} {c1 c2 : Cert} (h : Same c1 c2)
    (G : GlobT p c1 code) : GlobT p c2 code where
  top_mod := h.2.2 ▸ G.top_mod
  top_le := h.2.2 ▸ G.top_le
  size_lt := G.size_lt
  target := fun t ht htg => by
    rw [← isTarget_congr h.2.1] at htg
    rw [← h.offset, ← lowerFrom_congr h.2.1]
    exact G.target t ht htg

theorem entC_congr {p : Assemble.Program} {code : ByteArray} {msg : Message .fusaka} {ss0 : Substate}
    {c1 c2 : Cert} {mx1 mx2 : List Nat} (h : Same c1 c2) {x : Nat × List Word × State}
    {evm : Evm .fusaka Nat}
    (hn : x.1 < p.blocks.length → c1.need x.1 = c2.need x.1 ∧ maxH mx1 x.1 = maxH mx2 x.1)
    (he : c1.entry x.1 = c2.entry x.1)
    (hl : ∀ i (hi : i < x.2.1.length), tyAt (c1.entry x.1) i = some true → x.2.1[i].toNat ∈ c2.rets)
    (hE : EntC p c1 mx1 code msg ss0 x evm) :
    EntC p c2 mx2 code msg ss0 x evm := by
  obtain ⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩ := hE
  refine ⟨Tw, pc, M, st, ss, rd, hle, fun hb => ?_, ?_, ?_, h.2.2 ▸ htop, hmem, R, hat⟩
  · obtain ⟨h1, h2⟩ := hn hb
    rw [← h1, ← h2]; exact hneed hb
  · rw [← he]; exact SR_congr h hR hl
  · rw [← h.offset, ← lowerFrom_congr h.2.1]; exact hseg

theorem entT_congr {p : Assemble.Program} {code : ByteArray} {msg : Message .fusaka} {ss0 : Substate}
    {T : RunTable} {c1 c2 : Cert} {mx1 mx2 : List Nat} (h : Same c1 c2) {x : Nat × List Word × State}
    {evm : Evm .fusaka Nat}
    (hn : x.1 < p.blocks.length → c1.need x.1 = c2.need x.1 ∧ maxH mx1 x.1 = maxH mx2 x.1)
    (he : c1.entry x.1 = c2.entry x.1)
    (hl : ∀ i (hi : i < x.2.1.length), tyAt (c1.entry x.1) i = some true → x.2.1[i].toNat ∈ c2.rets)
    (hE : EntT p c1 mx1 code msg ss0 T x evm) :
    EntT p c2 mx2 code msg ss0 T x evm :=
  ⟨entC_congr h hn he hl hE.1, hE.2⟩

/-! ## The certificate of a block in a context -/

theorem getD_map_range {α : Type} {f : Nat → α} {n t : Nat} (ht : t < n) (d : α) :
    ((List.range n).map f).getD t d = f t := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]

theorem certAt_same (cx : CtxCert) (n b j : Nat) : Same (certAt cx n b j) cx.base :=
  ⟨rfl, rfl, rfl⟩

theorem certAt_need {cx : CtxCert} {n b j t : Nat} (ht : t < n) :
    (certAt cx n b j).need t = (pick cx b j t).need := getD_map_range ht 0

theorem certAt_entry {cx : CtxCert} {n b j t : Nat} (ht : t < n) :
    (certAt cx n b j).entry t = (pick cx b j t).types := getD_map_range ht []

theorem maxsAt_max {cx : CtxCert} {n b j t : Nat} (ht : t < n) :
    maxH (maxsAt cx n b j) t = (pick cx b j t).max := getD_map_range ht 0

theorem pick_of_exit {cx : CtxCert} {b j t j' : Nat} (h : exitCtx cx b j t = some j') :
    pick cx b j t = cx.at t j' := by
  simp [pick, h]

theorem exitCtx_self (cx : CtxCert) (b j : Nat) : exitCtx cx b j b = some j := by
  simp [exitCtx]

theorem LabOk.le {L W : List Lab} {S : List Word} (hle : labLe L W = true) (h : LabOk L S) :
    LabOk W S := by
  intro i ws hw w hS
  have hi : i < W.length := by
    by_contra hc
    simp [labAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hw
  simp only [labLe, List.all_eq_true, List.mem_range] at hle
  have := hle i hi
  rw [hw] at this
  cases hl : labAt L i with
  | none => simp [hl] at this
  | some ts =>
    simp only [hl, List.all_eq_true] at this
    have h2 := this _ (h i ts hl w hS)
    simpa using h2

theorem LabOk.empty (L : List Lab) : LabOk L [] := by
  intro i ts _ w hw
  simp at hw

theorem exitsOk_mem {n : Nat} {cx : CtxCert} {b j : Nat} {E : List (Nat × List Lab)}
    (h : exitsOk n cx b j (some E) = true) {t : Nat} {L : List Lab} (hm : (t, L) ∈ E) (ht : t < n) :
    ∃ j', exitCtx cx b j t = some j' ∧ j' < cx.count t ∧ labLe L (cx.at t j').labs = true := by
  simp only [exitsOk, List.all_eq_true] at h
  have := h _ hm
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · omega
  · cases he : exitCtx cx b j t with
    | none => simp [he] at h1
    | some j' =>
      simp only [he, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact ⟨j', rfl, h1.1, h1.2⟩

theorem blocksX_get {p : Assemble.Program} {cx : CtxCert} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat), blocksX p cx b l = true →
      ∀ k (hk : k < l.length) j, j < cx.count (b + k) → ctxOk p cx (b + k) j l[k] = true
  | [], _, _, _, hk, _, _ => absurd hk (by simp)
  | x :: l, b, h, 0, _, j, hj => by
    simp only [blocksX, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    simpa using h.1 j (by simpa using hj)
  | x :: l, b, h, k + 1, hk, j, hj => by
    simp only [blocksX, Bool.and_eq_true] at h
    have := blocksX_get l (b + 1) h.2 k (by simp at hk; omega) j (by rw [show b + 1 + k = b + (k + 1) by omega]; exact hj)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the checker with contexts. -/
structure GlobX (p : Assemble.Program) (cx : CtxCert) (code : ByteArray) : Prop where
  glob : GlobT p cx.base code
  calls : cx.base.calls = false
  block : ∀ b (hb : b < p.blocks.length) j, j < cx.count b → ctxOk p cx b j p.blocks[b] = true

theorem globX_of_checkX {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (h : checkX p code cx = true) :
    GlobX p cx code ∧ Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size ∧
      0 < cx.count 0 ∧ (cx.at 0 0).need = 0 := by
  simp only [checkX, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hlabels⟩, hmod⟩, htop⟩, hsize⟩, hnc⟩, hcount⟩, hneed⟩, hblocks⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨⟨hmod, htop, hsize, fun t ht htgt => ?_⟩, hnc, fun b hb j hj => ?_⟩, hseg, hcount, hneed⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (cx.base.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p cx.base t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p cx.base ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksX_get p.blocks 0 hblocks b hb j (by simpa using hj)
    simpa using this

/-! ## A block in a context, read back from a run that succeeds -/

/-- The relation at a block entry: \`AssembleCut.EntT\` under a certificate of the layout, at the
height range and the types of one of the block's contexts, its words what the context knows them
as. -/
def EntX (p : Assemble.Program) (cx : CtxCert) (code : ByteArray) (msg : Message .fusaka)
    (ss0 : Substate) (T : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat) : Prop :=
  ∃ (c : Cert) (mx : List Nat), Same c cx.base ∧ EntT p c mx code msg ss0 T x evm ∧
    (x.1 < p.blocks.length → ∃ j, j < cx.count x.1 ∧ c.need x.1 = (cx.at x.1 j).need ∧
      maxH mx x.1 = (cx.at x.1 j).max ∧ c.entry x.1 = (cx.at x.1 j).types ∧
      LabOk (cx.at x.1 j).labs x.2.1)

/-- **A block of code with loops and GAS, in one of its contexts, read back from a run that
succeeds.** -/
theorem advances_checkX {p : Assemble.Program} {cx : CtxCert} {code : ByteArray}
    (G : GlobX p cx code) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntX p cx code msg ss0 T0 x evm) :
    Advances (fun o => SolarTV.EVM.Program.block o call p) O (EntX p cx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p cx.base e.gas y.1) T0 x evm := by
  intro bound runChild _ within fin hrun hok
  obtain ⟨b, S, s⟩ := x
  obtain ⟨c0, mx0, hsame0, hE0, hctx⟩ := hE
  by_cases hb : b < p.blocks.length
  · obtain ⟨j, hj, hn0, hm0, he0, hlab⟩ := hctx hb
    have hbn : b < p.blocks.length + 1 := by omega
    obtain ⟨c, hc⟩ : ∃ c, c = certAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
    obtain ⟨mx, hmx⟩ : ∃ mx, mx = maxsAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
    have hsame : Same c cx.base := hc ▸ certAt_same cx _ b j
    have hcb : c.need b = (cx.at b j).need := by
      rw [hc, certAt_need hbn, pick_of_exit (exitCtx_self cx b j)]
    have hmb : maxH mx b = (cx.at b j).max := by
      rw [hmx, maxsAt_max hbn, pick_of_exit (exitCtx_self cx b j)]
    have heb : c.entry b = (cx.at b j).types := by
      rw [hc, certAt_entry hbn, pick_of_exit (exitCtx_self cx b j)]
    have hck := G.block b hb j hj
    simp only [ctxOk, Bool.and_eq_true] at hck
    obtain ⟨⟨hblk0, hexOk⟩, hcov⟩ := hck
    have hcr : c.rets = (cx.at b j).rets := by rw [hc]; rfl
    have hE' : EntT p c mx code msg ss0 T0 (b, S, s) evm :=
      entT_congr (c1 := c0) (mx1 := mx0) ⟨hsame0.1.trans hsame.1.symm, hsame0.2.1.trans hsame.2.1.symm,
        hsame0.2.2.trans hsame.2.2.symm⟩
        (fun _ => ⟨hn0.trans hcb.symm, hm0.trans hmb.symm⟩) (he0.trans heb.symm)
        (by rw [he0, hcr]; exact labsCover_mem hcov hlab) hE0
    have hGc : GlobT p c code := globT_congr ⟨hsame.1.symm, hsame.2.1.symm, hsame.2.2.symm⟩ G.glob
    have hnc : c.calls = false := by rw [hc]; exact G.calls
    rw [← hc, ← hmx] at hblk0
    simp only [blockCtxOk, Bool.and_eq_true, decide_eq_true_eq] at hblk0
    obtain ⟨⟨⟨hL, hnm⟩, hstk⟩, hblock⟩ := hblk0
    cases hexE : exits b (cx.at b j).labs p.blocks[b] with
    | none => rw [hexE] at hexOk; simp [exitsOk] at hexOk
    | some Ex =>
    rw [hexE] at hexOk
    obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hbud⟩ := hE'
    simp only at hle hneed hR hseg hmem R hTg hs0
    obtain ⟨hn, hm⟩ := hneed hb
    have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
    rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at hseg
    -- The label, at the frame's gas.
    obtain ⟨pc1, m1, within1, hat1, hseg1, hg1, hrun1⟩ : ∃ (pc1 : Nat) (m1 : Evm .fusaka Nat)
        (within1 : GasMeter.gasHeld m1.gas ≤ bound),
        At code msg pc1 Tw M m1.gas st ss rd m1 ∧
        Seg (bytesOf code) c.offset pc1 (lowerInstrs p c b p.blocks[b] ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size ∧
        m1.gas + (if isTarget p c b then 1 else 0) ≤ evm.gas ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m1 within1 = .ok fin := by
      by_cases ht : isTarget p c b = true
      · simp only [ht, ite_true, List.cons_append] at hseg
        obtain ⟨next, hd, hseg'⟩ := hseg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hp := hat.addGas 1
        obtain ⟨e1, r1, he1⟩ := Logic.jumpdestG hlt hcode (show 1 ≤ evm.gas + 1 by omega) _ hp
        obtain ⟨m, within', hz, hrm⟩ := reaches_low r1 1 evm rfl within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hgm⟩ := at_of_addGasR he1
        exact ⟨pc + 1, m, within', hatm, hseg', by simp only [ht, ite_true]; omega, hrm⟩
      · simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at hseg
        exact ⟨pc, evm, within, hat, hseg, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          hrun⟩
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := seg (G0 := msg.gas) hGc hnc hdata hvalue hstatic hself
      hcaller hbenv htx hb hok hgas (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) List.nil_prefix hR hseg1 (by omega) htop hmem R hat1 hTg hs0
      (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨T', r, hle', fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T'' h]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj'⟩, after, within', hE', hT', hs', hga, hbud', hra⟩ := hnext _ hy
      have hr := hex T' (RunTable.Le.refl T')
      rw [hy] at hr
      obtain ⟨L', hmemE, hL'⟩ := exits_sound (O T') call b p.blocks[b] _ S s Ex _ hlab hexE hr
      refine ⟨after, within', ⟨c, mx, hsame, ⟨hE', hT', hs', hbud'⟩, fun ht => ?_⟩, ?_, hra⟩
      · obtain ⟨j', hx, hj'c, hlabs⟩ := exitsOk_mem hexOk hmemE ht
        have htn : t < p.blocks.length + 1 := by omega
        have hpk := pick_of_exit hx
        refine ⟨j', hj'c, ?_, ?_, ?_, hL'.le hlabs⟩
        · rw [hc, certAt_need htn, hpk]
        · rw [hmx, maxsAt_max htn, hpk]
        · rw [hc, certAt_entry htn, hpk]
      · have := meas_step (c := c) (g := evm.gas) (g' := after.gas) hb htle (by omega) hj'
        rw [meas_congr hsame.2.1, meas_congr hsame.2.1] at this
        dsimp only at this ⊢
        omega
  · obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hbud⟩ := hE0
    simp only at hle hseg R
    obtain rfl : b = p.blocks.length := by omega
    have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
    have hbl : ∀ o, SolarTV.EVM.Program.block o call p (p.blocks.length, S, s) =
        some (.inl (.stop, s)) := by
      intro o
      simp only [SolarTV.EVM.Program.block, hblk, ite_true]
    refine ⟨T0, _, RunTable.Le.refl T0, fun _ _ => hbl _, ?_, ?_⟩
    · intro res hres
      cases hres
      have hseg' := hseg
      rw [lowerFrom_nil p c0 (by omega)] at hseg'
      have hpc := hseg'.nil_end
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy

/-! ## The theorems -/

/-- **EVM IR to bytecode, run by run, at the run's own gas, for code with loops, GAS, memory at
any offset and internal functions called in several contexts**: \`AssembleCut.runs_of_checkC\` for
every program the checker with contexts accepts. -/
theorem runs_of_checkX {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkX p code cx = true) (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) :
    ∃ T, Within (evmirSem (O T)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨G, hseg, hcount, hneed0⟩ := globX_of_checkX hc
  refine within_of_advances O (fun ss0 => EntX p cx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p cx.base e.gas y.1) (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkX G rfl
      (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl rfl rfl hgas T x evm hE)
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hseg0 : Seg (bytesOf code) (certAt cx (p.blocks.length + 1) 0 0).offset 0
      (lowerFrom p (certAt cx (p.blocks.length + 1) 0 0) 0 (p.blocks.drop 0)) code.size := by
    rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  refine ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame,
    ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hn0, hneed0], by simp⟩,
    SR.nil _ _, hseg0, by simp, memRel_initial, R, ?_⟩, rfl, rfl, ?_⟩, fun _ => ⟨0, hcount,
    hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
    by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- **The per-run theorem below \`2 ^ 256\` gas for every program the checker with contexts
accepts**: \`AssembleCut.withinRun_of_checkC\`'s statement, under the oracles that meet the base
certificate's flags. -/
theorem withinRun_of_checkX {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkX p code cx = true) (scope : Call → Prop) :
    WithinRunLt evmirSem (fun _ => p) code scope (CertOk cx.base) := by
  intro gas hgas call _
  obtain ⟨T, hT⟩ := runs_of_checkX hc gas hgas call
  exact ⟨O T, O_ok cx.base T, hT⟩

/-- **The assembly premise of \`AssembleCut.holds_of_runs_lt\`** for every program the checker with
contexts accepts. -/
theorem assembly_of_checkX {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkX p code cx = true) (scope : Call → Prop) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call _
  obtain ⟨T, hT⟩ := runs_of_checkX hc gas hgas call
  obtain ⟨W, hW, hA⟩ := O_agree T
  exact ⟨O T, W, hW, hA, hT⟩

/-- The first lowered MIR to the exact bytecode, run by run, for every program the checker with
contexts accepts: \`AssembleCut.withinRun_mir_of_checkC\` with \`checkX\`. -/
theorem withinRun_mir_of_checkX {stage0 : SolarTV.MIR.Lowered.moduleLayer.Prog}
    {p : Assemble.Program} {code : ByteArray} {cx : CtxCert} {S scope : Call → Prop}
    (back : ∀ o, Certified SolarTV.EVM.Program.layer SolarTV.MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call) (hc : checkX p code cx = true) :
    WithinRunLt mirSem (fun _ => stage0) code scope (CertOk cx.base) :=
  WithinRunLt.of_back (fun o _ => fun call hcall obs h =>
      stage_of_certified (back o) call (hS call hcall) obs h)
    (withinRun_of_checkX hc scope)

/-- info: 'SolidCore.Refinement.Solar.AssembleCtx.withinRun_of_checkX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_of_checkX

/-- info: 'SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkX

/-- info: 'SolidCore.Refinement.Solar.AssembleCtx.withinRun_mir_of_checkX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_mir_of_checkX

end SolidCore.Refinement.Solar.AssembleCtx
