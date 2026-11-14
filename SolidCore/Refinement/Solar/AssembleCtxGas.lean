import SolidCore.Refinement.Solar.AssembleCtx
import SolidCore.Refinement.Solar.AssembleGasLoop
import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# EVM IR to bytecode from a gas bound on, for internal functions called in several contexts

The checker with contexts (`AssembleCtx.checkX`, `checkXB`) reads each run back from a frame that
succeeds, at the run's own gas: it proves no gas bound. Here is the forward direction with gas, for
the loop checker's fragment (memory at known offsets, no GAS, no call): `checkXL` checks each block
once per context with `AssembleLoop.blockOkL` under the context's certificate, except the blocks of
a set `F` that it leaves unchecked (a contract's functions outside a statement: the permit path's
STATICCALL and GAS, say). `guard F p` is the program with each block of `F` replaced by a jump to
itself, so a run of it that ends never enters `F`. `forward_of_checkXL`: when SolarTV's run of
`guard F p` ends within `n` blocks, then at every gas from `gasBoundL cx.base n` on, EthLib runs
the exact bytecode to exactly that result, reverts and their data included. That a valid call's
run of `guard F p` ends is a stage like any other (the run of `p` ends and never enters `F`),
which the stage generator proves by symbolic execution; nothing here assumes it.
-/

namespace SolidCore.Refinement.Solar.AssembleCtxGas

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## The guarded program -/

/-- `p` with each block of `F` a jump to itself. -/
def guard (F : List Nat) (p : Assemble.Program) : Assemble.Program :=
  ⟨p.blocks.mapIdx fun b instrs => if F.contains b then [.jump b] else instrs⟩

theorem guard_length (F : List Nat) (p : Assemble.Program) :
    (guard F p).blocks.length = p.blocks.length := by
  simp [guard]

theorem guard_get? (F : List Nat) (p : Assemble.Program) (b : Nat) :
    (guard F p).blocks[b]? = p.blocks[b]?.map fun instrs => if F.contains b then [.jump b] else instrs := by
  simp [guard, List.getElem?_mapIdx]

theorem block_guard_out {F : List Nat} {p : Assemble.Program} {o : Oracle} {call : Call} {b : Nat}
    (hb : b < p.blocks.length) (hF : F.contains b = false) (S : List Word) (s : State) :
    SolarTV.EVM.Program.block o call (guard F p) (b, S, s) =
      some (SolarTV.EVM.Program.exec o call b p.blocks[b] S s) := by
  simp only [SolarTV.EVM.Program.block, guard_get?, List.getElem?_eq_getElem hb, Option.map_some,
    hF, Bool.false_eq_true, ite_false]

theorem block_guard_end {F : List Nat} {p : Assemble.Program} {o : Oracle} {call : Call}
    (S : List Word) (s : State) :
    SolarTV.EVM.Program.block o call (guard F p) (p.blocks.length, S, s) = some (.inl (.stop, s)) := by
  have h : (guard F p).blocks[p.blocks.length]? = none := by
    rw [guard_get?, List.getElem?_eq_none (by omega)]; rfl
  simp only [SolarTV.EVM.Program.block, h, guard_length, ite_true]

/-- A run of `guard F p` that enters a block of `F` with fewer than 1024 words never ends. -/
theorem iterate_guard_in {F : List Nat} {p : Assemble.Program} {o : Oracle} {call : Call} {b : Nat}
    (hb : b < p.blocks.length) (hF : F.contains b = true) (S : List Word) (hS : S.length < 1024)
    (s : State) : ∀ n, iterate (SolarTV.EVM.Program.block o call (guard F p)) n (b, S, s) = none
  | 0 => rfl
  | n + 1 => by
    have hblk : SolarTV.EVM.Program.block o call (guard F p) (b, S, s) = some (.inr (b, S, s)) := by
      simp only [SolarTV.EVM.Program.block, guard_get?, List.getElem?_eq_getElem hb, Option.map_some,
        hF, ite_true, SolarTV.EVM.Program.exec]
      rw [if_neg (by omega)]
    simp only [iterate, hblk]
    exact iterate_guard_in hb hF S hS s n

/-! ## The checker -/

/-- Block `b` under a certificate, as `AssembleLoop.blocksOkL` checks it. -/
def blockCtxOkL (p : Assemble.Program) (c : Cert) (mx : List Nat) (b : Nat)
    (instrs : List Assemble.Instr) : Bool :=
  decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
    decide (maxH mx b + budget c b ≤ 1000) &&
    blockOkL p c mx b (c.need b) [] (c.entry b) (budget c b - labelItems p c b) instrs

/-- Block `b` in context `j`, on the loop checker's fragment. -/
def ctxOkL (p : Assemble.Program) (cx : CtxCert) (b j : Nat) (instrs : List Assemble.Instr) : Bool :=
  blockCtxOkL p (certAt cx (p.blocks.length + 1) b j) (maxsAt cx (p.blocks.length + 1) b j) b instrs &&
    exitsOk p.blocks.length cx b j (exits b (cx.at b j).labs instrs) &&
    labsCover (cx.at b j).types (cx.at b j).labs (cx.at b j).rets

/-- Every block outside `F` in each of its contexts; a block of `F` is entered with at most 1000
words in every context. -/
def blocksXL (F : List Nat) (p : Assemble.Program) (cx : CtxCert) :
    Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    (List.range (cx.count b)).all (fun j =>
      if F.contains b then decide ((cx.at b j).max ≤ 1000) else ctxOkL p cx b j instrs) &&
      blocksXL F p cx (b + 1) rest

/-- **The checker with contexts and gas**: the layout of `AssembleLoop.checkL`, the first
block's first context at height zero, and every block outside `F` in each of its contexts. -/
def checkXL (F : List Nat) (p : Assemble.Program) (code : ByteArray) (cx : CtxCert) : Bool :=
  (walk (bytesOf code) cx.base.offset 0 (lower p cx.base)).isSome && labelsValid p cx.base code &&
    decide (cx.base.top % 32 = 0) && decide (cx.base.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32) &&
    decide (0 < cx.count 0) && decide ((cx.at 0 0).need = 0) && !F.contains 0 &&
    blocksXL F p cx 0 p.blocks

theorem blocksXL_get {F : List Nat} {p : Assemble.Program} {cx : CtxCert} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat), blocksXL F p cx b l = true →
      ∀ k (hk : k < l.length) j, j < cx.count (b + k) →
        (if F.contains (b + k) then decide ((cx.at (b + k) j).max ≤ 1000)
          else ctxOkL p cx (b + k) j l[k]) = true
  | [], _, _, _, hk, _, _ => absurd hk (by simp)
  | x :: l, b, h, 0, _, j, hj => by
    simp only [blocksXL, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    simpa using h.1 j (by simpa using hj)
  | x :: l, b, h, k + 1, hk, j, hj => by
    simp only [blocksXL, Bool.and_eq_true] at h
    have := blocksXL_get l (b + 1) h.2 k (by simp at hk; omega) j
      (by rw [show b + 1 + k = b + (k + 1) by omega]; exact hj)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the checker. -/
structure GlobXL (F : List Nat) (p : Assemble.Program) (cx : CtxCert) (code : ByteArray) : Prop where
  glob : GlobLT p cx.base code
  block : ∀ b (hb : b < p.blocks.length), F.contains b = false → ∀ j, j < cx.count b →
    ctxOkL p cx b j p.blocks[b] = true
  guarded : ∀ b, b < p.blocks.length → F.contains b = true → ∀ j, j < cx.count b → (cx.at b j).max ≤ 1000

theorem globXL_of_checkXL {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (h : checkXL F p code cx = true) :
    GlobXL F p cx code ∧ Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size ∧
      0 < cx.count 0 ∧ (cx.at 0 0).need = 0 ∧ F.contains 0 = false := by
  simp only [checkXL, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hlabels⟩, hmod⟩, htop⟩, hsize⟩, hcount⟩, hneed⟩, hF0⟩, hblocks⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨⟨hmod, htop, hsize, fun t ht htgt => ?_⟩, fun b hb hF j hj => ?_, fun b hb hF j hj => ?_⟩,
    hseg, hcount, hneed, hF0⟩
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
  · have := blocksXL_get p.blocks 0 hblocks b hb j (by simpa using hj)
    simp only [Nat.zero_add, hF] at this
    simpa using this
  · have := blocksXL_get p.blocks 0 hblocks b hb j (by simpa using hj)
    simp only [Nat.zero_add, hF] at this
    simpa using this

theorem globLT_congr {p : Assemble.Program} {code : ByteArray} {c1 c2 : Cert} (h : Same c1 c2)
    (G : GlobLT p c1 code) : GlobLT p c2 code where
  top_mod := h.2.2 ▸ G.top_mod
  top_le := h.2.2 ▸ G.top_le
  size_lt := G.size_lt
  target := fun t ht htg => by
    rw [← isTarget_congr h.2.1] at htg
    rw [← h.offset, ← lowerFrom_congr h.2.1]
    exact G.target t ht htg

theorem entryL_congr {c1 c2 : Cert} (h : Same c1 c2) {p : Assemble.Program} {code : ByteArray}
    {call : Call} {b R pc : Nat} {s : State} {M : ByteArray} {g : Nat}
    (E : EntryL c1 code call (lowerFrom p c1 b (p.blocks.drop b)) R pc s M g) :
    EntryL c2 code call (lowerFrom p c2 b (p.blocks.drop b)) R pc s M g := by
  obtain ⟨hseg, hg, htop, hmem⟩ := E
  refine ⟨?_, h.2.2 ▸ hg, h.2.2 ▸ htop, hmem⟩
  rw [← h.offset, ← lowerFrom_congr h.2.1]
  exact hseg

/-! ## The forward simulation -/

/-- The relation at a block entry, with gas for `R` more items: `AssembleLoop.run_simL`'s, under a
certificate of the layout, at the height range and types of one of the block's contexts when the
block is outside `F`. -/
def EntL (F : List Nat) (p : Assemble.Program) (cx : CtxCert) (code : ByteArray) (call : Call)
    (R : Nat) (x : Nat × List Word × State) (pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    Prop :=
  ∃ (c : Cert) (mx : List Nat), Same c cx.base ∧ x.1 ≤ p.blocks.length ∧
    (x.1 < p.blocks.length → c.need x.1 ≤ x.2.1.length ∧ x.2.1.length ≤ maxH mx x.1) ∧
    SR c (c.entry x.1) x.2.1 T ∧ EntryL c code call (lowerFrom p c x.1 (p.blocks.drop x.1)) R pc x.2.2 M g ∧
    (x.1 < p.blocks.length → ∃ j, j < cx.count x.1 ∧ c.need x.1 = (cx.at x.1 j).need ∧
      maxH mx x.1 = (cx.at x.1 j).max ∧ c.entry x.1 = (cx.at x.1 j).types ∧
      LabOk (cx.at x.1 j).labs x.2.1)

theorem bmax_certAt (cx : CtxCert) (n b j : Nat) : bmax (certAt cx n b j) = bmax cx.base := rfl

open SolarTV.EVM.Program in
/-- **EthLib runs the bytecode as SolarTV runs `guard F p`**, from a block whose relation holds,
with gas for `fuel` blocks: to SolarTV's result when its run ends within them. -/
theorem run_simXL {F : List Nat} {p : Assemble.Program} {cx : CtxCert} {code : ByteArray}
    (G : GlobXL F p cx code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    {a : Nat} (hcaller : msg.caller = Target.address a) (ho : cx.base.env = true → OracleOkAt a o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : cx.base.reads = true → msg.txEnv = Target.txEnv)
    (he : cx.base.reads = true → EnvOk o) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      EntL F p cx code call (fuel * bmax cx.base) (b, S, s) pc T M g → Rel msg ss0 st ss s →
      ∀ r, SolarTV.Machine.iterate (block o call (guard F p)) fuel (b, S, s) = some r →
        SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)
  | 0, b, S, T, s, pc, M, g, st, ss, _, _, r, hr => by simp [SolarTV.Machine.iterate] at hr
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hE, R, r, hr => by
    obtain ⟨c0, mx0, hsame0, hle, hneed0, hR0, E0, hctx⟩ := hE
    dsimp only at hle hneed0 hR0 E0 hctx
    by_cases hb : b < p.blocks.length
    · obtain ⟨j, hj, hn0, hm0, he0, hlab⟩ := hctx hb
      cases hF : F.contains b with
      | true =>
        have hS : S.length < 1024 := by
          have := G.guarded b hb hF j hj
          have := (hneed0 hb).2
          omega
        rw [iterate_guard_in hb hF S hS s] at hr
        cases hr
      | false =>
      have hbn : b < p.blocks.length + 1 := by omega
      obtain ⟨c, hc⟩ : ∃ c, c = certAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
      obtain ⟨mx, hmx⟩ : ∃ mx, mx = maxsAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
      have hsame : Same c cx.base := hc ▸ certAt_same cx _ b j
      have hsame' : Same c0 c := ⟨hsame0.1.trans hsame.1.symm, hsame0.2.1.trans hsame.2.1.symm,
        hsame0.2.2.trans hsame.2.2.symm⟩
      have hcb : c.need b = (cx.at b j).need := by
        rw [hc, certAt_need hbn, pick_of_exit (exitCtx_self cx b j)]
      have hmb : maxH mx b = (cx.at b j).max := by
        rw [hmx, maxsAt_max hbn, pick_of_exit (exitCtx_self cx b j)]
      have heb : c.entry b = (cx.at b j).types := by
        rw [hc, certAt_entry hbn, pick_of_exit (exitCtx_self cx b j)]
      have hcr : c.rets = (cx.at b j).rets := by rw [hc]; rfl
      have hbc : bmax c = bmax cx.base := by rw [hc]; rfl
      have hck := G.block b hb hF j hj
      simp only [ctxOkL, Bool.and_eq_true] at hck
      obtain ⟨⟨hblk0, hexOk⟩, hcov⟩ := hck
      have hR : SR c (c.entry b) S T := by
        rw [heb, ← he0]
        exact SR_congr hsame' hR0 (by rw [he0, hcr]; exact labsCover_mem hcov hlab)
      have E : EntryL c code call (lowerFrom p c b (p.blocks.drop b)) ((fuel + 1) * bmax c) pc s M g := by
        rw [hbc]; exact entryL_congr hsame' E0
      have hn : c.need b ≤ S.length := by rw [hcb, ← hn0]; exact (hneed0 hb).1
      have hm : S.length ≤ maxH mx b := by rw [hmb, ← hm0]; exact (hneed0 hb).2
      have hGc : GlobLT p c code := globLT_congr ⟨hsame.1.symm, hsame.2.1.symm, hsame.2.2.symm⟩ G.glob
      rw [← hc, ← hmx] at hblk0
      simp only [blockCtxOkL, Bool.and_eq_true, decide_eq_true_eq] at hblk0
      obtain ⟨⟨⟨hL, hnm⟩, hstk⟩, hblock⟩ := hblk0
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
      have hsim := exec_simL (o := o) hGc hdata hvalue hstatic hself hcaller (by rw [hc]; exact ho)
        hbenv (by rw [hc]; exact htx) (by rw [hc]; exact he) b hb (fuel * bmax c)
        p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
        (KR.nil _) hR I1 R
      cases hexE : exits b (cx.at b j).labs p.blocks[b] with
      | none => rw [hexE] at hexOk; simp [exitsOk] at hexOk
      | some Ex =>
      rw [hexE] at hexOk
      simp only [SolarTV.Machine.iterate, block_guard_out hb hF] at hr
      generalize hx : exec o call b p.blocks[b] S s = x at hsim hr
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', E', R'⟩ := hsim
        obtain ⟨L', hmemE, hL'⟩ := exits_sound o call b p.blocks[b] _ S s Ex _ hlab hexE hx
        have IH := run_simXL G hdata hvalue hstatic hself hcaller ho hbenv htx he fuel t S' T' s' pc'
          M' g' st' ss' ⟨c, mx, hsame, htle, hneedt, hR', by rw [← hbc]; exact E', fun ht => ?_⟩ R' r hr
        · exact SpecG.seq (Triple.seq hlabel hh) IH
        · obtain ⟨j', hx', hj'c, hlabs⟩ := exitsOk_mem hexOk hmemE ht
          have htn : t < p.blocks.length + 1 := by omega
          have hpk := pick_of_exit hx'
          refine ⟨j', hj'c, ?_, ?_, ?_, hL'.le hlabs⟩
          · rw [hc, certAt_need htn, hpk]
          · rw [hmx, maxsAt_max htn, hpk]
          · rw [hc, certAt_entry htn, hpk]
    · obtain rfl : b = p.blocks.length := by omega
      simp only [SolarTV.Machine.iterate, block_guard_end, Option.some.injEq] at hr
      subst hr
      have hseg := E0.seg
      rw [lowerFrom_nil p c0 (by omega)] at hseg
      have hpc := hseg.nil_end
      exact SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h

/-- **The forward assembly theorem for code with contexts.** When SolarTV's run of `guard F p`
ends within `n` blocks, from `gasBoundL cx.base n` gas on EthLib runs the exact bytecode to
exactly its result. -/
theorem forward_of_checkXL {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXL F p code cx = true) (o : SolarTV.Machine.Oracle) (ho : cx.base.env = true → OracleOk o)
    (he : cx.base.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL cx.base n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hcount, hneed0, hF0⟩ := globXL_of_checkXL hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine Assemble.run_of_rel_with code call r.2 r.1 gas fun st R => ?_
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  refine SpecG.toSpec (run_simXL G rfl (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl ho rfl (fun _ => rfl) he
    n 0 [] [] _ 0 .empty gas st Substate.empty
    ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame, Nat.zero_le _,
      fun _ => ⟨by simp [hn0, hneed0], by simp⟩, SR.nil _ _, ⟨?_, ?_, by simp, memRel_initial⟩,
      fun _ => ⟨0, hcount, hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
        by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩ R r hit)
  · rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  · rw [hm0, hsame.2.2]
    unfold gasBoundL at hg
    exact Nat.le_trans (Nat.add_le_add_left (Nat.sub_le _ _) _) hg

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_of_checkXL

open SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at every gas, without hypotheses on the runner of messages.** When
SolarTV's run of `guard F p` ends within `n` blocks, every result EthLib gives for the exact
bytecode at any gas is that run's result, or a failure that changes nothing: a run that succeeds at
gas `g` is the run with `gasBoundL cx.base n` more gas, which `run_simXL` follows to the end. No
block of `F` (the only ones with STATICCALL or GAS) is reached, so the runner of messages is never
consulted. -/
theorem within_of_checkXL {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXL F p code cx = true) (o : SolarTV.Machine.Oracle) (ho : cx.base.env = true → OracleOk o)
    (he : cx.base.reads = true → EnvOk o) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r) (gas : Nat) (obs : Observable)
    (hrun : Final.Target.runWith gas code call = some obs) :
    obs = SolarTV.Machine.observe call r.2 r.1 ∨
      (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) := by
  obtain ⟨G, hseg, hcount, hneed0, hF0⟩ := globXL_of_checkXL hc
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
  set msg := Final.Target.messageWith gas code call with hmsg
  have hcode : msg.code = code := rfl
  have R := rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hsim := run_simXL (msg := msg) (ss0 := ss') G rfl (by simp [msg, Final.Target.messageWith,
    Target.message]) rfl rfl rfl ho rfl (fun _ => rfl) he n 0 [] [] _ 0 .empty (gas + gasBoundL cx.base n) st' ss'
    ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame, Nat.zero_le _,
      fun _ => ⟨by simp [hn0, hneed0], by simp⟩, SR.nil _ _,
      ⟨by rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]; exact hseg,
        by
          rw [hm0]
          show 22100 * (n * bmax cx.base) + (memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0) ≤ _
          have : memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0 ≤ memoryGasCost cx.base.top := by
            rw [hsame.2.2]; exact Nat.sub_le _ _
          unfold gasBoundL; omega,
        by simp, memRel_initial⟩,
      fun _ => ⟨0, hcount, hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
        by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩ R r hit
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas (gasBoundL cx.base n)
  rcases r with ⟨halt, sF⟩
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := SpecG.low hsim hp within hrf hok
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
  clear herr hout hst hsim hit
  generalize SolarTV.Machine.observe call sF halt = X at *
  have hsucc : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout' hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc, hout', ?_, ?_⟩
    · rw [hsucc]
      cases hs : success
      · simp [hok, hs] at hsucc
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc]
      cases hs : success
      · simp [hok, hs] at hsucc
      · simp only [ite_true]
        exact (hst' hs).2 slot

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_checkXL

end SolidCore.Refinement.Solar.AssembleCtxGas
