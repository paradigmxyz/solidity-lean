import Contracts.VerifyCounter.Source
import Contracts.VerifyCounter.StageMir
import SolidCore.Refinement.Generic.MirNoLog
import SolidCore.Refinement.Generic.Stage
import SolarTV.Composition

/-!
# bump's source stage: SolidCore's `Counter` to solar's first lowered MIR

`mir_eq`: on every call of `bump(n)` (any argument word, no value, any storage), under every
oracle, solar's first lowered MIR `stage0` and SolidCore's runtime (`solidCoreRuntime fuel`,
`Source.lean`) give the **same observable**. Both sides are total on these calls, so this is
equality of results, not inclusion:

* SolidCore runs the call to its tree's leaf (`Source.runs`, the loop by its ranking
  certificate `n - i`);
* `stage0` ends in its exact end (`Bump.xstage0_ends`: the generated header invariant and the
  same rank, checked segment by segment), with no logs (`Module.ends_logs`: `stage0` has no
  `log` instruction, `stage0_noLog`);
* the three leaves agree: `Panic(0x11)` when `count + n` wraps, `Error("over")` when it
  exceeds `limit` (the revert data byte for byte), else success with slot 0 holding
  `count + n` and every other slot unchanged.

`stage` restates it as `Stage (solidCoreRuntime fuel) (mirSem o) c stage0 BumpCall`, and
`stage_back` the converse stage.
-/

namespace Contracts.VerifyCounter.Source
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop
open SolarTV SolarTV.Machine

theorem stage0_noLog : SolarTV.Export.Counter.stage0.noLog = true := by decide

theorem lit_eval_map (ρ : Val) (ns : List Nat) :
    (ns.map OByte.lit).map (OByte.eval ρ) = ns.map (· % 256) := by
  simp [List.map_map, Function.comp_def, OByte.eval]

theorem panic_out (ρ : Val) :
    (panicBytes 0x11).map (OByte.eval ρ) =
      SolarTV.Milestone.VerifyCounter.Bump.panicData.map BitVec.toNat := by
  have e : panicBytes 0x11 = ((SolarTV.Milestone.VerifyCounter.Bump.panicData.map BitVec.toNat).map OByte.lit) := by
    decide +kernel
  rw [e, lit_eval_map, List.map_map]
  apply List.map_congr_left
  intro b _
  exact Nat.mod_eq_of_lt b.isLt

theorem over_out (ρ : Val) {bs : List OByte} (h : errorBytes "over" = some bs) :
    bs.map (OByte.eval ρ) = SolarTV.Milestone.VerifyCounter.Bump.overData.map BitVec.toNat := by
  have e : errorBytes "over" = some ((SolarTV.Milestone.VerifyCounter.Bump.overData.map BitVec.toNat).map OByte.lit) := by
    decide +kernel
  rw [e, Option.some.injEq] at h
  subst h
  rw [lit_eval_map, List.map_map]
  apply List.map_congr_left
  intro b _
  exact Nat.mod_eq_of_lt b.isLt

/-- The call of `bump(a)` from the storage `σ`. -/
def bumpCall (σ : List (Nat × Nat)) (a : Nat) : Call :=
  { calldata := Abi.calldata bumpSel [a], callvalue := 0, storage := σ }

theorem toNat_ofNat_lt {w n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The call of `bump(a)`: bump's selector, and `a` as its word. -/
theorem bumpCall_facts (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) :
    SolarTV.Milestone.VerifyCounter.Bump.IsBump (bumpCall σ a) ∧
      calldataWord (bumpCall σ a) 4 = BitVec.ofNat 256 a := by
  have hf : CallFacts bumpSel 1 ⟨[a], slotValue σ, solHash⟩ (bumpCall σ a) :=
    callFacts bumpSel (by decide) [a] (by simpa using ha) σ
  refine ⟨?_, ?_⟩
  · unfold SolarTV.Milestone.VerifyCounter.Bump.IsBump
    rw [hf.selector]
    rfl
  · apply BitVec.eq_of_toNat_eq
    have h4 := hf.args 0 (by decide) (by decide)
    rw [toNat_ofNat_lt ha]
    simpa [WExpr.eval, Nat.mod_eq_of_lt ha] using h4

/-- **bump's end on the first lowered MIR**, on the call of `bump(a)`: it exists, logs nothing,
and is the exact end `PostX` names, read on the call's words. -/
theorem mir_end (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) :
    ∃ r, MIR.Lowered.moduleLayer.Ends o SolarTV.Export.Counter.stage0 (bumpCall σ a) r ∧
      logs r.2 = [] ∧
      (BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a < BitVec.ofNat 256 (slotValue σ 0) →
        r.1 = .revert SolarTV.Milestone.VerifyCounter.Bump.panicData) ∧
      (¬ BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a < BitVec.ofNat 256 (slotValue σ 0) →
        BitVec.ofNat 256 (slotValue σ 1) < BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a →
        r.1 = .revert SolarTV.Milestone.VerifyCounter.Bump.overData) ∧
      (¬ BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a < BitVec.ofNat 256 (slotValue σ 0) →
        ¬ BitVec.ofNat 256 (slotValue σ 1) < BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a →
        r.1 = .stop ∧ r.2.storage 0 = BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a ∧
          ∀ k, k ≠ 0 → r.2.storage k = (Machine.State.initial (bumpCall σ a)).storage k) := by
  obtain ⟨hsel, hn⟩ := bumpCall_facts σ a ha
  have hf : CallFacts bumpSel 1 ⟨[a], slotValue σ, solHash⟩ (bumpCall σ a) :=
    callFacts bumpSel (by decide) [a] (by simpa using ha) σ
  obtain ⟨r, e, hpost⟩ := SolarTV.Milestone.VerifyCounter.Bump.xstage0_ends o _ hsel
  have hsz : ¬ BitVec.ofNat 256 (bumpCall σ a).calldata.size < 36 := by
    rw [hf.size]; decide
  have hp := hpost rfl hsz
  have hs0 : (Machine.State.initial (bumpCall σ a)).storage 0 = BitVec.ofNat 256 (slotValue σ 0) := rfl
  have hs1 : (Machine.State.initial (bumpCall σ a)).storage 1 = BitVec.ofNat 256 (slotValue σ 1) := rfl
  rw [hn, hs0, hs1] at hp
  exact ⟨r, e, MIR.Lowered.Module.ends_logs stage0_noLog e, hp⟩

theorem mir_run {o : Oracle} {σ : List (Nat × Nat)} {a : Nat} {r : Halt × Machine.State}
    (e : MIR.Lowered.moduleLayer.Ends o SolarTV.Export.Counter.stage0 (bumpCall σ a) r) :
    (SolarTV.mirSem o).run SolarTV.Export.Counter.stage0 (bumpCall σ a) =
      some (observe (bumpCall σ a) r.2 r.1) := by
  show (MIR.Lowered.moduleLayer.result o _ _).map _ = _
  rw [MIR.Lowered.moduleLayer.result_of_ends e]
  rfl

set_option maxHeartbeats 1000000 in
/-- **bump's first lowered MIR shows SolidCore's observable**, on every call of `bump`, under
every oracle. -/
theorem mir_eq (o : Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) :
    (SolarTV.mirSem o).run SolarTV.Export.Counter.stage0 (bumpCall σ a) =
      runtimeRun fuel c (bumpCall σ a) := by
  obtain ⟨T, hT⟩ := tree_ok
  rw [show runtimeRun fuel c (bumpCall σ a) = _ from runs hc hT σ a ha]
  obtain ⟨r, e, hl, hp1, hp2, hp3⟩ := mir_end o σ a ha
  rw [mir_run e]
  congr 1
  have h0lt : slotValue σ 0 < 2 ^ 256 := slotValue_lt σ 0
  have h1lt : slotValue σ 1 < 2 ^ 256 := slotValue_lt σ 1
  have c1 : (BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a < BitVec.ofNat 256 (slotValue σ 0)) ↔
      (slotValue σ 0 + a) % 2 ^ 256 < slotValue σ 0 := by
    rw [BitVec.lt_def, BitVec.toNat_add, toNat_ofNat_lt h0lt, toNat_ofNat_lt ha]
  have c2 : (BitVec.ofNat 256 (slotValue σ 1) < BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a) ↔
      slotValue σ 1 < (slotValue σ 0 + a) % 2 ^ 256 := by
    rw [BitVec.lt_def, BitVec.toNat_add, toNat_ofNat_lt h0lt, toNat_ofNat_lt ha, toNat_ofNat_lt h1lt]
  -- the tree's leaf
  set ρ : Val := ⟨[a], slotValue σ, solHash⟩ with hρ
  obtain ⟨T', hT', hTe⟩ := brTree_eval bumpFn (argFacts [256] 0) ρ bumpBr T hT
  rw [← hTe]
  have hna : nOf ρ = a := by
    simp only [nOf, WExpr.eval, hρ, List.getD_cons_zero]; exact Nat.mod_eq_of_lt ha
  have eovf : ovf.eval ρ = if (slotValue σ 0 + a) % 2 ^ 256 < slotValue σ 0 then 1 else 0 := by
    simp only [ovf, WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero, Nat.mod_eq_of_lt h0lt,
      Nat.mod_eq_of_lt ha, Nat.mod_mod]
    split <;> rfl
  have ele : le.eval ρ = if slotValue σ 1 < (slotValue σ 0 + a) % 2 ^ 256 then 0 else 1 := by
    simp only [le, WExpr.eval, BinOp.eval, UnOp.eval, hρ, List.getD_cons_zero, Nat.mod_eq_of_lt h0lt,
      Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt ha, Nat.mod_mod]
    split <;> rfl
  obtain ⟨M, hM⟩ : ∃ M, (slotValue σ 0 + a) % 2 ^ 256 = M := ⟨_, rfl⟩
  rw [hM] at eovf ele c1 c2
  obtain ⟨h, st⟩ := r
  unfold bumpBr at hT'
  rw [guards_eval] at hT'
  by_cases hg : [ovf].any (fun g => g.eval ρ != 0) = true
  · -- count + n wraps: Panic(0x11)
    rw [if_pos hg] at hT'
    have hw : M < slotValue σ 0 := by
      by_contra hw
      simp [eovf, hw] at hg
    have hh : h = .revert SolarTV.Milestone.VerifyCounter.Bump.panicData := hp1 (c1.mpr hw)
    subst hh
    simp only [leafTree, Option.some.injEq] at hT'
    subst hT'
    simp only [observe, Tree.eval, Res.obs, Bool.false_eq_true, ↓reduceIte, panic_out]
    rfl
  rw [if_neg hg] at hT'
  have hw : ¬ M < slotValue σ 0 := by
    intro hw
    exact hg (by simp [eovf, hw])
  simp only [Br.eval] at hT'
  by_cases hv : le.eval ρ = 0
  · -- count + n exceeds limit: Error("over")
    rw [if_pos hv] at hT'
    have hgt : slotValue σ 1 < M := by
      by_contra hgt
      simp [ele, hgt] at hv
    have hh : h = .revert SolarTV.Milestone.VerifyCounter.Bump.overData :=
      hp2 (fun h' => hw (c1.mp h')) (c2.mpr hgt)
    subst hh
    simp only [leafTree, Option.map_eq_some_iff] at hT'
    obtain ⟨bs, hbs, rfl⟩ := hT'
    simp only [observe, Tree.eval, Res.obs, Bool.false_eq_true, ↓reduceIte, over_out ρ hbs]
    rfl
  rw [if_neg hv] at hT'
  have hle : ¬ slotValue σ 1 < M := by
    intro hgt
    exact hv (by simp [ele, hgt])
  obtain ⟨hstop, hst0, hstk⟩ := hp3 (fun h' => hw (c1.mp h')) (fun h' => hle (c2.mp h'))
  simp only at hstop hst0 hstk hl
  subst hstop
  have hT2 : T' = .halt true [] [(.lit 0, .bin .add (.init 0) (.arg 0))] [] := by
    simp [leafTree, bumpFn, SF, retsOk] at hT'
    first | exact hT'.symm | exact hT'
  subst hT2
  simp only [observe, Tree.eval, Res.obs, ↓reduceIte, List.map_nil, hl]
  congr 1
  funext k
  simp only [storageOf, Writes.store, WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero]
  by_cases hk : k % 2 ^ 256 = 0
  · have hk' : BitVec.ofNat 256 k = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hk]; rfl
    rw [hk', hst0, BitVec.toNat_add, toNat_ofNat_lt h0lt, toNat_ofNat_lt ha, if_pos (by rw [hk]; rfl)]
    rw [Nat.mod_eq_of_lt h0lt, Nat.mod_eq_of_lt ha, Nat.mod_mod]
  · have hk' : BitVec.ofNat 256 k ≠ 0 := by
      intro h0; apply hk
      have := congrArg BitVec.toNat h0
      rwa [BitVec.toNat_ofNat] at this
    rw [hstk _ hk', if_neg (by rw [Nat.zero_mod]; exact fun h => hk h.symm)]
    show (BitVec.ofNat 256 (slotValue σ (BitVec.ofNat 256 k).toNat)).toNat = slotValue σ k
    rw [toNat_ofNat_lt (slotValue_lt σ _), BitVec.toNat_ofNat]
    exact slotValue_mod σ k

/-- What a call of `bump` can show in SolidCore: success, `Panic(0x11)`'s data or
`Error("over")`'s data, never another revert. -/
theorem result_kinds (o : Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) {obs : Observable}
    (h : runtimeRun fuel c (bumpCall σ a) = some obs) :
    obs.success = true ∨ obs.output = SolarTV.Milestone.VerifyCounter.Bump.panicData.map BitVec.toNat ∨
      obs.output = SolarTV.Milestone.VerifyCounter.Bump.overData.map BitVec.toNat := by
  rw [← mir_eq o hc σ a ha] at h
  obtain ⟨r, e, -, hp1, hp2, hp3⟩ := mir_end o σ a ha
  rw [mir_run e, Option.some.injEq] at h
  subst h
  obtain ⟨hh, st⟩ := r
  by_cases w : BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a < BitVec.ofNat 256 (slotValue σ 0)
  · have := hp1 w; simp only at this; subst this; exact Or.inr (Or.inl rfl)
  by_cases v : BitVec.ofNat 256 (slotValue σ 1) < BitVec.ofNat 256 (slotValue σ 0) + BitVec.ofNat 256 a
  · have := hp2 w v; simp only at this; subst this; exact Or.inr (Or.inr rfl)
  · have := (hp3 w v).1; simp only at this; subst this; exact Or.inl rfl

/-- **The source stage of bump**, under every oracle. -/
theorem stage (o : Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCoreRuntime fuel) (SolarTV.mirSem o) c SolarTV.Export.Counter.stage0 BumpCall := by
  rintro _ ⟨σ, a, ha, rfl⟩ obs h
  exact (mir_eq o hc σ a ha).trans h

/-- The converse stage: every result of `stage0` on a call of `bump` is SolidCore's. -/
theorem stage_back (o : Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (SolarTV.mirSem o) (solidCoreRuntime fuel) SolarTV.Export.Counter.stage0 c BumpCall := by
  rintro _ ⟨σ, a, ha, rfl⟩ obs h
  exact (mir_eq o hc σ a ha).symm.trans h

/-- info: 'Contracts.VerifyCounter.Source.mir_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mir_eq

end Contracts.VerifyCounter.Source
