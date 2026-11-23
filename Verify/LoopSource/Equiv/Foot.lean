import Verify.LoopSource.Equiv.Cut

/-!
# Footprints of the symbolic steps

One symbolic step of the module (`symStep`) with no call in progress binds only the values and
writes only the memory words `stepFoot` lists, and after a tail call every value outside the
callee's parameters is the word 0. So `Frame`, the footprint of a cut-point run, holds along it
(`frame_step`).
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement.Generic

theorem not_covered_append {a b : List Nat} {i : Nat} (h : ¬ Covered (a ++ b) i) :
    ¬ Covered a i ∧ ¬ Covered b i :=
  ⟨fun ⟨o, ho, h1⟩ => h ⟨o, List.mem_append_left _ ho, h1⟩,
    fun ⟨o, ho, h1⟩ => h ⟨o, List.mem_append_right _ ho, h1⟩⟩

/-- A footprint holds for any larger one. -/
theorem Frame.mono {D D' MO MO' : List Nat} {senv : SEnv} {st : SState} (h : Frame D MO senv st)
    (hD : ∀ j ∈ D, j ∈ D') (hM : ∀ o ∈ MO, o ∈ MO') : Frame D' MO' senv st :=
  ⟨fun j hj => h.1 j (fun hm => hj (hD j hm)),
    fun i hi => h.2 i (fun ⟨o, ho, h1⟩ => hi ⟨o, hM o ho, h1⟩)⟩

theorem splitCall_of_noCall : ∀ insts : List Inst, insts.all (fun i => !isCallInst i) = true →
    splitCall insts = (insts, none)
  | [], _ => rfl
  | i :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitCall_of_noCall rest h.2
    cases i <;> simp_all [isCallInst, splitCall]

theorem storeBytes_out {mem : Nat → OByte} {off i : Nat} {e : WExpr} (h : ¬ (off ≤ i ∧ i < off + 32)) :
    storeBytes mem off e i = mem i := by
  simp [storeBytes, h]

theorem symEffect_mem_of_ne {ev : EnvFlags} {cv : SV} {n : Nat} {eff : Effect} {args : List SV}
    {st st' : SState} {r : Option SV} (hne : eff ≠ .mstore)
    (h : symEffect ev cv n eff args st = some (r, st')) : st'.mem = st.mem := by
  unfold symEffect at h
  split at h <;> (repeat' split at h) <;> simp_all <;> (try obtain ⟨_, _, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

theorem symEffect_mstore {ev : EnvFlags} {cv : SV} {n : Nat} {args : List SV}
    {st st' : SState} {r : Option SV} (h : symEffect ev cv n .mstore args st = some (r, st')) :
    ∃ off e, args = [.w (.lit off), .w e] ∧ st'.mem = storeBytes st.mem (off % wordSize) e := by
  unfold symEffect at h
  split at h <;> simp_all <;> (obtain ⟨-, rfl⟩ := h; rfl)

/-- An effect writes memory only where `instMem` says. -/
theorem effect_mem {ev : EnvFlags} {cv : SV} {n : Nat} {dst : Option Nat} {eff : Effect}
    {args : List Operand} {senv : SEnv} {st st' : SState} {r : Option SV} {o1 : List Nat}
    (h : symEffect ev cv n eff (args.map (SV.ofOperand senv)) st = some (r, st'))
    (hi : instMem (.effect dst eff args) = some o1) : ∀ i, ¬ Covered o1 i → st'.mem i = st.mem i := by
  by_cases he : eff = .mstore
  · subst he
    obtain ⟨off, e, ha, hm⟩ := symEffect_mstore h
    match args, ha, hi with
    | .const w :: rest, ha, hi =>
      simp only [instMem, Option.some.injEq] at hi
      subst hi
      simp only [List.map_cons, SV.ofOperand, List.cons.injEq, SV.w.injEq, WExpr.lit.injEq] at ha
      intro i hc
      rw [hm, ← ha.1]
      exact storeBytes_out fun hb => hc ⟨_, List.mem_singleton_self _, hb⟩
    | .value _ :: _, _, hi => simp [instMem] at hi
    | [], _, hi => simp [instMem] at hi
  · intro i _
    rw [symEffect_mem_of_ne he h]

theorem symInsts_foot {ev : EnvFlags} {cv : SV} {sel n : Nat} {K : Facts} :
    ∀ (insts : List Inst) (senv senv' : SEnv) (st st' : SState) (offs : List (List Nat)),
      symInsts ev cv sel n K insts senv st = some (senv', st') → insts.mapM instMem = some offs →
      (∀ j, j ∉ insts.flatMap instDsts → senv' j = senv j) ∧
      (∀ i, ¬ Covered offs.flatten i → st'.mem i = st.mem i)
  | [], senv, senv', st, st', offs, h, _ => by
    simp only [symInsts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | inst :: rest, senv, senv', st, st', offs, h, ho => by
    rw [List.mapM_cons] at ho
    cases hi : instMem inst with
    | none => simp [hi] at ho
    | some o1 =>
    cases hr : rest.mapM instMem with
    | none => simp [hi, hr] at ho
    | some os =>
    simp [hi, hr] at ho
    subst ho
    have cov : ∀ i, ¬ Covered (o1 :: os).flatten i → ¬ Covered o1 i ∧ ¬ Covered os.flatten i :=
      fun i hc => not_covered_append (by simpa using hc)
    have dst : ∀ j, j ∉ (inst :: rest).flatMap instDsts → j ∉ instDsts inst ∧ j ∉ rest.flatMap instDsts :=
      fun j hj => by simp only [List.flatMap_cons, List.mem_append, not_or] at hj; exact hj
    have setk : ∀ d v, (∀ j, j ∉ instDsts inst → j ≠ d) →
        symInsts ev cv sel n K rest (senv.set d v) st = some (senv', st') →
        (∀ j, j ∉ (inst :: rest).flatMap instDsts → senv' j = senv j) ∧
        (∀ i, ¬ Covered (o1 :: os).flatten i → st'.mem i = st.mem i) := fun d v hd hv => by
      obtain ⟨h1, h2⟩ := symInsts_foot rest _ _ _ _ os hv hr
      refine ⟨fun j hj => ?_, fun i hc => h2 i (cov i hc).2⟩
      obtain ⟨hj1, hj2⟩ := dst j hj
      rw [h1 j hj2]
      simp [SEnv.set, hd j hj1]
    have keep : symInsts ev cv sel n K rest senv st = some (senv', st') →
        (∀ j, j ∉ (inst :: rest).flatMap instDsts → senv' j = senv j) ∧
        (∀ i, ¬ Covered (o1 :: os).flatten i → st'.mem i = st.mem i) := fun hv => by
      obtain ⟨h1, h2⟩ := symInsts_foot rest _ _ _ _ os hv hr
      exact ⟨fun j hj => h1 j (dst j hj).2, fun i hc => h2 i (cov i hc).2⟩
    cases inst with
    | pure d op args =>
      simp only [symInsts] at h
      split at h
      · exact setk d _ (fun j hj => by simpa [instDsts] using hj) h
      · simp at h
    | effect d eff args =>
      simp only [symInsts] at h
      split at h
      · rename_i res st2 he
        obtain ⟨h1, h2⟩ := symInsts_foot rest _ _ _ _ os h hr
        have hm := effect_mem he hi
        refine ⟨fun j hj => ?_, fun i hc => by rw [h2 i (cov i hc).2, hm i (cov i hc).1]⟩
        obtain ⟨hj1, hj2⟩ := dst j hj
        rw [h1 j hj2]
        cases d <;> cases res <;> simp_all [instDsts, SEnv.set]
      · simp at h
    | ne d a b =>
      simp only [symInsts] at h
      have hd : ∀ j, j ∉ instDsts (Inst.ne d a b) → j ≠ d := fun j hj => by simpa [instDsts] using hj
      split at h <;> (try split at h) <;> first | exact setk d _ hd h | simp at h
    | assume neg op args =>
      simp only [symInsts] at h
      repeat' split at h
      all_goals first | exact keep h | simp at h
    | word d a =>
      simp only [symInsts] at h
      split at h
      · exact setk d _ (fun j hj => by simpa [instDsts] using hj) h
      · simp at h
    | heapFloor d fl =>
      simp only [symInsts] at h
      exact setk d _ (fun j hj => by simpa [instDsts] using hj) h
    | call _ _ _ _ _ => simp [symInsts] at h
    | low _ _ _ => simp [symInsts] at h
    | select _ _ _ _ => simp [symInsts] at h
    | alloc _ _ => simp [symInsts] at h

theorem symPhis_foot {inc : SEnv} {pred : Nat} :
    ∀ (phis : List (Nat × List (Nat × Operand))) (env env' : SEnv),
      symPhis inc pred phis env = some env' → ∀ j, j ∉ phis.map Prod.fst → env' j = env j
  | [], env, env', h, j, _ => by simp only [symPhis, Option.some.injEq] at h; rw [h]
  | (d, arms) :: rest, env, env', h, j, hj => by
    simp only [symPhis] at h
    split at h
    · simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [symPhis_foot rest _ _ h j hj.2]
      simp [SEnv.set, hj.1]
    · simp at h

theorem symBindParams_foot : ∀ (ps : List Nat) (as : List SV) (env env' : SEnv),
    symBindParams ps as env = some env' → ∀ j, j ∉ ps → env' j = env j
  | [], [], env, env', h, j, _ => by simp only [symBindParams, Option.some.injEq] at h; rw [h]
  | p :: ps, a :: as, env, env', h, j, hj => by
    simp only [symBindParams] at h
    simp only [List.mem_cons, not_or] at hj
    rw [symBindParams_foot ps as _ _ h j hj.2]
    simp [SEnv.set, hj.1]
  | [], _ :: _, _, _, h, _, _ => by simp [symBindParams] at h
  | _ :: _, [], _, _, h, _, _ => by simp [symBindParams] at h

/-- What one symbolic step gives, with no call in progress, under a footprint. -/
def nextFrame (D MO : List Nat) : SNext → Prop
  | .done _ => True
  | .go stack _ senv st => stack = [] → Frame D MO senv st
  | .fork _ stack _ _ _ _ senv st => stack = [] → Frame D MO senv st

theorem nextFrame_mono {D D' MO MO' : List Nat} {x : SNext} (h : nextFrame D MO x)
    (hD : ∀ j ∈ D, j ∈ D') (hM : ∀ o ∈ MO, o ∈ MO') : nextFrame D' MO' x := by
  cases x <;> simp only [nextFrame] at h ⊢ <;> first | trivial | exact fun hs => (h hs).mono hD hM

theorem symStart_mem {g : Function} {st : SState} :
    ∀ i, ¬ Covered (match g.entryHeap with | some _ => [64] | none => []) i →
      (symStart g st).mem i = st.mem i := by
  intro i hc
  unfold symStart
  split
  · rfl
  · rename_i heap hg
    simp only [hg] at hc
    exact storeBytes_out fun hb => hc ⟨64, List.mem_singleton_self _, hb⟩

theorem symTerm_frame {m : Module} {fn b : Nat} {senv : SEnv} {st : SState} {term : Terminator}
    {x : SNext} {D MO : List Nat} (hF : Frame D MO senv st)
    (h : symTerm m [] fn b senv st term = some x) :
    nextFrame (D ++ (termFoot m term).1) (MO ++ (termFoot m term).2) x := by
  have hF' : Frame (D ++ (termFoot m term).1) (MO ++ (termFoot m term).2) senv st :=
    hF.mono (fun j hj => List.mem_append_left _ hj) (fun o ho => List.mem_append_left _ ho)
  cases term with
  | tailCall callee args =>
    simp only [symTerm] at h
    split at h
    · simp at h
    · rename_i g hg
      split at h
      · simp at h
      · rename_i env' hb
        simp only [Option.some.injEq] at h
        subst h
        intro _
        have hg' : m.functions[callee]? = some g := hg
        simp only [termFoot, hg']
        refine ⟨fun j hj => ?_, fun i hi => ?_⟩
        · simp only [List.mem_append, not_or] at hj
          rw [symBindParams_foot _ _ _ _ hb j hj.2]
        · obtain ⟨h1, h2⟩ := not_covered_append hi
          rw [symStart_mem i h2]
          exact hF.2 i h1
  | leave vs => simp [symTerm] at h
  | _ =>
    simp only [symTerm] at h
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; first | trivial | exact fun _ => hF')
      | simp at h

theorem segFoot_pre {m : Module} {insts : List Inst} {term : Terminator} {pre d mo : List Nat}
    (h : segFoot m insts term pre = some (d, mo)) : ∀ j ∈ pre, j ∈ d := by
  unfold segFoot at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro j hj
      simp [hj]
  · simp at h

theorem symSegment_frame {ev : EnvFlags} {cv : SV} {m : Module} {sel n : Nat} {K : Facts}
    {fn b : Nat} {insts : List Inst} {term : Terminator} {senv : SEnv} {st : SState} {x : SNext}
    {D MO pre d mo : List Nat} (hF : Frame D MO senv st)
    (hfoot : segFoot m insts term pre = some (d, mo))
    (h : symSegment ev cv m sel n K [] fn b insts term senv st = some x) :
    nextFrame (D ++ d) (MO ++ mo) x := by
  unfold segFoot at hfoot
  split at hfoot
  · rename_i hnc
    split at hfoot
    · simp at hfoot
    · rename_i offs ho
      simp only [Option.some.injEq, Prod.mk.injEq] at hfoot
      obtain ⟨rfl, rfl⟩ := hfoot
      unfold symSegment at h
      rw [splitCall_of_noCall insts hnc] at h
      simp only at h
      split at h
      · simp at h
      · rename_i senv2 st2 hi
        obtain ⟨h1, h2⟩ := symInsts_foot insts _ _ _ _ offs hi ho
        have hF2 : Frame (D ++ insts.flatMap instDsts) (MO ++ offs.flatten) senv2 st2 := by
          refine ⟨fun j hj => ?_, fun i hc => ?_⟩
          · simp only [List.mem_append, not_or] at hj
            rw [h1 j hj.2]; exact hF.1 j hj.1
          · obtain ⟨c1, c2⟩ := not_covered_append hc
            rw [h2 i c2]; exact hF.2 i c1
        exact nextFrame_mono (symTerm_frame hF2 h)
          (fun j hj => by simp only [List.mem_append] at hj ⊢; tauto)
          (fun o ho => by simp only [List.mem_append] at ho ⊢; tauto)
  · simp at hfoot

/-- **One step keeps the footprint**: what `stepFoot` lists, added to it. -/
theorem frame_step {ev : EnvFlags} {cv : SV} {m : Module} {sel n : Nat} {K : Facts} {pos : Pos}
    {senv : SEnv} {st : SState} {x : SNext} {D MO d mo : List Nat} (hF : Frame D MO senv st)
    (hfoot : stepFoot m pos = some (d, mo)) (h : symStep ev cv m sel n K [] pos senv st = some x) :
    nextFrame (D ++ d) (MO ++ mo) x := by
  cases pos with
  | enter fn pred b =>
    simp only [stepFoot] at hfoot
    simp only [symStep] at h
    split at hfoot
    · simp at hfoot
    · rename_i f hf
      simp only [hf] at h
      split at hfoot
      · simp at hfoot
      · rename_i blk hb
        simp only [hb] at h
        split at h
        · simp at h
        · rename_i senv1 hp
          have hF1 : Frame (D ++ blk.phis.map Prod.fst) MO senv1 st := by
            refine ⟨fun j hj => ?_, hF.2⟩
            simp only [List.mem_append, not_or] at hj
            rw [symPhis_foot _ _ _ hp j hj.2]; exact hF.1 j hj.1
          have hpre := segFoot_pre hfoot
          exact nextFrame_mono (symSegment_frame hF1 hfoot h)
            (fun j hj => by
              simp only [List.mem_append] at hj ⊢
              rcases hj with (hj | hj) | hj
              · exact Or.inl hj
              · exact Or.inr (hpre j hj)
              · exact Or.inr hj)
            (fun o ho => ho)
  | resume fn b insts term =>
    simp only [stepFoot] at hfoot
    exact symSegment_frame hF hfoot h

end Verify.LoopSource.Equiv
