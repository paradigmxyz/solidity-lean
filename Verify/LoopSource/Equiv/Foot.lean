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

/-- `(senv', st')` differs from `(senv, st)` only at the values `D` and in the words at `MO`. -/
private def Changes (D MO : List Nat) (senv senv' : SEnv) (st st' : SState) : Prop :=
  (∀ j, j ∉ D → senv' j = senv j) ∧ (∀ i, ¬ Covered MO i → st'.mem i = st.mem i)

private theorem Changes.rfl' {D MO : List Nat} {senv : SEnv} {st : SState} : Changes D MO senv senv st st :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

private theorem Changes.set {MO : List Nat} {senv : SEnv} {st : SState} (d : Nat) (v : SV) :
    Changes [d] MO senv (senv.set d v) st st :=
  ⟨fun j hj => by simp [SEnv.set, List.mem_singleton.not.mp hj], fun _ _ => rfl⟩

private theorem Changes.trans {D D' MO MO' : List Nat} {e1 e2 e3 : SEnv} {s1 s2 s3 : SState}
    (h1 : Changes D MO e1 e2 s1 s2) (h2 : Changes D' MO' e2 e3 s2 s3) :
    Changes (D ++ D') (MO ++ MO') e1 e3 s1 s3 :=
  ⟨fun j hj => by simp only [List.mem_append, not_or] at hj; rw [h2.1 j hj.2, h1.1 j hj.1],
    fun i hi => by obtain ⟨c1, c2⟩ := not_covered_append hi; rw [h2.2 i c2, h1.2 i c1]⟩

/-- A footprint, grown by what a run changes, holds after it. -/
private theorem Frame.changes {D D' MO MO' : List Nat} {senv senv' : SEnv} {st st' : SState}
    (hF : Frame D MO senv st) (h : Changes D' MO' senv senv' st st') : Frame (D ++ D') (MO ++ MO') senv' st' :=
  ⟨fun j hj => by simp only [List.mem_append, not_or] at hj; rw [h.1 j hj.2]; exact hF.1 j hj.1,
    fun i hi => by obtain ⟨c1, c2⟩ := not_covered_append hi; rw [h.2 i c2]; exact hF.2 i c1⟩

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

/-- One instruction changes only what `instDsts` and `instMem` list. -/
private theorem symInsts_cons {ev : EnvFlags} {cv : SV} {sel n : Nat} {K : Facts} {inst : Inst}
    {rest : List Inst} {senv senv' : SEnv} {st st' : SState} {o1 : List Nat}
    (h : symInsts ev cv sel n K (inst :: rest) senv st = some (senv', st')) (hi : instMem inst = some o1) :
    ∃ senv1 st1, Changes (instDsts inst) o1 senv senv1 st st1 ∧
      symInsts ev cv sel n K rest senv1 st1 = some (senv', st') := by
  cases inst with
  | effect d eff args =>
    simp only [symInsts] at h
    split at h
    · rename_i res st2 he
      refine ⟨_, _, ⟨fun j hj => ?_, effect_mem he hi⟩, h⟩
      clear h
      cases d <;> cases res <;> simp_all [instDsts, SEnv.set]
    · simp at h
  | assume neg op args =>
    simp only [symInsts] at h
    repeat' split at h
    all_goals first | exact ⟨_, _, Changes.rfl', h⟩ | simp at h
  | _ =>
    simp only [symInsts] at h
    repeat' split at h
    all_goals first | exact ⟨_, _, Changes.set _ _, h⟩ | simp at h

private theorem symInsts_foot {ev : EnvFlags} {cv : SV} {sel n : Nat} {K : Facts} :
    ∀ (insts : List Inst) (senv senv' : SEnv) (st st' : SState) (offs : List (List Nat)),
      symInsts ev cv sel n K insts senv st = some (senv', st') → insts.mapM instMem = some offs →
      Changes (insts.flatMap instDsts) offs.flatten senv senv' st st'
  | [], senv, senv', st, st', offs, h, _ => by
    simp only [symInsts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Changes.rfl'
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
    obtain ⟨_, _, h1, h2⟩ := symInsts_cons h hi
    exact h1.trans (symInsts_foot rest _ _ _ _ os h2 hr)

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
      | (simp only [Option.some.injEq] at h; subst h; first | trivial | exact fun _ => hF.changes Changes.rfl')
      | simp at h

/-- A segment from a footprint that already holds its block's phis `pre`. -/
theorem symSegment_frame {ev : EnvFlags} {cv : SV} {m : Module} {sel n : Nat} {K : Facts}
    {fn b : Nat} {insts : List Inst} {term : Terminator} {senv : SEnv} {st : SState} {x : SNext}
    {D MO pre d mo : List Nat} (hF : Frame (D ++ pre) MO senv st)
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
        simpa only [List.append_assoc] using
          symTerm_frame (hF.changes (symInsts_foot insts _ _ _ _ offs hi ho)) h
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
          refine symSegment_frame ⟨fun j hj => ?_, hF.2⟩ hfoot h
          simp only [List.mem_append, not_or] at hj
          rw [symPhis_foot _ _ _ hp j hj.2]; exact hF.1 j hj.1
  | resume fn b insts term =>
    simp only [stepFoot] at hfoot
    exact symSegment_frame (by rwa [List.append_nil]) hfoot h

end Verify.LoopSource.Equiv
