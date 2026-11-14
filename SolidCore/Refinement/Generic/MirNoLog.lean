import SolarTV.MIR.Program

/-!
# A lowered MIR module without `LOG` logs nothing

`Module.noLog m` checks that no instruction of `m` is a `log` effect. Then every end of `m`
on every call, under every oracle, has no logs (`Module.run_logs`, `Module.ends_logs`):
every other effect leaves the logs as they were (external calls, creations and `GAS` append
events to the world, but none is a log), and so do internal calls, returns and halts.

The proof is one invariant of `moduleBlock`'s frames (`FrameOk`): the state has no logs, and
the instructions still to run (in the frame and in every pending return) are free of `log`,
since they are suffixes of `m`'s blocks.
-/

namespace SolarTV.MIR.Lowered

open SolarTV.Machine

/-- An instruction that is not a `log` effect. -/
def Inst.noLog : Inst → Bool
  | .effect _ (.log _) _ => false
  | _ => true

/-- No instruction of the module is a `log` effect. -/
def Module.noLog (m : Module) : Bool :=
  m.functions.all fun f => f.blocks.all fun b => b.insts.all Inst.noLog

/-- The log an event is, if it is one. -/
def logOf : Event → Option (List Nat × List Nat)
  | .log topics data => some (topics.map BitVec.toNat, data.map BitVec.toNat)
  | _ => none

theorem logs_eq (s : State) : logs s = s.world.filterMap logOf := by
  unfold logs
  congr 1
  funext e
  cases e <;> rfl

/-- Every effect but `log` leaves the logs as they were. -/
theorem Effect.apply_logs {o : Oracle} {call : Call} {e : Effect} {args : List EvmRules.Word} {s s' : State}
    {r : Option EvmRules.Word} (he : ∀ n, e ≠ .log n) (h : e.apply o call args s = some (r, s')) :
    logs s' = logs s := by
  unfold Effect.apply at h
  split at h
  all_goals first
    | exact absurd rfl (he _)
    | skip
  all_goals (repeat' split at h)
  all_goals (cases h)
  all_goals first
    | rfl
    | (simp [logs_eq, List.filterMap_append, logOf]; done)
    | (unfold called; split <;> simp [logs_eq, List.filterMap_append, logOf])

theorem Inst.noLog_effect {dst : Option Nat} {e : Effect} {args : List Operand}
    (h : Inst.noLog (.effect dst e args) = true) : ∀ n, e ≠ .log n := by
  rintro n rfl
  simp [Inst.noLog] at h

/-- Instructions without `log` leave the logs as they were. -/
theorem execInsts_logs {o : Oracle} {call : Call} :
    ∀ {is : List Inst} {env : Env} {s : State} {env' : Env} {s' : State},
      is.all Inst.noLog = true → execInsts o call is env s = some (env', s') → logs s' = logs s
  | [], _, _, _, _, _, h => by
    simp only [execInsts, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | i :: is, env, s, env', s', hno, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hno
    obtain ⟨hi, hno⟩ := hno
    cases i with
    | effect dst e args =>
      simp only [execInsts] at h
      split at h
      · rename_i res s1 hres
        exact (execInsts_logs hno h).trans (Effect.apply_logs (Inst.noLog_effect hi) hres)
      · cases h
    | call => simp [execInsts] at h
    | alloc dst p =>
      cases p with
      | static a => exact execInsts_logs hno h
      | dynamic size =>
        simp only [execInsts] at h
        have := execInsts_logs hno h
        exact this
    | pure dst op args =>
      simp only [execInsts] at h
      split at h
      · exact execInsts_logs hno h
      · cases h
    | assume neg op args =>
      simp only [execInsts] at h
      split at h
      · split at h <;> split at h
        all_goals first | cases h | exact execInsts_logs hno h
      · cases h
    | ne => exact execInsts_logs hno h
    | word => exact execInsts_logs hno h
    | low => exact execInsts_logs hno h
    | select => exact execInsts_logs hno h
    | heapFloor => exact execInsts_logs hno h

theorem splitCall_cons_of (i : Inst) (hi : ∀ d c a x p, i ≠ .call d c a x p) (is : List Inst) :
    splitCall (i :: is) = (i :: (splitCall is).1, (splitCall is).2) := by
  cases i <;> first | rfl | exact absurd rfl (hi _ _ _ _ _)

theorem splitCall_noLog : ∀ {is : List Inst}, is.all Inst.noLog = true →
    (splitCall is).1.all Inst.noLog = true ∧
      ∀ d c a x p rest, (splitCall is).2 = some (d, c, a, x, p, rest) → rest.all Inst.noLog = true
  | [], _ => ⟨rfl, fun _ _ _ _ _ _ h => by cases h⟩
  | i :: is, hno => by
    simp only [List.all_cons, Bool.and_eq_true] at hno
    by_cases hc : ∃ d c a x p, i = .call d c a x p
    · obtain ⟨d, c, a, x, p, rfl⟩ := hc
      refine ⟨rfl, ?_⟩
      intro d' c' a' x' p' rest' hn
      have hn' : some (d, c, a, x, p, is) = some (d', c', a', x', p', rest') := hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn'
      obtain ⟨-, -, -, -, -, rfl⟩ := hn'
      exact hno.2
    · have hi : ∀ d c a x p, i ≠ .call d c a x p := fun d c a x p h => hc ⟨d, c, a, x, p, h⟩
      rw [splitCall_cons_of i hi]
      obtain ⟨h1, h2⟩ := splitCall_noLog hno.2
      exact ⟨by simp only [List.all_cons, hno.1, h1, Bool.and_self], h2⟩

theorem splitCall_noLog_eq {is before : List Inst}
    {next : Option (Option Nat × Nat × List Operand × List (Option Nat) × Option EvmRules.Word × List Inst)}
    (hno : is.all Inst.noLog = true) (h : splitCall is = (before, next)) :
    before.all Inst.noLog = true ∧
      ∀ d c a x p rest, next = some (d, c, a, x, p, rest) → rest.all Inst.noLog = true := by
  have := splitCall_noLog hno
  rw [h] at this
  exact this

theorem logs_start (f : Function) (s : State) : logs (f.start s) = logs s := by
  unfold Function.start
  split <;> rfl

theorem logs_publish (s : State) (p : Option EvmRules.Word) (vs : List EvmRules.Word) :
    logs (publishResults s p vs) = logs s := by
  unfold publishResults
  split <;> rfl

/-- What still runs in a frame is free of `log`, and its state has no logs. -/
def FrameOk (x : Frame) : Prop :=
  logs x.2.2.2 = [] ∧ (∀ r ∈ x.1, r.rest.all Inst.noLog = true) ∧
    match x.2.1 with
    | .resume _ _ is _ => is.all Inst.noLog = true
    | .enter .. => True

/-- An outcome of a step: an end without logs, or a frame that keeps the invariant. -/
def StepOk : (Halt × State) ⊕ Frame → Prop
  | .inl r => logs r.2 = []
  | .inr x => FrameOk x

theorem segment_ok {o : Oracle} {call : Call} {m : Module} {stack : List Return} {fn b : Nat}
    {insts : List Inst} {term : Terminator} {env : Env} {s : State} {y : (Halt × State) ⊕ Frame}
    (hl : logs s = []) (hst : ∀ r ∈ stack, r.rest.all Inst.noLog = true)
    (hno : insts.all Inst.noLog = true)
    (h : segment o call m stack fn b insts term env s = some y) : StepOk y := by
  unfold segment at h
  split at h
  · rename_i before dst callee args extras publish rest hsplit
    obtain ⟨hb, hr⟩ := splitCall_noLog_eq hno hsplit
    split at h
    · cases h
    · rename_i env1 s1 hex
      have hl1 : logs s1 = [] := (execInsts_logs hb hex).trans hl
      split at h
      · cases h
      · split at h
        · cases h
        · obtain rfl := Option.some.inj h
          refine ⟨(logs_start _ _).trans hl1, ?_, trivial⟩
          intro r hr'
          simp only [List.mem_cons] at hr'
          rcases hr' with rfl | hr'
          · exact hr dst callee args extras publish rest rfl
          · exact hst r hr'
  · rename_i before hsplit
    obtain ⟨hb, -⟩ := splitCall_noLog_eq hno hsplit
    split at h
    · cases h
    · rename_i env1 s1 hex
      have hl1 : logs s1 = [] := (execInsts_logs hb hex).trans hl
      split at h
      all_goals first
        | (obtain rfl := Option.some.inj h; exact ⟨hl1, hst, trivial⟩)
        | (obtain rfl := Option.some.inj h; exact hl1)
        | skip
      · -- tailCall
        split at h
        · cases h
        · split at h
          · cases h
          · obtain rfl := Option.some.inj h
            exact ⟨(logs_start _ _).trans hl1, hst, trivial⟩
      · -- leave
        cases stack with
        | nil => cases h
        | cons ret stack' =>
          simp only at h
          split at h
          · cases h
          · obtain rfl := Option.some.inj h
            refine ⟨(logs_publish _ _ _).trans hl1, fun r hr => hst r (List.mem_cons_of_mem _ hr), ?_⟩
            exact hst ret List.mem_cons_self

theorem block_noLog {m : Module} (hm : m.noLog = true) {fn b : Nat} {f : Function} {blk : Block}
    (hf : m.functions[fn]? = some f) (hb : f.blocks[b]? = some blk) : blk.insts.all Inst.noLog = true := by
  unfold Module.noLog at hm
  rw [List.all_eq_true] at hm
  have h1 := hm f (List.mem_of_getElem? hf)
  rw [List.all_eq_true] at h1
  exact h1 blk (List.mem_of_getElem? hb)

theorem step_ok {o : Oracle} {call : Call} {m : Module} (hm : m.noLog = true) {x : Frame}
    {y : (Halt × State) ⊕ Frame} (hx : FrameOk x) (h : moduleBlock o call m x = some y) : StepOk y := by
  obtain ⟨stack, pos, env, s⟩ := x
  obtain ⟨hl, hst, hpos⟩ := hx
  cases pos with
  | enter fn p b =>
    simp only [moduleBlock] at h
    split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i blk hb
        split at h
        · cases h
        · exact segment_ok hl hst (block_noLog hm hf hb) h
  | resume fn b is term =>
    simp only [moduleBlock] at h
    exact segment_ok hl hst hpos h

theorem iterate_ok {o : Oracle} {call : Call} {m : Module} (hm : m.noLog = true) :
    ∀ (n : Nat) (x : Frame) (r : Halt × State), FrameOk x →
      iterate (moduleBlock o call m) n x = some r → logs r.2 = []
  | 0, _, _, _, h => by simp [iterate] at h
  | n + 1, x, r, hx, h => by
    unfold iterate at h
    split at h
    · rename_i res hs
      obtain rfl := Option.some.inj h
      exact step_ok hm hx hs
    · rename_i next hs
      exact iterate_ok hm n next r (step_ok hm hx hs) h
    · cases h

/-- **A module without `log` ends with no logs**, on every call under every oracle. -/
theorem Module.run_logs {o : Oracle} {call : Call} {m : Module} (hm : m.noLog = true) {n : Nat}
    {r : Halt × State} (h : Module.run o m call n = some r) : logs r.2 = [] := by
  refine iterate_ok hm n ([], .enter m.entry 0 0, fun _ => 0, m.startState (State.initial call)) r ?_ h
  unfold FrameOk
  dsimp only
  refine ⟨?_, fun _ h => by simp at h, trivial⟩
  show logs (m.startState (State.initial call)) = []
  unfold Module.startState
  split
  · exact (logs_start _ _).trans rfl
  · rfl

theorem Module.ends_logs {o : Oracle} {call : Call} {m : Module} (hm : m.noLog = true)
    {r : Halt × State} (h : moduleLayer.Ends o m call r) : logs r.2 = [] := by
  obtain ⟨n, hn⟩ := h
  exact Module.run_logs hm hn

/-- info: 'SolarTV.MIR.Lowered.Module.ends_logs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.ends_logs

end SolarTV.MIR.Lowered
