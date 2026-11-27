import SolidCore.Refinement.Generic.CallMir
import SolidCore.Refinement.Generic.MirRun
import W1Proofs.Tactic
import SolidCore.Refinement.SourceOracle

/-!
# The symbolic run with one external call is sound

`symTreeC_sound`: on a call that gives the symbolic run what `CallFacts` says, under every oracle
that answers the external call the path reaches as the callee `A` does (`OAns`: the success flag,
the size and bytes of the return data, in the world that ends with the call and in that world
followed by events with no call), with the valuation's words after the `n` argument words the
answer's words (`Val.withAns`), SolarTV's lowered MIR shows the call tree's result.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered EvmRules

/-! ## Relations -/

/-- A word holds a value of the call fragment; a gas word holds every word. -/
def CV.Rel (ρ : Val) (call : Call) (v : Word) : CV → Prop
  | .v x => SV.Rel ρ call v x
  | .gas => True

def CEnvRel (ρ : Val) (call : Call) (env : Env) (cenv : CEnv) : Prop :=
  ∀ j, CV.Rel ρ call (env j) (cenv j)

def CArgsRel (ρ : Val) (call : Call) : List Word → List CV → Prop
  | [], [] => True
  | a :: as, s :: ss => CV.Rel ρ call a s ∧ CArgsRel ρ call as ss
  | _, _ => False

def COptRel (ρ : Val) (call : Call) : Option Word → Option CV → Prop
  | none, none => True
  | some v, some s => CV.Rel ρ call v s
  | _, _ => False

def CStackRel (ρ : Val) (call : Call) : List Return → List CReturn → Prop
  | [], [] => True
  | r :: rs, q :: qs =>
    r.fn = q.fn ∧ r.block = q.block ∧ r.dst = q.dst ∧ r.rest = q.rest ∧ r.term = q.term ∧
      r.extras = [] ∧ r.publish = none ∧ CEnvRel ρ call r.env q.env ∧ CStackRel ρ call rs qs
  | _, _ => False

theorem CEnvRel.set {ρ : Val} {call : Call} {env : Env} {cenv : CEnv} (h : CEnvRel ρ call env cenv)
    {v : Word} {s : CV} (hv : CV.Rel ρ call v s) (d : Nat) :
    CEnvRel ρ call (env.set d v) (cenv.set d s) := by
  intro j
  simp only [Env.set, CEnv.set]
  split
  · exact hv
  · exact h j

theorem crel_operand {ρ : Val} {call : Call} {env : Env} {cenv : CEnv} (h : CEnvRel ρ call env cenv)
    (op : Operand) : CV.Rel ρ call (op.eval env) (CV.ofOperand cenv op) := by
  cases op with
  | value id => exact h id
  | const word =>
    simp only [Operand.eval, CV.ofOperand, CV.Rel, SV.Rel, WExpr.eval]
    exact (Nat.mod_eq_of_lt word.isLt).symm

theorem crel_args {ρ : Val} {call : Call} {env : Env} {cenv : CEnv} (h : CEnvRel ρ call env cenv) :
    ∀ ops : List Operand, CArgsRel ρ call (ops.map (Operand.eval env)) (ops.map (CV.ofOperand cenv))
  | [] => trivial
  | op :: ops => ⟨crel_operand h op, crel_args h ops⟩

theorem cvSVs_sound {ρ : Val} {call : Call} : ∀ {ws : List Word} {cs : List CV} {ss : List SV},
    cvSVs cs = some ss → CArgsRel ρ call ws cs → ArgsRel ρ call ws ss
  | [], [], ss, h, _ => by
    simp only [cvSVs, Option.some.injEq] at h
    subst h
    trivial
  | w :: ws, c :: cs, ss, h, ⟨hw, hr⟩ => by
    simp only [cvSVs] at h
    split at h
    · rename_i a r ha hr'
      simp only [Option.some.injEq] at h
      subst h
      cases c with
      | v x =>
        simp only [CV.sv, Option.some.injEq] at ha
        subst ha
        exact ⟨hw, cvSVs_sound hr' hr⟩
      | gas => simp [CV.sv] at ha
    · simp at h
  | [], _ :: _, _, _, hr => by simp [CArgsRel] at hr
  | _ :: _, [], _, _, hr => by simp [CArgsRel] at hr

theorem CEnvRel.zero (ρ : Val) (call : Call) :
    CEnvRel ρ call (fun _ => 0) (fun _ => .v (.w (.lit 0))) :=
  fun _ => by simp [CV.Rel, SV.Rel, WExpr.eval]

theorem copt_of_opt {ρ : Val} {call : Call} {r : Option Word} {s : Option SV}
    (h : OptRel ρ call r s) : COptRel ρ call r (s.map CV.v) := by
  cases r <;> cases s <;> simp_all [OptRel, COptRel, CV.Rel]

/-! ## The frame of the world -/

/-! ## The frame of the world -/

theorem machineCalls_append : ∀ (a b : List Event), machineCalls (a ++ b) = machineCalls a ++ machineCalls b
  | [], b => rfl
  | e :: a, b => by
    cases e <;> simp only [List.cons_append, machineCalls, machineCalls_append a b, List.cons_append]

/-- The effects of the call-free run, which add no call to the world and keep the transient
storage. -/
def plainEff : Effect → Bool
  | .mload | .mstore | .sload | .sstore => true
  | .calldataload | .calldatasize | .callvalue | .caller | .returndatasize => true
  | .log _ | .keccak256 | .returndatacopy => true
  | _ => false

theorem plain_log {o : Oracle} {call : Call} {k : Nat}
    {args : List Word} {s s' : State} {r : Option Word} (h : (Effect.log k).apply o call args s = some (r, s')) :
    (∃ evs, s'.world = s.world ++ evs ∧ machineCalls evs = []) ∧ s'.transient = s.transient := by
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
    simp only [Effect.apply, reduceCtorEq] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[_], rfl, rfl⟩, rfl⟩
  · simp at h

theorem plain_apply {o : Oracle} {call : Call} {eff : Effect} (he : plainEff eff = true)
    {args : List Word} {s s' : State} {r : Option Word} (h : eff.apply o call args s = some (r, s')) :
    (∃ evs, s'.world = s.world ++ evs ∧ machineCalls evs = []) ∧ s'.transient = s.transient := by
  cases eff
  case log k => exact plain_log h
  all_goals simp only [plainEff, Bool.false_eq_true] at he
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp only [Effect.apply, reduceCtorEq] at h <;>
    (try split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨⟨[], by simp, rfl⟩, rfl⟩

theorem symEffect_plain {ev : EnvFlags} {cv : SV} {n : Nat} {eff : Effect} {sargs : List SV}
    {st : SState} {x : Option SV × SState} (h : symEffect ev cv n eff sargs st = some x) :
    plainEff eff = true := by
  unfold symEffect at h
  split at h <;> first | rfl | simp at h

/-! ## The phases -/

/-- What a machine state holds before the external call: the symbolic state, no call in its
world, and the transient storage the call started with. -/
structure PreRel (ρ : Val) (s : State) (st : SState) : Prop where
  st : StRel ρ s st
  calls : machineCalls s.world = []
  transient : s.transient = fun _ => 0

/-- The answer the oracle gives the external call whose world is `w0`: the valuation reads it after
the `n` argument words; its size and bytes, in that world and in that world followed by events with
no call; and its success flag. -/
structure AnsAt (o : Oracle) (n : Nat) (ρ : Val) (w0 : List Event) (a : CAns) : Prop where
  val : ρ.withAns n a = ρ
  len : a.data.length < wordSize
  flag : (callFlag o w0).toNat = if a.ok then 1 else 0
  size : ∀ rest, machineCalls rest = [] → (returndataSize o (w0 ++ rest)).toNat = a.data.length
  byte : ∀ rest, machineCalls rest = [] → ∀ j < a.data.length,
    (returndataByte o (w0 ++ rest) j).toNat = a.data.getD j 0

/-- What a machine state holds after the external call: the oracle's answer, its world the call's
followed by events with no call, and the symbolic state; once the return data was copied to `d`,
only its bytes there. -/
def PostRel (ρ : Val) (o : Oracle) (n : Nat) (w0 : List Event) (a : CAns) (s : State) (st : SState) :
    Option Nat → Prop
  | none => AnsAt o n ρ w0 a ∧ StRel ρ s st ∧ ∃ rest, s.world = w0 ++ rest ∧ machineCalls rest = []
  | some d => AnsAt o n ρ w0 a ∧ (∃ rest, s.world = w0 ++ rest ∧ machineCalls rest = []) ∧
      ∀ j < a.data.length, (s.memory.bytes (d + j)).toNat = a.data.getD j 0

def PhRel (ρ : Val) (o : Oracle) (n : Nat) (w0 : List Event) (a : CAns) (s : State) (st : SState) :
    Phase → Prop
  | .pre => PreRel ρ s st
  | .post rdc => PostRel ρ o n w0 a s st rdc

theorem PostRel.ans {ρ : Val} {o : Oracle} {n : Nat} {w0 : List Event} {a : CAns} {s : State}
    {st : SState} : ∀ {rdc : Option Nat}, PostRel ρ o n w0 a s st rdc → AnsAt o n ρ w0 a
  | none, h => h.1
  | some _, h => h.1

theorem PostRel.world {ρ : Val} {o : Oracle} {n : Nat} {w0 : List Event} {a : CAns} {s : State}
    {st : SState} : ∀ {rdc : Option Nat}, PostRel ρ o n w0 a s st rdc →
      ∃ rest, s.world = w0 ++ rest ∧ machineCalls rest = []
  | none, h => h.2.2
  | some _, h => h.2.1

theorem AnsAt.arg_size {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) : (WExpr.arg n).eval ρ = a.data.length := by
  have e := withAns_size ρ n a
  rw [h.val] at e
  simp only [WExpr.eval, e, Nat.mod_eq_of_lt h.len]

/-! ## Effects -/

theorem symEffectPre_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ)
    {eff : Effect} {args : List Word} {cargs : List CV} {s : State} {st st' : SState}
    {res : Option CV} (h : symEffectPre ev cv n eff cargs st = some (res, st'))
    (hr : CArgsRel ρ call args cargs) (hs : PreRel ρ s st) :
    ∃ res' s', eff.apply o call args s = some (res', s') ∧ COptRel ρ call res' res ∧ PreRel ρ s' st' := by
  unfold symEffectPre at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [], _ =>
      refine ⟨_, _, rfl, trivial, ?_⟩
      refine ⟨⟨hs.st.mem, hs.st.store, ?_⟩, ?_, hs.transient⟩
      · simp only [logs, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]
        exact hs.st.world
      · simp only [machineCalls_append, hs.calls]
        rfl
  all_goals try simp at h
  split at h
  · rename_i sargs hsargs
    split at h
    · rename_i r0 st0 hsym
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨res', s', h1, h2, h3⟩ := symEffect_sound hc henv hsym (cvSVs_sound hsargs hr) hs.st
      obtain ⟨⟨evs, hw, hcalls⟩, htr⟩ := plain_apply (symEffect_plain hsym) h1
      refine ⟨res', s', h1, copt_of_opt h2, h3, ?_, by rw [htr, hs.transient]⟩
      rw [hw, machineCalls_append, hs.calls, hcalls]
      rfl
    · simp at h
  · simp at h

theorem bytes_write' (m : Mem) (off size : Nat) (src : Nat → Memory.Byte) (i : Nat) :
    (m.write off size src).bytes i = if off ≤ i ∧ i < off + size then src (i - off) else m.bytes i := by
  unfold Mem.write Mem.expand
  split <;> rfl

theorem symEffectPost_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) {w0 : List Event} {a : CAns}
    {eff : Effect} {args : List Word} {cargs : List CV} {s : State} {st st' : SState}
    {rdc rdc' : Option Nat} {res : Option CV} (h : symEffectPost ev cv n eff cargs st rdc = some (res, st', rdc'))
    (hr : CArgsRel ρ call args cargs) (hs : PostRel ρ o n w0 a s st rdc) :
    ∃ res' s', eff.apply o call args s = some (res', s') ∧ COptRel ρ call res' res ∧
      PostRel ρ o n w0 a s' st' rdc' := by
  have hA := hs.ans
  unfold symEffectPost at h
  split at h
  · -- returndatasize
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    match args, hr with
    | [], _ =>
      refine ⟨_, _, rfl, ?_, hs⟩
      obtain ⟨rest, hw, hcalls⟩ := hs.world
      simp only [COptRel, CV.Rel, SV.Rel, hA.arg_size]
      rw [hw]
      exact hA.size rest hcalls
  · simp at h
  · -- returndatacopy
    rename_i d i
    split at h
    · rename_i hi
      obtain ⟨rfl, rfl⟩ := hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      match args, hr with
      | [dw, ow, sw], ⟨hd, ho, hsz, _⟩ =>
        simp only [CV.Rel, SV.Rel] at hd ho hsz
        rw [hA.arg_size] at hsz
        simp only [WExpr.eval, Nat.zero_mod] at hd ho
        obtain ⟨rest, hw, hcalls⟩ := hs.world
        have hsize : (returndataSize o s.world).toNat = a.data.length := by rw [hw]; exact hA.size rest hcalls
        refine ⟨none, { s with memory := s.memory.write dw.toNat sw.toNat (fun j => returndataByte o s.world (ow.toNat + j)) },
          ?_, trivial, hA, ⟨rest, hw, hcalls⟩, ?_⟩
        · simp only [Effect.apply, hsize, ho, hsz, Nat.zero_add, Nat.lt_irrefl, ↓reduceIte]
        · intro j hj
          simp only [bytes_write', hd, ho, hsz, Nat.zero_add]
          have hd' : d % wordSize ≤ d % wordSize + j ∧ d % wordSize + j < d % wordSize + a.data.length := by omega
          simp only [hd', and_self, ↓reduceIte, Nat.add_sub_cancel_left]
          rw [hw]
          exact hA.byte rest hcalls j hj
    · simp at h
  · simp at h
  · simp at h
  · simp at h
  · -- the call-free run's effects
    split at h
    · simp at h
    · split at h
      · rename_i sargs hsargs
        split at h
        · rename_i r0 st0 hsym
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨-, hst, rest, hw, hcalls⟩ := hs
          obtain ⟨res', s', h1, h2, h3⟩ := symEffect_sound hc henv hsym (cvSVs_sound hsargs hr) hst
          obtain ⟨⟨evs, hw', hcalls'⟩, -⟩ := plain_apply (symEffect_plain hsym) h1
          refine ⟨res', s', h1, copt_of_opt h2, hA, h3, rest ++ evs, ?_, ?_⟩
          · rw [hw', hw, List.append_assoc]
          · rw [machineCalls_append, hcalls, hcalls']; rfl
        · simp at h
      · simp at h


/-! ## Instructions -/

theorem symEffectC_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) {w0 : List Event} {a : CAns}
    {eff : Effect} {args : List Word} {cargs : List CV} {s : State} {st st' : SState}
    {ph ph' : Phase} {res : Option CV} (h : symEffectC ev cv n eff cargs st ph = some (res, st', ph'))
    (hr : CArgsRel ρ call args cargs) (hs : PhRel ρ o n w0 a s st ph) :
    ∃ res' s', eff.apply o call args s = some (res', s') ∧ COptRel ρ call res' res ∧
      PhRel ρ o n w0 a s' st' ph' := by
  cases ph with
  | pre =>
    simp only [symEffectC] at h
    split at h
    · rename_i r0 st0 h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact symEffectPre_sound hc henv h0 hr hs
    · simp at h
  | post rdc =>
    simp only [symEffectC] at h
    split at h
    · rename_i r0 st0 rdc0 h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact symEffectPost_sound hc henv h0 hr hs
    · simp at h

theorem symInstsC_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) {K : Facts}
    (hK : K.Hold ρ) {w0 : List Event} {a : CAns} : ∀ (insts : List Inst) (cenv cenv' : CEnv)
      (st st' : SState) (ph ph' : Phase),
      symInstsC ev cv sel n K insts cenv st ph = some (cenv', st', ph') → ∀ env s,
      CEnvRel ρ call env cenv → PhRel ρ o n w0 a s st ph → ∃ env' s',
        execInsts o call insts env s = some (env', s') ∧ CEnvRel ρ call env' cenv' ∧
          PhRel ρ o n w0 a s' st' ph'
  | [], cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨env, s, rfl, he, hs⟩
  | .pure dst op args :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    split at h
    · rename_i sargs hsargs
      split at h
      · rename_i v hv
        obtain ⟨w, hw, hwv⟩ := symPure_sound hc hv (cvSVs_sound hsargs (crel_args he args))
        obtain ⟨env', s', h1, h2, h3⟩ := symInstsC_sound hc henv hK rest _ _ _ _ _ _ h _ s
          (he.set (s := .v v) hwv dst) hs
        exact ⟨env', s', by simp only [execInsts, hw]; exact h1, h2, h3⟩
      · simp at h
    · simp at h
  | .effect dst eff args :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    split at h
    · rename_i res st1 ph1 hv
      obtain ⟨res', s1, h1, hr1, hs1⟩ := symEffectC_sound hc henv hv (crel_args he args) hs
      have key : ∀ (env1 : Env) (cenv1 : CEnv), CEnvRel ρ call env1 cenv1 →
          symInstsC ev cv sel n K rest cenv1 st1 ph1 = some (cenv', st', ph') → ∃ env' s',
            execInsts o call rest env1 s1 = some (env', s') ∧ CEnvRel ρ call env' cenv' ∧
              PhRel ρ o n w0 a s' st' ph' :=
        fun env1 cenv1 he1 h' => symInstsC_sound hc henv hK rest _ _ _ _ _ _ h' _ s1 he1 hs1
      simp only [execInsts, h1]
      cases dst <;> cases res' <;> cases res <;> simp only [COptRel] at hr1 <;> dsimp only at h ⊢
      all_goals first
        | exact key _ _ he h
        | exact key _ _ (he.set hr1 _) h
    · simp at h
  | .ne dst a' b :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    have ha := crel_operand he a'
    have hb := crel_operand he b
    obtain ⟨sv, hv, h⟩ : ∃ sv, CV.Rel ρ call (Evm.ne (a'.eval env) (b.eval env)) sv ∧
        symInstsC ev cv sel n K rest (cenv.set dst sv) st ph = some (cenv', st', ph') := by
      split at h
      · rename_i x y hx hy
        rw [hx] at ha
        rw [hy] at hb
        refine ⟨_, ?_, h⟩
        simp only [CV.Rel, SV.Rel] at ha hb ⊢
        rw [eval_mkUn, ne_toNat]
        simp only [WExpr.eval, eval_mkBin, ha, hb]
      · rename_i z hx hy
        split at h
        · rename_i hz
          rw [hx] at ha
          rw [hy] at hb
          refine ⟨_, ?_, h⟩
          simp only [CV.Rel] at ha hb ⊢
          simp only [SV.Rel, WExpr.eval, hz] at hb ⊢
          rw [ne_toNat, hb]
          simp [BinOp.eval, UnOp.eval, rel_paid ha]
        · simp at h
      · rename_i z hx hy
        split at h
        · rename_i hz
          rw [hx] at ha
          rw [hy] at hb
          refine ⟨_, ?_, h⟩
          simp only [CV.Rel] at ha hb ⊢
          simp only [SV.Rel, WExpr.eval, hz] at ha ⊢
          rw [ne_toNat, ha]
          simp [BinOp.eval, UnOp.eval, Ne.symm (rel_paid hb)]
        · simp at h
      · simp at h
    obtain ⟨env', s', h1, h2, h3⟩ :=
      symInstsC_sound hc henv hK rest _ _ _ _ _ _ h _ s (he.set hv dst) hs
    exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
  | .assume negated op args :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    split at h
    · rename_i sargs hsargs
      split at h
      · rename_i e hv
        split at h
        · rename_i v hl
          obtain ⟨w, hw, hwv⟩ := symPure_sound hc hv (cvSVs_sound hsargs (crel_args he args))
          have hwn : w.toNat = v % wordSize := by
            have hse := WExpr.eval_simp hK e
            rw [WExpr.decided_sound hK hl] at hse
            simp only [SV.Rel] at hwv
            rw [hwv, ← hse]
          have hz : (w = 0) ↔ (v % wordSize = 0) := by
            constructor
            · intro h0; rw [← hwn, h0]; rfl
            · intro h0; exact BitVec.eq_of_toNat_eq (by rw [hwn, h0]; rfl)
          simp only [execInsts, hw]
          by_cases h0 : v % wordSize = 0
          · have hw0 := hz.mpr h0
            simp only [h0, ite_true] at h
            simp only [hw0, ite_true]
            cases negated <;> simp only [Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h ⊢
            exact symInstsC_sound hc henv hK rest _ _ _ _ _ _ h env s he hs
          · have hw0 : ¬ w = 0 := fun h' => h0 (hz.mp h')
            simp only [h0, ite_false] at h
            simp only [hw0, ite_false]
            cases negated <;> simp only [Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h ⊢
            exact symInstsC_sound hc henv hK rest _ _ _ _ _ _ h env s he hs
        · simp at h
      · simp at h
    · simp at h
  | .word dst a' :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    split at h
    · rename_i e hx
      have ha := crel_operand he a'
      rw [hx] at ha
      obtain ⟨env', s', h1, h2, h3⟩ :=
        symInstsC_sound hc henv hK rest _ _ _ _ _ _ h _ s (he.set ha dst) hs
      exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
    · simp at h
  | .heapFloor dst floor :: rest, cenv, cenv', st, st', ph, ph', h, env, s, he, hs => by
    simp only [symInstsC] at h
    have hv : CV.Rel ρ call floor (.v (.w (.lit floor.toNat))) := by
      simp only [CV.Rel, SV.Rel, WExpr.eval, Nat.mod_eq_of_lt floor.isLt]
    obtain ⟨env', s', h1, h2, h3⟩ :=
      symInstsC_sound hc henv hK rest _ _ _ _ _ _ h _ s (he.set hv dst) hs
    exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
  | .low .. :: _, _, _, _, _, _, _, h, _, _, _, _ => by simp [symInstsC] at h
  | .select .. :: _, _, _, _, _, _, _, h, _, _, _, _ => by simp [symInstsC] at h
  | .call .. :: _, _, _, _, _, _, _, h, _, _, _, _ => by simp [symInstsC] at h
  | .alloc .. :: _, _, _, _, _, _, _, h, _, _, _, _ => by simp [symInstsC] at h

theorem symPhisC_sound {ρ : Val} {call : Call} {envI : Env} {cenvI : CEnv}
    (hI : CEnvRel ρ call envI cenvI) (pred : Nat) :
    ∀ (phis : List (Nat × List (Nat × Operand))) (cenv cenv' : CEnv) (env : Env),
      symPhisC cenvI pred phis cenv = some cenv' → CEnvRel ρ call env cenv →
      ∃ env', bindPhis envI pred phis env = some env' ∧ CEnvRel ρ call env' cenv'
  | [], cenv, cenv', env, h, he => by
    simp only [symPhisC, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | (dst, arms) :: rest, cenv, cenv', env, h, he => by
    simp only [symPhisC] at h
    split at h
    · rename_i x op hf
      obtain ⟨env', h1, h2⟩ := symPhisC_sound hI pred rest _ _ _ h (he.set (crel_operand hI op) dst)
      exact ⟨env', by simp only [bindPhis, hf]; exact h1, h2⟩
    · simp at h

theorem symSwitchC_sound {ρ : Val} {call : Call} {env : Env} {cenv : CEnv}
    (he : CEnvRel ρ call env cenv) {key : Word} {kv : Nat} (hk : key.toNat = kv % wordSize)
    (d : Nat) : ∀ (cs : List (Operand × Nat)) (t : Nat), symSwitchC cenv kv d cs = some t →
      switchTarget env key d cs = t
  | [], t, h => by simp only [symSwitchC, Option.some.injEq] at h; subst h; rfl
  | (c, t') :: rest, t, h => by
    simp only [symSwitchC] at h
    split at h
    · rename_i v hv
      have hc := crel_operand he c
      rw [hv] at hc
      have hcn : (c.eval env).toNat = v % wordSize := hc
      simp only [switchTarget]
      by_cases heq : v % wordSize = kv % wordSize
      · simp only [heq, ite_true, Option.some.injEq] at h
        subst h
        have : c.eval env = key := BitVec.eq_of_toNat_eq (by rw [hcn, hk, heq])
        simp [this]
      · simp only [heq, ite_false] at h
        have : ¬ c.eval env = key := fun h' => heq (by rw [← hcn, ← hk, h'])
        simp only [this, ite_false]
        exact symSwitchC_sound he hk d rest t h
    · simp at h

theorem symBindParamsC_sound {ρ : Val} {call : Call} :
    ∀ (ps : List Nat) (args : List Word) (cargs : List CV) (env : Env) (cenv cenv' : CEnv),
      symBindParamsC ps cargs cenv = some cenv' → CArgsRel ρ call args cargs →
      CEnvRel ρ call env cenv → ∃ env', bindParams ps args env = some env' ∧ CEnvRel ρ call env' cenv'
  | [], [], [], env, cenv, cenv', h, _, he => by
    simp only [symBindParamsC, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | p :: ps, a :: as, s :: ss, env, cenv, cenv', h, ⟨ha, hr⟩, he => by
    simp only [symBindParamsC] at h
    obtain ⟨env', h1, h2⟩ := symBindParamsC_sound ps as ss _ _ _ h hr (he.set ha p)
    exact ⟨env', by simp only [bindParams]; exact h1, h2⟩
  | [], [], _ :: _, _, _, _, h, _, _ => by simp [symBindParamsC] at h
  | [], _ :: _, _, _, _, _, _, hr, _ => by cases ‹List CV› <;> simp_all [CArgsRel, symBindParamsC]
  | _ :: _, [], _, _, _, _, h, hr, _ => by cases ‹List CV› <;> simp_all [CArgsRel, symBindParamsC]
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [symBindParamsC] at h

theorem symBindResultC_sound {ρ : Val} {call : Call} {env : Env} {cenv : CEnv}
    (he : CEnvRel ρ call env cenv) : ∀ (dst : Option Nat) (args : List Word) (cargs : List CV)
      (cenv' : CEnv), symBindResultC cenv dst cargs = some cenv' → CArgsRel ρ call args cargs →
      ∃ env', bindResult env dst args = some env' ∧ CEnvRel ρ call env' cenv'
  | none, [], [], cenv', h, _ => by
    simp only [symBindResultC, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | some d, [a], [v], cenv', h, hr => by
    simp only [symBindResultC, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, he.set hr.1 d⟩
  | none, _ :: _, _, _, h, hr => by
    cases ‹List CV› <;> simp_all [CArgsRel, symBindResultC]
  | none, [], _ :: _, _, h, hr => by simp [CArgsRel] at hr
  | some _, [], _, _, h, hr => by cases ‹List CV› <;> simp_all [CArgsRel, symBindResultC]
  | some _, _ :: _ :: _, cargs, _, h, hr => by
    match cargs, hr with
    | _ :: _ :: _, _ => simp [symBindResultC] at h
  | some _, [_], [], _, h, hr => by simp [CArgsRel] at hr
  | some _, [_], _ :: _ :: _, _, h, hr => by simp [CArgsRel] at hr


/-! ## Segments with the external call -/

theorem splitCall_append (pre post : List Inst) (hpre : ∀ i ∈ pre, instIsCall i = false) :
    splitCall (pre ++ post) = (pre ++ (splitCall post).1, (splitCall post).2) := by
  induction pre with
  | nil => rfl
  | cons i pre ih =>
    have hi := hpre i List.mem_cons_self
    have ih' := ih (fun j hj => hpre j (List.mem_cons_of_mem _ hj))
    cases i <;> simp only [instIsCall, reduceCtorEq, Bool.true_eq_false] at hi <;>
      simp only [List.cons_append, splitCall, ih']

theorem execInsts_append (o : Oracle) (call : Call) : ∀ (l1 l2 : List Inst) (env : Env) (s : State),
    execInsts o call (l1 ++ l2) env s =
      match execInsts o call l1 env s with
      | some (e, s') => execInsts o call l2 e s'
      | none => none
  | [], l2, env, s => rfl
  | i :: l1, l2, env, s => by
    cases i with
    | pure dst op args =>
      simp only [List.cons_append, execInsts]
      split <;> simp only [execInsts_append o call l1 l2]
    | effect dst eff args =>
      simp only [List.cons_append, execInsts]
      split <;> simp only [execInsts_append o call l1 l2]
    | ne dst a b => simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]
    | assume negated op args =>
      simp only [List.cons_append, execInsts]
      split
      · split
        · split <;> simp only [execInsts_append o call l1 l2]
        · split <;> simp only [execInsts_append o call l1 l2]
      · rfl
    | word dst a => simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]
    | call => rfl
    | low dst bits a => simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]
    | select dst c y n => simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]
    | heapFloor dst floor => simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]
    | alloc dst p =>
      cases p <;> simp only [List.cons_append, execInsts, execInsts_append o call l1 l2]

theorem isExtCall_spec {i : Inst} {dst : Option Nat} {args : List Operand}
    (h : isExtCall i = some (dst, args)) : i = .effect dst (.call .staticcall) args := by
  unfold isExtCall at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp at h

theorem splitExt_spec : ∀ {insts pre : List Inst} {dst : Option Nat} {args : List Operand} {post : List Inst},
    splitExt insts = some (pre, dst, args, post) →
      insts = pre ++ .effect dst (.call .staticcall) args :: post ∧ ∀ i ∈ pre, instIsCall i = false
  | [], _, _, _, _, h => by simp [splitExt] at h
  | i :: rest, pre, dst, args, post, h => by
    simp only [splitExt] at h
    cases hx : isExtCall i with
    | some p =>
      obtain ⟨d, as⟩ := p
      simp only [hx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨by rw [isExtCall_spec hx]; rfl, by simp⟩
    | none =>
      simp only [hx] at h
      split at h
      · simp at h
      · rename_i hic
        cases hr : splitExt rest with
        | none => simp [hr] at h
        | some q =>
          obtain ⟨pre', d', as', post'⟩ := q
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨e, hp⟩ := splitExt_spec hr
          refine ⟨by rw [e]; rfl, ?_⟩
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · simpa using hic
          · exact hp j hj

/-- The values after an effect: its result bound to its destination, if both are there. -/
def bindDst (env : Env) : Option Nat → Option Word → Env
  | some d, some v => env.set d v
  | _, _ => env

theorem execInsts_effect (o : Oracle) (call : Call) (dst : Option Nat) (eff : Effect) (args : List Operand)
    (l : List Inst) (env : Env) (s s' : State) (res : Option Word)
    (h : eff.apply o call (args.map (Operand.eval env)) s = some (res, s')) :
    execInsts o call (.effect dst eff args :: l) env s = execInsts o call l (bindDst env dst res) s' := by
  simp only [execInsts, h]
  cases dst <;> cases res <;> rfl

/-- **The segment through the external call**: a block's instructions that reach the call first
run as the instructions after it, from the frame after the call. -/
theorem segment_ext (o : Oracle) (call : Call) (m : Module) (ms : List Return) (fn b : Nat)
    {insts pre post : List Inst} {dst : Option Nat} {args : List Operand}
    (h : splitExt insts = some (pre, dst, args, post)) (term : Terminator) {env env1 : Env} {s s1 s2 : State}
    {res : Option Word} (hpre : execInsts o call pre env s = some (env1, s1))
    (hcall : (Effect.call .staticcall).apply o call (args.map (Operand.eval env1)) s1 = some (res, s2)) :
    segment o call m ms fn b insts term env s =
      segment o call m ms fn b post term (bindDst env1 dst res) s2 := by
  obtain ⟨rfl, hp⟩ := splitExt_spec h
  have hp' : ∀ i ∈ pre ++ [Inst.effect dst (.call .staticcall) args], instIsCall i = false := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hp i hi
    · simp only [List.mem_singleton] at hi; subst hi; rfl
  have hsplit := splitCall_append (pre ++ [Inst.effect dst (.call .staticcall) args]) post hp'
  simp only [List.append_assoc, List.singleton_append] at hsplit
  have hex : ∀ l, execInsts o call (pre ++ Inst.effect dst (.call .staticcall) args :: l) env s =
      execInsts o call l (bindDst env1 dst res) s2 := by
    intro l
    rw [execInsts_append, hpre]
    exact execInsts_effect o call dst _ args l env1 s1 s2 res hcall
  unfold segment
  rw [hsplit]
  cases hsc : splitCall post with
  | mk before next =>
    cases next with
    | some c =>
      obtain ⟨dst', callee, args', extras, publish, rest⟩ := c
      simp only [hex]
    | none =>
      simp only [hex]


/-! ## Steps -/

/-- The state an external call leaves, from the state ¤s¤ before it, with its memory after the
operand ranges' expansion, its output range and its world. -/
abbrev callWorld (s : State) (seen : List Word) (input : List Memory.Byte) : List Event :=
  s.world ++ [.call .staticcall seen input s.storage s.transient]

/-- What a machine step gives, held by what a symbolic step gives: the same end, or a bubbled
failure, or the next frame related, or for a branch on a word the side the call's words take, or
the external call: then the machine's step is the step from the frame after the call. -/
def CNextOk (ρ : Val) (call : Call) (o : Oracle) (m : Module) (n : Nat) (w0 : List Event) (a : CAns)
    (x : Option ((Halt × State) ⊕ Frame)) : CNext → Prop
  | .done T => ∃ r, x = some (.inl r) ∧ observe call r.2 r.1 = (T.eval ρ).obs
  | .bubble => ∃ r, x = some (.inl r) ∧ observe call r.2 r.1 = (bubbleRes ρ a).obs
  | .go stack pos cenv st ph => ∃ ms env s, x = some (.inr (ms, pos, env, s)) ∧
      CStackRel ρ call ms stack ∧ CEnvRel ρ call env cenv ∧ PhRel ρ o n w0 a s st ph
  | .fork e stack fn b yes no cenv st ph => ∃ ms env s,
      x = some (.inr (ms, .enter fn b (if e.eval ρ = 0 then no else yes), env, s)) ∧
      CStackRel ρ call ms stack ∧ CEnvRel ρ call env cenv ∧ PhRel ρ o n w0 a s st ph
  | .callAt r stack dst pos cenv st oo os => ∃ (ms : List Return) (env : Env) (s : State) (seen : List Word)
      (input : List Memory.Byte) (mem : Mem) (ooW osW : Word),
      x = moduleBlock o call m (ms, pos, bindDst env dst (some (callFlag o (callWorld s seen input))),
        called o .staticcall s mem ooW osW (callWorld s seen input)) ∧
      CStackRel ρ call ms stack ∧ CEnvRel ρ call env cenv ∧ PreRel ρ s st ∧
      mem.bytes = s.memory.bytes ∧ ooW.toNat = oo ∧ osW.toNat = os ∧
      (seen.getD 1 0).toNat = r.target.eval ρ ∧ input.map BitVec.toNat = r.input.map (OByte.eval ρ) ∧
      r.static = true ∧ r.value = .lit 0

theorem PhRel.readOk {ρ : Val} {o : Oracle} {n : Nat} {w0 : List Event} {a : CAns} {s : State}
    {st : SState} : ∀ {ph : Phase}, Generic.readOk ph = true → PhRel ρ o n w0 a s st ph → StRel ρ s st
  | .pre, _, h => h.st
  | .post none, _, h => h.2.1
  | .post (some _), hr, _ => by simp [Generic.readOk] at hr

theorem start_world (g : Function) (s : State) : (g.start s).world = s.world := by
  unfold Function.start; split <;> rfl

theorem start_transient (g : Function) (s : State) : (g.start s).transient = s.transient := by
  unfold Function.start; split <;> rfl

theorem PhRel.start {ρ : Val} {o : Oracle} {n : Nat} {w0 : List Event} {a : CAns} {s : State}
    {st : SState} : ∀ {ph : Phase}, Generic.readOk ph = true → PhRel ρ o n w0 a s st ph → ∀ g : Function,
      PhRel ρ o n w0 a (g.start s) (symStart g st) ph
  | .pre, _, h, g => ⟨h.st.start g, by rw [start_world]; exact h.calls, by rw [start_transient]; exact h.transient⟩
  | .post none, _, h, g => ⟨h.1, h.2.1.start g, by rw [start_world]; exact h.2.2⟩
  | .post (some _), hr, _, _ => by simp [Generic.readOk] at hr

theorem symTermC_sound {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (m : Module) {K : Facts} (hK : K.Hold ρ)
    {w0 : List Event} {a : CAns} {stack : List CReturn}
    {fn b : Nat} {cenv : CEnv} {st : SState} {ph : Phase} {term : Terminator} {r : CNext}
    (h : symTermC m n K stack fn b cenv st ph term = some r) {ms : List Return} {env : Env} {s : State}
    (hst : CStackRel ρ call ms stack) (he : CEnvRel ρ call env cenv) (hs : PhRel ρ o n w0 a s st ph) :
    CNextOk ρ call o m n w0 a (segment o call m ms fn b [] term env s) r := by
  cases term with
  | jump t =>
    simp only [symTermC, Option.some.injEq] at h
    subst h
    exact ⟨ms, env, s, rfl, hst, he, hs⟩
  | branch c yes no =>
    simp only [symTermC] at h
    have hcr := crel_operand he c
    have hseg : segment o call m ms fn b [] (.branch c yes no) env s =
        some (.inr (ms, .enter fn b (if c.eval env = 0 then no else yes), env, s)) := rfl
    rw [hseg]
    split at h
    · rename_i e hsv
      rw [hsv] at hcr
      have hz := rel_zero_iff (show SV.Rel ρ call _ (.w e) from hcr)
      split at h
      · rename_i v hl
        simp only [Option.some.injEq] at h
        subst h
        have hev : e.eval ρ = v % wordSize := by rw [WExpr.eq_of_lit? hl]; rfl
        exact ⟨ms, env, s, by simp only [hz, hev], hst, he, hs⟩
      · split at h
        · rename_i sd hl
          simp only [Option.some.injEq] at h
          subst h
          have hf := Facts.lookup_sound hK hl
          refine ⟨ms, env, s, ?_, hst, he, hs⟩
          cases sd with
          | true =>
            have : ¬ e.eval ρ = 0 := fun h0 => by simpa using hf.mp h0
            simp only [hz, this, ↓reduceIte]
          | false =>
            have : e.eval ρ = 0 := hf.mpr rfl
            simp only [hz, this, ↓reduceIte, Bool.false_eq_true]
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨ms, env, s, by simp only [hz], hst, he, hs⟩
    · rename_i hsv
      simp only [Option.some.injEq] at h
      subst h
      rw [hsv] at hcr
      have hc0 : ¬ c.eval env = 0 := hcr
      exact ⟨ms, env, s, by simp only [hc0, ↓reduceIte], hst, he, hs⟩
    · simp at h
  | switch key d cs =>
    simp only [symTermC] at h
    split at h
    · rename_i kv hkv
      cases hs' : symSwitchC cenv kv d cs with
      | none => simp [hs'] at h
      | some t =>
        simp only [hs', Option.some.injEq] at h
        subst h
        have hk := crel_operand he key
        rw [hkv] at hk
        have htg := symSwitchC_sound he (show (key.eval env).toNat = kv % wordSize from hk) d cs t hs'
        exact ⟨ms, env, s, by simp [segment, splitCall, execInsts, htg], hst, he, hs⟩
    · simp at h
  | tailCall callee args =>
    simp only [symTermC] at h
    cases hg : symCallee m callee with
    | none => simp [hg] at h
    | some g =>
      simp only [hg] at h
      have hg' := symCallee_some hg
      cases hbp : symBindParamsC g.params (args.map (CV.ofOperand cenv)) (fun _ => .v (.w (.lit 0))) with
      | none => simp [hbp] at h
      | some cenv3 =>
        simp only [hbp] at h
        split at h
        · rename_i hro
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨env3, hbp', he3⟩ :=
            symBindParamsC_sound g.params _ _ _ _ _ hbp (crel_args he args) (CEnvRel.zero ρ call)
          refine ⟨ms, env3, g.start s, by simp only [segment, splitCall, execInsts, hg', hbp'], hst, he3, ?_⟩
          exact PhRel.start hro hs g
        · simp at h
  | leave values =>
    simp only [symTermC] at h
    cases stack with
    | nil => simp at h
    | cons q qs =>
      match ms, hst with
      | r :: rs, ⟨hfn, hb, hdst, hrest, hterm, hextras, hpublish, henvr, hst'⟩ =>
        simp only at h
        cases hbr : symBindResultC q.env q.dst (values.map (CV.ofOperand cenv)) with
        | none => simp [hbr] at h
        | some env' =>
          simp only [hbr, Option.some.injEq] at h
          subst h
          rw [← hdst] at hbr
          obtain ⟨env'', hbr', he''⟩ :=
            symBindResultC_sound henvr r.dst _ _ _ hbr (crel_args he values)
          have hbr2 : bindResults r.env r.dst r.extras (values.map (Operand.eval env)) = some env'' := by
            rw [hextras]; exact hbr'
          exact ⟨rs, env'', s, by
              simp [segment, splitCall, execInsts, hbr2, hfn, hb, hrest, hterm, hpublish,
                publishResults],
            hst', he'', hs⟩
  | ret off size =>
    simp only [symTermC] at h
    split at h
    · rename_i ov sv hov hsv
      split at h
      · rename_i hro
        simp only [Option.some.injEq] at h
        subst h
        have hs0 := hs.readOk hro
        have h1 := crel_operand he off
        have h2 := crel_operand he size
        rw [hov] at h1
        rw [hsv] at h2
        refine ⟨_, rfl, ?_⟩
        simp only [halt, observe, Tree.eval, Res.obs, Bool.false_eq_true, ↓reduceIte,
          toNat_of_rel (show SV.Rel ρ call _ _ from h1), toNat_of_rel (show SV.Rel ρ call _ _ from h2)]
        congr 1
        · exact read_eq hs0 _ (bytes_expand _ _ _) _ _
        · exact hs0.world
        · exact storageOf_eq hc (s := s) hs0
      · simp at h
    · simp at h
  | revert off size =>
    simp only [symTermC] at h
    split at h
    · -- the bubble
      rename_i _ _ d o' i hov hsv
      split at h
      · rename_i hcond
        obtain ⟨hod, rfl⟩ := hcond
        simp only [Option.some.injEq] at h
        subst h
        have hs' : PostRel ρ o _ w0 a s st (some d) := hs
        have hA := hs'.ans
        have h1 := crel_operand he off
        have h2 := crel_operand he size
        rw [hov] at h1
        rw [hsv] at h2
        have h1' : (off.eval env).toNat = d := by
          have := toNat_of_rel (show SV.Rel ρ call _ _ from h1); rw [this, hod]
        have h2' : (size.eval env).toNat = a.data.length := by
          have : (size.eval env).toNat = (WExpr.arg _).eval ρ := h2
          rw [this, hA.arg_size]
        refine ⟨_, rfl, ?_⟩
        simp only [halt, observe, bubbleRes, Res.obs, ↓reduceIte, h1', h2', hc.store]
        congr 1
        simp only [Mem.read, List.map_map, bytes_expand]
        apply List.ext_getElem
        · simp
        · intro j hj1 hj2
          simp only [List.getElem_map, List.getElem_range, Function.comp]
          simp only [List.length_map, List.length_range] at hj1
          rw [hs'.2.2 j hj1]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]
          rfl
      · simp at h
    · rename_i ov sv hov hsv
      split at h
      · rename_i hro
        simp only [Option.some.injEq] at h
        subst h
        have hs0 := hs.readOk hro
        have h1 := crel_operand he off
        have h2 := crel_operand he size
        rw [hov] at h1
        rw [hsv] at h2
        refine ⟨_, rfl, ?_⟩
        simp only [halt, observe, Tree.eval, Res.obs, ↓reduceIte,
          toNat_of_rel (show SV.Rel ρ call _ _ from h1), toNat_of_rel (show SV.Rel ρ call _ _ from h2),
          hc.store, Bool.false_eq_true]
        congr 1
        exact read_eq hs0 _ (bytes_expand _ _ _) _ _
      · simp at h
    · simp at h
  | stop =>
    simp only [symTermC] at h
    split at h
    · rename_i hro
      simp only [Option.some.injEq] at h
      subst h
      have hs0 := hs.readOk hro
      refine ⟨_, rfl, ?_⟩
      simp only [observe, Tree.eval, Res.obs, ite_true, hs0.world, storageOf_eq hc hs0, List.map_nil]
    · simp at h
  | invalid =>
    simp only [symTermC, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [observe, Tree.eval, Res.obs, hc.store, Bool.false_eq_true, ite_false, List.map_nil]


theorem symSegmentPlain_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) (m : Module)
    {K : Facts} (hK : K.Hold ρ) {w0 : List Event} {a : CAns} {stack : List CReturn} {fn b : Nat}
    {insts : List Inst} {term : Terminator} {cenv : CEnv} {st : SState} {ph : Phase} {r : CNext}
    (h : symSegmentPlain ev cv m sel n K stack fn b insts term cenv st ph = some r) {ms : List Return}
    {env : Env} {s : State} (hst : CStackRel ρ call ms stack) (he : CEnvRel ρ call env cenv)
    (hs : PhRel ρ o n w0 a s st ph) :
    CNextOk ρ call o m n w0 a (segment o call m ms fn b insts term env s) r := by
  unfold symSegmentPlain at h
  cases hsp : splitCall insts with
  | mk before next =>
  rw [hsp] at h
  cases next with
  | some c =>
    obtain ⟨dst, callee, args, extras, publish, rest⟩ := c
    cases extras with
    | cons _ _ => simp at h
    | nil =>
    cases publish with
    | some _ => simp at h
    | none =>
    simp only at h
    cases hi : symInstsC ev cv sel n K before cenv st ph with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨cenv2, st2, ph2⟩ := p
      simp only [hi] at h
      obtain ⟨env2, s2, hexec, he2, hs2⟩ := symInstsC_sound hc henv hK before _ _ _ _ _ _ hi env s he hs
      cases hg : symCallee m callee with
      | none => simp [hg] at h
      | some g =>
        simp only [hg] at h
        have hg' := symCallee_some hg
        cases hbp : symBindParamsC g.params (args.map (CV.ofOperand cenv2)) (fun _ => .v (.w (.lit 0))) with
        | none => simp [hbp] at h
        | some inner =>
          simp only [hbp] at h
          split at h
          · rename_i hro
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨env3, hbp', he3⟩ :=
              symBindParamsC_sound g.params _ _ _ _ _ hbp (crel_args he2 args) (CEnvRel.zero ρ call)
            exact ⟨⟨fn, b, dst, rest, term, env2, [], none⟩ :: ms, env3, g.start s2,
              by simp only [segment, hsp, hexec, hg', hbp'],
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, he2, hst⟩, he3, PhRel.start hro hs2 g⟩
          · simp at h
  | none =>
    simp only at h
    cases hi : symInstsC ev cv sel n K before cenv st ph with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨cenv2, st2, ph2⟩ := p
      simp only [hi] at h
      obtain ⟨env2, s2, hexec, he2, hs2⟩ := symInstsC_sound hc henv hK before _ _ _ _ _ _ hi env s he hs
      have hseg : segment o call m ms fn b insts term env s = segment o call m ms fn b [] term env2 s2 := by
        simp only [segment, hsp, hexec, splitCall, execInsts]
      rw [hseg]
      exact symTermC_sound hc o m hK h hst he2 hs2

theorem symSegmentC_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) (m : Module)
    {K : Facts} (hK : K.Hold ρ) {w0 : List Event} {a : CAns} {stack : List CReturn} {fn b : Nat}
    {insts : List Inst} {term : Terminator} {cenv : CEnv} {st : SState} {ph : Phase} {r : CNext}
    (h : symSegmentC ev cv m sel n K stack fn b insts term cenv st ph = some r) {ms : List Return}
    {env : Env} {s : State} (hst : CStackRel ρ call ms stack) (he : CEnvRel ρ call env cenv)
    (hs : PhRel ρ o n w0 a s st ph) :
    CNextOk ρ call o m n w0 a (segment o call m ms fn b insts term env s) r := by
  unfold symSegmentC at h
  split at h
  · -- the external call
    rename_i pre dst args post hext
    cases hi : symInstsC ev cv sel n K pre cenv st .pre with
    | none => simp [hi] at h
    | some q =>
      obtain ⟨cenv1, st1, ph1⟩ := q
      cases ph1 with
      | post _ => simp [hi] at h
      | pre =>
      simp only [hi] at h
      obtain ⟨env1, s1, hexec, he1, hs1⟩ := symInstsC_sound hc henv hK pre _ _ _ _ _ _ hi env s he hs
      have hargs := crel_args he1 args
      split at h
      · rename_i g e io is oo os hpat
        simp only [Option.some.injEq] at h
        subst h
        rw [hpat] at hargs
        match hm : args.map (Operand.eval env1), hargs with
        | [gw, aw, iow, isw, oow, osw], ⟨_, ha, hio, his, hoo, hos, _⟩ =>
          simp only [CV.Rel, SV.Rel, WExpr.eval] at ha hio his hoo hos
          have hcall : (Effect.call .staticcall).apply o call (args.map (Operand.eval env1)) s1 =
              some (some (callFlag o (callWorld s1 [gw, aw]
                  (((s1.memory.expand iow.toNat isw.toNat).expand oow.toNat osw.toNat).read iow.toNat isw.toNat))),
                called o .staticcall s1 ((s1.memory.expand iow.toNat isw.toNat).expand oow.toNat osw.toNat) oow osw
                  (callWorld s1 [gw, aw]
                    (((s1.memory.expand iow.toNat isw.toNat).expand oow.toNat osw.toNat).read iow.toNat isw.toNat))) := by
            rw [hm]; rfl
          rw [segment_ext o call m ms fn b hext term hexec hcall]
          have hb : ((s1.memory.expand iow.toNat isw.toNat).expand oow.toNat osw.toNat).bytes = s1.memory.bytes := by
            rw [bytes_expand, bytes_expand]
          refine ⟨ms, env1, s1, [gw, aw], _, _, oow, osw, rfl, hst, he1, hs1, hb, hoo, hos, ?_, ?_, rfl, rfl⟩
          · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact ha
          · refine (read_eq hs1.st _ hb iow.toNat isw.toNat).trans ?_
            rw [hio, his]
      · simp at h
  · exact symSegmentPlain_sound hc henv m hK h hst he hs

theorem symStepC_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) (m : Module)
    {K : Facts} (hK : K.Hold ρ) {w0 : List Event} {a : CAns} {stack : List CReturn} {pos : Pos}
    {cenv : CEnv} {st : SState} {ph : Phase}
    {r : CNext} (h : symStepC ev cv m sel n K stack pos cenv st ph = some r) {ms : List Return}
    {env : Env} {s : State} (hst : CStackRel ρ call ms stack) (he : CEnvRel ρ call env cenv)
    (hs : PhRel ρ o n w0 a s st ph) : CNextOk ρ call o m n w0 a (moduleBlock o call m (ms, pos, env, s)) r := by
  cases pos with
  | enter fn pred b =>
    simp only [symStepC] at h
    simp only [moduleBlock]
    cases hf : m.functions[fn]? with
    | none => simp [hf] at h
    | some f =>
      simp only [hf] at h ⊢
      cases hb : f.blocks[b]? with
      | none => simp [hb] at h
      | some blk =>
        simp only [hb] at h ⊢
        cases hp : symPhisC cenv pred blk.phis cenv with
        | none => simp [hp] at h
        | some cenv1 =>
          simp only [hp] at h
          obtain ⟨env1, hbind, he1⟩ := symPhisC_sound he pred blk.phis cenv cenv1 env hp he
          simp only [hbind]
          exact symSegmentC_sound hc henv m hK h hst he1 hs
  | resume fn b insts term => exact symSegmentC_sound hc henv m hK h hst he hs


/-! ## The runs -/

/-- What the run after the call shows: its tree's result, or the bubbled failure of the answer. -/
def POut.res (ρ : Val) (a : CAns) : POut → Res
  | .tree T => T.eval ρ
  | .bubble => bubbleRes ρ a

theorem iterate_step_eq {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x y : σ}
    (h : step x = step y) : ∀ k, iterate step k x = iterate step k y
  | 0 => rfl
  | _ + 1 => by simp only [iterate, h]

theorem symRunPost_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module)
    {w0 : List Event} {a : CAns} :
    ∀ (fuel : Nat) (stack : List CReturn) (pos : Pos) (cenv : CEnv) (st : SState) (ph : Phase)
      (K : Facts) (out : POut), symRunPost ev cv m sel n fuel stack pos cenv st ph K = some out →
      ∀ ms env s, CStackRel ρ call ms stack → CEnvRel ρ call env cenv → PhRel ρ o n w0 a s st ph →
        K.Hold ρ → ∃ k r, iterate (moduleBlock o call m) k (ms, pos, env, s) = some r ∧
          observe call r.2 r.1 = (out.res ρ a).obs
  | 0, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _ => by simp [symRunPost] at h
  | fuel + 1, stack, pos, cenv, st, ph, K, out, h, ms, env, s, hst, he, hs, hK => by
    simp only [symRunPost] at h
    cases ph with
    | pre => simp at h
    | post rdc =>
    simp only at h
    cases hx : symStepC ev cv m sel n K stack pos cenv st (.post rdc) with
    | none => simp [hx] at h
    | some x =>
      have hn := symStepC_sound hc henv m hK hx hst he hs
      simp only [hx] at h
      cases x with
      | done T' =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨r, hr, hobs⟩ := hn
        exact ⟨1, r, iterate_inl hr, hobs⟩
      | bubble =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨r, hr, hobs⟩ := hn
        exact ⟨1, r, iterate_inl hr, hobs⟩
      | go stack' pos' cenv' st' ph' =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        obtain ⟨k, r, hk, hobs⟩ :=
          symRunPost_sound hc o henv m fuel stack' pos' cenv' st' ph' K out h ms' env' s' hst' he' hs' hK
        exact ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, hobs⟩
      | fork e stack' fn b yes no cenv' st' ph' =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        cases ht : symRunPost ev cv m sel n fuel stack' (.enter fn b yes) cenv' st' ph' (K.add e true) with
        | none => simp [ht] at h
        | some t =>
          cases hf : symRunPost ev cv m sel n fuel stack' (.enter fn b no) cenv' st' ph' (K.add e false) with
          | none => simp [ht, hf] at h
          | some f =>
            by_cases h0 : e.eval ρ = 0
            · simp only [h0, ite_true] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRunPost_sound hc o henv m fuel stack' _ cenv' st' ph' _ f hf
                ms' env' s' hst' he' hs' (hK.add e false (by simp [h0]))
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              cases t <;> cases f <;> simp only [ht, hf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
                simp only [POut.res, Tree.eval, h0, ite_true] at hobs ⊢ <;> exact hobs
            · simp only [h0, ite_false] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRunPost_sound hc o henv m fuel stack' _ cenv' st' ph' _ t ht
                ms' env' s' hst' he' hs' (hK.add e true (by simp [h0]))
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              cases t <;> cases f <;> simp only [ht, hf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
                simp only [POut.res, Tree.eval, h0, ite_false] at hobs ⊢ <;> exact hobs
      | callAt => simp at h


/-! ## The memory a call writes -/

theorem wordAt_byte (data : List Nat) (k i : Nat) (hi : i < 32) :
    wordAt data (32 * k) / 256 ^ (31 - i) % 256 = data.getD (32 * k + i) 0 % 256 := by
  unfold wordAt
  rw [← byte_toNat, SolarTV.Milestone.W1.byte_load _ _ _ hi]
  simp [dataMem, BitVec.toNat_ofNat]

theorem lt_wordSize_256 {x : Nat} (h : x < 256) : x < wordSize := lt_of_lt_of_le h (by decide)

theorem OByte.word_eval (ρ : Val) (b : OByte) : b.word.eval ρ = b.eval ρ := by
  cases b with
  | lit b =>
    simp only [OByte.word, OByte.eval, WExpr.eval]
    exact Nat.mod_eq_of_lt (lt_wordSize_256 (Nat.mod_lt _ (by decide)))
  | byteOf e i =>
    simp only [OByte.word, OByte.eval]
    by_cases hi : i < 32
    · simp only [hi, ↓reduceIte]
      have hi' : i % wordSize = i := Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by decide))
      have : (WExpr.bin .byte (.lit i) e).eval ρ = (if i % wordSize < 32 then
          e.eval ρ / 256 ^ (31 - i % wordSize) % 256 else 0) % wordSize := rfl
      rw [this]
      simp only [hi', hi, ↓reduceIte]
      exact Nat.mod_eq_of_lt (lt_wordSize_256 (Nat.mod_lt _ (by decide)))
    · simp only [hi, ↓reduceIte]
      have : (WExpr.bin .and e (.lit 255)).eval ρ = (e.eval ρ &&& (255 % wordSize)) % wordSize := rfl
      rw [this]
      have h255 : (255 : Nat) % wordSize = 2 ^ 8 - 1 := by decide
      rw [h255, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_wordSize_256 (Nat.mod_lt _ (by decide)))]
      have : 31 - i = 0 := by omega
      rw [this]
      simp

theorem AnsAt.data_lt {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) {j : Nat} (hj : j < a.data.length) : a.data.getD j 0 < 256 := by
  have := h.byte [] rfl j hj
  rw [← this]
  exact (returndataByte o (w0 ++ []) j).isLt

theorem AnsAt.word_lt {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) {j : Nat} (hj : j < a.data.length) :
    ρ.args.getD (n + 1 + j / 32) 0 = wordAt a.data (32 * (j / 32)) := by
  have hw := withAns_word ρ n a (k := j / 32) (by have := Nat.div_mul_le_self j 32; omega)
  rw [h.val] at hw
  exact hw

theorem AnsAt.word {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) {j : Nat} (hj : j < a.data.length) :
    (ρ.args.getD (n + 1 + j / 32) 0) / 256 ^ (31 - j % 32) % 256 = a.data.getD j 0 := by
  rw [h.word_lt hj, wordAt_byte _ _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]
  exact Nat.mod_eq_of_lt (h.data_lt hj)

theorem AnsAt.argWord {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) {j : Nat} (hj : j < a.data.length) :
    (WExpr.arg (n + 1 + j / 32)).eval ρ = ρ.args.getD (n + 1 + j / 32) 0 := by
  show ρ.args.getD (n + 1 + j / 32) 0 % wordSize = _
  rw [h.word_lt hj]
  exact Nat.mod_eq_of_lt ((dataMem a.data).load (32 * (j / 32))).isLt

theorem AnsAt.retByte_eval {o : Oracle} {n : Nat} {ρ : Val} {w0 : List Event} {a : CAns}
    (h : AnsAt o n ρ w0 a) {j : Nat} (hj : j < a.data.length) :
    (Generic.retByte n j).eval ρ = a.data.getD j 0 := by
  have hj32 : j % 32 < 32 := Nat.mod_lt _ (by decide)
  have hm : j % 32 % wordSize = j % 32 := Nat.mod_eq_of_lt (lt_of_lt_of_le hj32 (by decide))
  have e : (Generic.retByte n j).eval ρ = (if j % 32 % wordSize < 32 then
      (WExpr.arg (n + 1 + j / 32)).eval ρ / 256 ^ (31 - j % 32 % wordSize) % 256 else 0) % wordSize := rfl
  rw [e, hm, if_pos hj32, h.argWord hj, h.word hj]
  exact Nat.mod_eq_of_lt (lt_wordSize_256 (h.data_lt hj))

theorem called_bytes (o : Oracle) (s : State) (mem : Mem) (ooW osW : Word) (w : List Event) (i : Nat) :
    (called o .staticcall s mem ooW osW w).memory.bytes i =
      if ooW.toNat ≤ i ∧ i < ooW.toNat + min osW.toNat (returndataSize o w).toNat then
        returndataByte o w (i - ooW.toNat)
      else mem.bytes i := by
  simp only [called, bytes_write']

theorem logs_call (s : State) (seen : List Word) (input : List Memory.Byte) (m : Mem) :
    logs { s with memory := m, world := callWorld s seen input } = logs s := by
  simp only [logs, callWorld, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]

theorem called_eq (o : Oracle) (s : State) (mem : Mem) (ooW osW : Word) (w : List Event) :
    called o .staticcall s mem ooW osW w =
      { s with memory := (called o .staticcall s mem ooW osW w).memory, world := w } := rfl

/-- The state after the call holds the symbolic state over the memory `mem'`, when its bytes are
the symbolic ones. -/
theorem stRel_called {ρ : Val} {s : State} {st : SState} (hs : StRel ρ s st) (o : Oracle) (mem : Mem)
    (ooW osW : Word) (seen : List Word) (input : List Memory.Byte) (mem' : Nat → OByte)
    (hm : ∀ i, ((called o .staticcall s mem ooW osW (callWorld s seen input)).memory.bytes i).toNat =
      (mem' i).eval ρ) :
    StRel ρ (called o .staticcall s mem ooW osW (callWorld s seen input)) { st with mem := mem' } where
  mem := hm
  store := hs.store
  world := by
    rw [called_eq, logs_call]
    exact hs.world

theorem lt_eval (ρ : Val) (x y : WExpr) :
    (WExpr.bin .lt x y).eval ρ = (if x.eval ρ < y.eval ρ then 1 else 0) % wordSize := rfl

theorem sel_eval (ρ : Val) (c x y : WExpr) :
    (WExpr.sel c x y).eval ρ = if c.eval ρ = 0 then y.eval ρ else x.eval ρ := rfl

theorem byteOf31_eval (ρ : Val) (e : WExpr) : (OByte.byteOf e 31).eval ρ = e.eval ρ % 256 := by
  simp [OByte.eval]

/-- The bytes a call writes when the return data is shorter than the output range. -/
theorem memShort_eval {ρ : Val} {o : Oracle} {n : Nat} {s : State} {st : SState} (hs : StRel ρ s st)
    {mem : Mem} (hmem : mem.bytes = s.memory.bytes) {ooW osW : Word} {seen : List Word}
    {input : List Memory.Byte} {a : CAns} (hA : AnsAt o n ρ (callWorld s seen input) a)
    (hshort : a.data.length < osW.toNat) (i : Nat) :
    ((called o .staticcall s mem ooW osW (callWorld s seen input)).memory.bytes i).toNat =
      (memShort st.mem n ooW.toNat osW.toNat i).eval ρ := by
  have hsize : (returndataSize o (callWorld s seen input)).toNat = a.data.length := by
    have := hA.size [] rfl; simpa using this
  rw [called_bytes, hsize, Nat.min_eq_right (Nat.le_of_lt hshort), hmem]
  unfold memShort
  have hosl := osW.isLt
  by_cases hr : ooW.toNat ≤ i ∧ i < ooW.toNat + osW.toNat
  · rw [if_pos hr, byteOf31_eval, sel_eval, lt_eval, hA.arg_size]
    have hj1 : (WExpr.lit (i - ooW.toNat + 1)).eval ρ = i - ooW.toNat + 1 := by
      show (i - ooW.toNat + 1) % wordSize = _
      exact Nat.mod_eq_of_lt (show _ < 2 ^ 256 by omega)
    rw [hj1]
    by_cases hj : i - ooW.toNat < a.data.length
    · have hi : ooW.toNat ≤ i ∧ i < ooW.toNat + a.data.length := by omega
      have hn : ¬ a.data.length < i - ooW.toNat + 1 := by omega
      rw [if_pos hi, if_neg hn, Nat.zero_mod, if_pos rfl, hA.retByte_eval hj,
        Nat.mod_eq_of_lt (hA.data_lt hj)]
      have := hA.byte [] rfl (i - ooW.toNat) hj
      simpa using this
    · have hi : ¬ (ooW.toNat ≤ i ∧ i < ooW.toNat + a.data.length) := by omega
      have hn : a.data.length < i - ooW.toNat + 1 := by omega
      rw [if_neg hi, if_pos hn, Nat.one_mod_eq_one.mpr (by decide), if_neg (by decide), OByte.word_eval,
        ← hs.mem i]
      exact (Nat.mod_eq_of_lt (s.memory.bytes i).isLt).symm
  · have hi : ¬ (ooW.toNat ≤ i ∧ i < ooW.toNat + a.data.length) := by omega
    rw [if_neg hi, if_neg hr]
    exact hs.mem i

/-- The bytes a call writes when the return data fills the output range. -/
theorem memLong_eval {ρ : Val} {o : Oracle} {n : Nat} {s : State} {st : SState} (hs : StRel ρ s st)
    {mem : Mem} (hmem : mem.bytes = s.memory.bytes) {ooW osW : Word} {seen : List Word}
    {input : List Memory.Byte} {a : CAns} (hA : AnsAt o n ρ (callWorld s seen input) a)
    (hlong : osW.toNat ≤ a.data.length) (i : Nat) :
    ((called o .staticcall s mem ooW osW (callWorld s seen input)).memory.bytes i).toNat =
      (memLong st.mem n ooW.toNat osW.toNat i).eval ρ := by
  have hsize : (returndataSize o (callWorld s seen input)).toNat = a.data.length := by
    have := hA.size [] rfl; simpa using this
  rw [called_bytes, hsize, Nat.min_eq_left hlong, hmem]
  unfold memLong
  by_cases hr : ooW.toNat ≤ i ∧ i < ooW.toNat + osW.toNat
  · rw [if_pos hr, if_pos hr]
    have hj : i - ooW.toNat < a.data.length := by omega
    show _ = (WExpr.arg (n + 1 + (i - ooW.toNat) / 32)).eval ρ / 256 ^ (31 - (i - ooW.toNat) % 32) % 256
    rw [hA.argWord hj, hA.word hj]
    have := hA.byte [] rfl (i - ooW.toNat) hj
    simpa using this
  · rw [if_neg hr, if_neg hr]
    exact hs.mem i

theorem symRunAfter_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module)
    {fuel : Nat} {stack : List CReturn} {dst : Option Nat} {pos : Pos} {cenv : CEnv} {st : SState}
    {K : Facts} {flag : Nat} {out : POut}
    {ms : List Return} {env : Env} {s : State} {seen : List Word} {input : List Memory.Byte} {mem : Mem}
    {ooW osW : Word}
    (h : symRunAfter ev cv m sel n fuel stack dst pos cenv st ooW.toNat osW.toNat K flag = some out)
    (hst : CStackRel ρ call ms stack) (he : CEnvRel ρ call env cenv)
    (hs : PreRel ρ s st) (hmem : mem.bytes = s.memory.bytes)
    (hK : K.Hold ρ) {a : CAns} (hA : AnsAt o n ρ (callWorld s seen input) a)
    (hflag : flag = if a.ok then 1 else 0) :
    ∃ k r, iterate (moduleBlock o call m) k
        (ms, pos, bindDst env dst (some (callFlag o (callWorld s seen input))),
          called o .staticcall s mem ooW osW (callWorld s seen input)) = some r ∧
      observe call r.2 r.1 = (out.res ρ a).obs := by
  have he' : CEnvRel ρ call (bindDst env dst (some (callFlag o (callWorld s seen input))))
      (setDst cenv dst flag) := by
    cases dst with
    | none => exact he
    | some d =>
      refine he.set ?_ d
      show (callFlag o (callWorld s seen input)).toNat = flag % wordSize
      rw [hA.flag, hflag]
      split <;> decide
  have hworld : ∃ rest, (called o .staticcall s mem ooW osW (callWorld s seen input)).world =
      callWorld s seen input ++ rest ∧ machineCalls rest = [] := ⟨[], by simp [called], rfl⟩
  unfold symRunAfter at h
  split at h
  · -- no output range
    rename_i hos0
    have hm : ∀ i, ((called o .staticcall s mem ooW osW (callWorld s seen input)).memory.bytes i).toNat =
        (st.mem i).eval ρ := by
      intro i
      rw [called_bytes, hos0, Nat.zero_min, Nat.add_zero]
      have : ¬ (ooW.toNat ≤ i ∧ i < ooW.toNat) := by omega
      rw [if_neg this, hmem]
      exact hs.st.mem i
    have hrel : PhRel ρ o n (callWorld s seen input) a (called o .staticcall s mem ooW osW (callWorld s seen input))
        st (.post none) := ⟨hA, stRel_called hs.st o mem ooW osW seen input st.mem hm, hworld⟩
    exact symRunPost_sound hc o henv m fuel stack pos _ st _ K out h ms _ _ hst he' hrel hK
  · have hosl := osW.isLt
    have hcond : (shortCond n osW.toNat).eval ρ = if a.data.length < osW.toNat then 1 else 0 := by
      unfold shortCond
      rw [lt_eval, hA.arg_size]
      have : (WExpr.lit osW.toNat).eval ρ = osW.toNat := Nat.mod_eq_of_lt hosl
      rw [this]
      split <;> decide
    cases hsr : symRunPost ev cv m sel n fuel stack pos (setDst cenv dst flag)
        { st with mem := memShort st.mem n ooW.toNat osW.toNat } (.post none)
        (K.add (shortCond n osW.toNat) true) with
    | none => simp [hsr] at h
    | some ts =>
    cases hlr : symRunPost ev cv m sel n fuel stack pos (setDst cenv dst flag)
        { st with mem := memLong st.mem n ooW.toNat osW.toNat } (.post none)
        (K.add (shortCond n osW.toNat) false) with
    | none => simp [hsr, hlr] at h
    | some tl =>
    by_cases hshort : a.data.length < osW.toNat
    · have hrel : PhRel ρ o n (callWorld s seen input) a
          (called o .staticcall s mem ooW osW (callWorld s seen input))
          { st with mem := memShort st.mem n ooW.toNat osW.toNat } (.post none) :=
        ⟨hA, stRel_called hs.st o mem ooW osW seen input _ (memShort_eval hs.st hmem hA hshort), hworld⟩
      obtain ⟨k, r, hk, hobs⟩ := symRunPost_sound hc o henv m fuel stack pos _ _ _ _ ts hsr ms _ _ hst he'
        hrel (hK.add _ true (by rw [hcond, if_pos hshort]; decide))
      refine ⟨k, r, hk, ?_⟩
      cases ts <;> cases tl <;> simp only [hsr, hlr, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        simp only [POut.res, Tree.eval, hcond, if_pos hshort, one_ne_zero, ↓reduceIte] at hobs ⊢ <;> exact hobs
    · have hlong : osW.toNat ≤ a.data.length := by omega
      have hrel : PhRel ρ o n (callWorld s seen input) a
          (called o .staticcall s mem ooW osW (callWorld s seen input))
          { st with mem := memLong st.mem n ooW.toNat osW.toNat } (.post none) :=
        ⟨hA, stRel_called hs.st o mem ooW osW seen input _ (memLong_eval hs.st hmem hA hlong), hworld⟩
      obtain ⟨k, r, hk, hobs⟩ := symRunPost_sound hc o henv m fuel stack pos _ _ _ _ tl hlr ms _ _ hst he'
        hrel (hK.add _ false (by rw [hcond, if_neg hshort]; simp))
      refine ⟨k, r, hk, ?_⟩
      cases ts <;> cases tl <;> simp only [hsr, hlr, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        simp only [POut.res, Tree.eval, hcond, if_neg hshort, ↓reduceIte] at hobs ⊢ <;> exact hobs


/-! ## The run before the call -/

/-- **The oracle answers the external call the path reaches as the callee `A` does**: in every world
that ends with that call (its target, no value, its input bytes, the caller's storage after the
writes before it and zero transient storage), before which the world has no call, the oracle's answer
is `A`'s on the request's values and the caller's storage (`AnsAt`). -/
def OAns (o : Oracle) (A : Callee) (ρ : Val) (n : Nat) (T : CTree) : Prop :=
  ∀ r ws n', T.reach ρ = some (r, ws, n') → ∀ (pre : List Event) (seen : List Word)
    (input : List Memory.Byte) (sto : Word → Word),
    machineCalls pre = [] → (seen.getD 1 0).toNat = r.target.eval ρ →
    input.map BitVec.toNat = r.input.map (OByte.eval ρ) →
    (∀ k : Word, (sto k).toNat = Writes.store ρ ws k.toNat) →
    AnsAt o n ρ (pre ++ [.call .staticcall seen input sto (fun _ => 0)]) (A (r.eval ρ) (Writes.store ρ ws))

theorem OAns.ite_true {o : Oracle} {A : Callee} {ρ : Val} {n : Nat} {e : WExpr} {t f : CTree}
    (h : OAns o A ρ n (.ite e t f)) (he : ¬ e.eval ρ = 0) : OAns o A ρ n t :=
  fun r ws n' hr => h r ws n' (by simp [CTree.reach, he, hr])

theorem OAns.ite_false {o : Oracle} {A : Callee} {ρ : Val} {n : Nat} {e : WExpr} {t f : CTree}
    (h : OAns o A ρ n (.ite e t f)) (he : e.eval ρ = 0) : OAns o A ρ n f :=
  fun r ws n' hr => h r ws n' (by simp [CTree.reach, he, hr])

theorem symRunPre_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module) (A : Callee) :
    ∀ (fuel : Nat) (stack : List CReturn) (pos : Pos) (cenv : CEnv) (st : SState) (K : Facts)
      (T : CTree), symRunPre ev cv m sel n fuel stack pos cenv st K = some T →
      ∀ ms env s, CStackRel ρ call ms stack → CEnvRel ρ call env cenv → PreRel ρ s st →
        K.Hold ρ → OAns o A ρ n T → ∃ k r, iterate (moduleBlock o call m) k (ms, pos, env, s) = some r ∧
          observe call r.2 r.1 = (T.eval ρ A).obs
  | 0, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp [symRunPre] at h
  | fuel + 1, stack, pos, cenv, st, K, T, h, ms, env, s, hst, he, hs, hK, hA => by
    simp only [symRunPre] at h
    cases hx : symStepC ev cv m sel n K stack pos cenv st .pre with
    | none => simp [hx] at h
    | some x =>
      have hn := symStepC_sound (w0 := []) (a := ⟨false, []⟩) hc henv m hK hx hst he hs
      simp only [hx] at h
      cases x with
      | done T' =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨r, hr, hobs⟩ := hn
        exact ⟨1, r, iterate_inl hr, hobs⟩
      | bubble => simp at h
      | go stack' pos' cenv' st' ph' =>
        cases ph' with
        | post _ => simp at h
        | pre =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        obtain ⟨k, r, hk, hobs⟩ :=
          symRunPre_sound hc o henv m A fuel stack' pos' cenv' st' K T h ms' env' s' hst' he' hs' hK hA
        exact ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, hobs⟩
      | fork e stack' fn b yes no cenv' st' ph' =>
        cases ph' with
        | post _ => simp at h
        | pre =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        cases ht : symRunPre ev cv m sel n fuel stack' (.enter fn b yes) cenv' st' (K.add e true) with
        | none => simp [ht] at h
        | some t =>
          cases hf : symRunPre ev cv m sel n fuel stack' (.enter fn b no) cenv' st' (K.add e false) with
          | none => simp [ht, hf] at h
          | some f =>
            simp only [ht, hf, Option.some.injEq] at h
            subst h
            by_cases h0 : e.eval ρ = 0
            · simp only [h0, ite_true] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRunPre_sound hc o henv m A fuel stack' _ cenv' st' _ f hf
                ms' env' s' hst' he' hs' (hK.add e false (by simp [h0])) (hA.ite_false h0)
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              simp only [CTree.eval, h0, ite_true]
              exact hobs
            · simp only [h0, ite_false] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRunPre_sound hc o henv m A fuel stack' _ cenv' st' _ t ht
                ms' env' s' hst' he' hs' (hK.add e true (by simp [h0])) (hA.ite_true h0)
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              simp only [CTree.eval, h0, ite_false]
              exact hobs
      | callAt rq stack' dst pos' cenv' st' oo os =>
        obtain ⟨ms', env1, s1, seen, input, mem, ooW, osW, hxm, hst', he1, hs1, hmem, hoo, hos,
          htgt, hin, hstat, hval⟩ := hn
        subst hoo hos
        cases h1 : symRunAfter ev cv m sel n fuel stack' dst pos' cenv' st' ooW.toNat osW.toNat K 1 with
        | none => simp [h1] at h
        | some o1 =>
        cases h0 : symRunAfter ev cv m sel n fuel stack' dst pos' cenv' st' ooW.toNat osW.toNat K 0 with
        | none => simp [h1, h0] at h
        | some o0 =>
        cases o1 with
        | bubble => simp [h1, h0] at h
        | tree t =>
        cases o0 with
        | tree _ => simp [h1, h0] at h
        | bubble =>
        simp only [h1, h0, Option.some.injEq] at h
        subst h
        have hAns := hA rq st'.writes n (by simp [CTree.reach]) s1.world seen input s1.storage hs1.calls
          htgt hin hs1.st.store
        rw [← hs1.transient] at hAns
        have hAw : AnsAt o n ρ (callWorld s1 seen input) (A (rq.eval ρ) (Writes.store ρ st'.writes)) := hAns
        have hstep := iterate_step_eq (step := moduleBlock o call m) hxm
        cases hok : (A (rq.eval ρ) (Writes.store ρ st'.writes)).ok with
        | true =>
          obtain ⟨k, r, hk, hobs⟩ := symRunAfter_sound hc o henv m h1 hst' he1 hs1 hmem hK hAw
            (by rw [hok]; rfl)
          refine ⟨k, r, ?_, ?_⟩
          · cases k with
            | zero => simp [iterate] at hk
            | succ k =>
              simp only [iterate] at hk ⊢
              rw [hxm]
              exact hk
          · simp only [CTree.eval, hok, ↓reduceIte, hAw.val]
            simpa [POut.res] using hobs
        | false =>
          obtain ⟨k, r, hk, hobs⟩ := symRunAfter_sound hc o henv m h0 hst' he1 hs1 hmem hK hAw
            (by rw [hok]; rfl)
          refine ⟨k, r, ?_, ?_⟩
          · cases k with
            | zero => simp [iterate] at hk
            | succ k =>
              simp only [iterate] at hk ⊢
              rw [hxm]
              exact hk
          · simp only [CTree.eval, hok, Bool.false_eq_true, ↓reduceIte]
            simpa [POut.res] using hobs

theorem startState_world (m : Module) (s : State) : (m.startState s).world = s.world := by
  unfold Module.startState; split <;> [exact start_world _ _; rfl]

theorem startState_transient (m : Module) (s : State) : (m.startState s).transient = s.transient := by
  unfold Module.startState; split <;> [exact start_transient _ _; rfl]

/-- **SolarTV's lowered MIR runs a module as its symbolic call tree**: on a call that gives the
symbolic run what `CallFacts` says, under every oracle that the environment flag allows and that
answers the external call the path reaches as the callee `A` does (`OAns`), the fuel-free semantics
shows the call tree's result for `A`. -/
theorem symTreeC_sound {sel n : Nat} {ρ : Val} {call : Call} (hc : CallFacts sel n ρ call)
    (o : Oracle) (m : Module) {fuel : Nat} {env : EnvFlags} (henv : EnvAsk env o ρ) {T : CTree}
    (h : symTreeC m sel n fuel env = some T) (A : Callee) (hA : OAns o A ρ n T) :
    (moduleSem o).run m call = some (T.eval ρ A).obs := by
  unfold symTreeC at h
  have hs0 := (StRel.initial call hc.store hc.ok).entryStart m
  have hpre : PreRel ρ (m.startState (State.initial call)) (symEntryStart m SState.initial) :=
    ⟨hs0, by rw [startState_world]; rfl, by rw [startState_transient]; rfl⟩
  obtain ⟨k, r, hk, hr⟩ := symRunPre_sound hc.at o henv m A fuel _ _ _ _ _ T h [] _ _ trivial
    (CEnvRel.zero ρ call) hpre (fun _ hp => absurd hp List.not_mem_nil) hA
  have e : moduleLayer.result o m call = some r := moduleLayer.result_of_ends ⟨k, hk⟩
  show (moduleLayer.result o m call).map _ = _
  rw [e, ← hr]
  rfl

/-- info: 'SolidCore.Refinement.Generic.symTreeC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symTreeC_sound

end SolidCore.Refinement.Generic

