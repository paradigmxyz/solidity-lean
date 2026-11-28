import Verify.Phase3.RecSum.gen.RecSum.Stage0
import W1Proofs.Tactic
import SolarTV.Termination

/-! # RecSum: the recursive function's contract, by its measure

`sum(n)` calls itself at `n - 1` until `n = 0`. Its contract, cut at its entry and at the point it
resumes after its recursive call (the cut points of its stage proofs), is proved by induction on
the measure `n` (`@custom:decreases n`): from the entry with argument `n` under any frame `r` and
any stack `rs` below it, the lowered MIR reaches the caller's resume point with `n * (n + 1) / 2`
bound to the call's result, the frame popped and the state unchanged (`sum_returns`), for every
`n ≤ 64` (the bound `total` requires; it keeps `n * (n + 1) / 2` and every frame's addition far
below 2^256). Each induction step runs the body as two segments: from the entry to the recursive
call (`enter_call`), the contract at `n - 1`, then from the resume point to the return
(`resume_ret`). `total_returns` runs a whole call of `total(n)` on top. -/

namespace SolarTV.Milestone.RecSum

open Machine SolarTV.Export.RecSum SolarTV.CutPoint SolarTV.Milestone.W1

/-- `0 + 1 + ... + n`. -/
def tri (n : Nat) : Nat := n * (n + 1) / 2

theorem tri_succ (m : Nat) : tri (m + 1) = tri m + (m + 1) := by
  unfold tri
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by
    rw [show m + 1 + 1 = m + 2 from rfl, Nat.mul_add (m + 1) m 2, Nat.mul_comm (m + 1) m,
      Nat.mul_comm (m + 1) 2]
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem tri_le : ∀ n, n ≤ 64 → tri n ≤ 2080 := by
  intro n hn
  have : n * (n + 1) ≤ 64 * 65 := Nat.mul_le_mul hn (by omega)
  unfold tri; omega

/-- One step of a run from a configuration the code has built (a pair), as `steps` takes it. -/
@[defeq] theorem steps_mk {α β ρ : Type} (step : α × β → Option (ρ ⊕ (α × β))) (k : Nat) (a : α) (b : β) :
    steps step (k + 1) (a, b) =
      match step (a, b) with
      | some (.inl r) => some (.inl r)
      | some (.inr y) => steps step k y
      | none => none := by
  rw [steps]
  cases step (a, b) with
  | none => rfl
  | some v => cases v <;> rfl

@[defeq] theorem steps_zero {α ρ : Type} (step : α → Option (ρ ⊕ α)) (x : α) :
    steps step 0 x = some (.inr x) := rfl

theorem sub_one_ofNat (m : Nat) (h : m + 1 < 2 ^ 256) :
    EvmRules.Evm.sub (BitVec.ofNat 256 (m + 1)) 1 = BitVec.ofNat 256 m := by
  apply BitVec.eq_of_toNat_eq
  simp [EvmRules.Evm.sub, BitVec.toNat_sub]
  omega

theorem add_ofNat (a b : Nat) :
    EvmRules.Evm.add (BitVec.ofNat 256 a) (BitVec.ofNat 256 b) = BitVec.ofNat 256 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [EvmRules.Evm.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lt_add_ofNat (a b : Nat) (h : a + b < 2 ^ 256) :
    EvmRules.Evm.lt (BitVec.ofNat 256 (a + b)) (BitVec.ofNat 256 b) = 0 := by
  unfold EvmRules.Evm.lt
  have : (BitVec.ofNat 256 (a + b)).ult (BitVec.ofNat 256 b) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  simp [this]

theorem eq_succ_zero (m : Nat) (h : m + 1 < 2 ^ 256) :
    EvmRules.Evm.eq (BitVec.ofNat 256 (m + 1)) 0 = 0 := by
  have hne : BitVec.ofNat 256 (m + 1) ≠ 0 := by
    intro e
    have := congrArg BitVec.toNat e
    simp at this
    omega
  simp [EvmRules.Evm.eq]
  exact hne

/-- The rest of the recursive call's block after the call, as the frame keeps it. -/
abbrev rest : List MIR.Lowered.Inst := [.pure 9 .add [.value 7, .value 0], .pure 10 .lt [.value 9, .value 0]]

/-- The frame the recursive call pushes. -/
abbrev recFrame (c : MIR.Lowered.Env) : MIR.Lowered.Return := ⟨0, 2, some 7, rest, .branch (.value 10) 3 4, c, [], none⟩

set_option hygiene false in
/-- Evaluate a run of the module by its definitions, as `sym_exec` does. -/
macro "mir_run" : tactic => `(tactic| (
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | simp only [steps_mk, steps_zero] | sym_eval | sym_cond | sym_mem)))

/-- The base case: `n = 0` returns 0, in two blocks. -/
theorem sum_zero (o : Oracle) (call : Call) (r : MIR.Lowered.Return) (rs : List MIR.Lowered.Return)
    (env : MIR.Lowered.Env) (s : State) (d : Nat) (hd : r.dst = some d) (he : r.extras = [])
    (hp : r.publish = none) (h0 : env 0 = BitVec.ofNat 256 0) :
    steps (MIR.Lowered.moduleBlock o call stage0) 2 (r :: rs, .enter 0 0 0, env, s) =
      some (.inr (rs, .resume r.fn r.block r.rest r.term, r.env.set d (BitVec.ofNat 256 (tri 0)), s)) := by
  obtain ⟨fn, blk, dst, rest, term, renv, extras, publish⟩ := r
  simp only at hd he hp
  subst hd he hp
  mir_run
  rfl

/-- From the entry with argument `m + 1`: the recursive call at `m`, with the caller's values `c`
(`c 0` is the argument) in the frame it pushes. -/
theorem enter_call (o : Oracle) (call : Call) (m : Nat) (hm : m + 1 < 2 ^ 256) (r : MIR.Lowered.Return)
    (rs : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State)
    (h0 : env 0 = BitVec.ofNat 256 (m + 1)) :
    ∃ c e, steps (MIR.Lowered.moduleBlock o call stage0) 2 (r :: rs, .enter 0 0 0, env, s) =
        some (.inr (recFrame c :: r :: rs, .enter 0 0 0, e, s)) ∧
      c 0 = BitVec.ofNat 256 (m + 1) ∧ e 0 = BitVec.ofNat 256 m := by
  have hz : ¬ ((0 : EvmRules.Word) = BitVec.ofNat 256 (m + 1)) := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  have hq := eq_succ_zero m hm
  refine ⟨(env.set 2 (EvmRules.Evm.eq (env 0) 0)).set 6 (EvmRules.Evm.sub (env 0) 1),
    MIR.Lowered.Env.set (fun _ => 0) 0 (EvmRules.Evm.sub (env 0) 1), ?_, ?_, ?_⟩
  · mir_run
  · simp [MIR.Lowered.Env.set, h0]
  · simp [MIR.Lowered.Env.set, h0]
    exact sub_one_ofNat m hm

/-- From the point the recursive call resumes, with the callee's result `tri m` and the argument
`m + 1`: the return of `tri (m + 1)` to the frame below, with no overflow. -/
theorem resume_ret (o : Oracle) (call : Call) (m : Nat) (hm : tri m + (m + 1) < 2 ^ 256)
    (r : MIR.Lowered.Return) (rs : List MIR.Lowered.Return) (c : MIR.Lowered.Env) (s : State) (d : Nat)
    (hd : r.dst = some d) (he : r.extras = []) (hp : r.publish = none)
    (h0 : c 0 = BitVec.ofNat 256 (m + 1)) :
    steps (MIR.Lowered.moduleBlock o call stage0) 2
        (r :: rs, .resume 0 2 rest (.branch (.value 10) 3 4), c.set 7 (BitVec.ofNat 256 (tri m)), s) =
      some (.inr (rs, .resume r.fn r.block r.rest r.term, r.env.set d (BitVec.ofNat 256 (tri (m + 1))), s)) := by
  obtain ⟨fn, blk, dst, rest', term, renv, extras, publish⟩ := r
  simp only at hd he hp
  subst hd he hp
  have hadd := add_ofNat (tri m) (m + 1)
  have hlt := lt_add_ofNat (tri m) (m + 1) hm
  have hnlt : ¬ (BitVec.ofNat 256 (tri m + (m + 1)) < BitVec.ofNat 256 (m + 1)) := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]; omega
  mir_run
  rw [tri_succ]

/-- **The recursive function's contract, by its measure**: from its entry with argument `n ≤ 64`,
under any frame `r` (one result, bound to `d`) and any stack `rs` below it, the module reaches `r`'s
resume point with `n * (n + 1) / 2` bound to `d`, the frame popped and the state unchanged. By
induction on `n`: the recursive call at `n - 1` uses the contract at the lower measure. -/
theorem sum_returns (o : Oracle) (call : Call) : ∀ n, n ≤ 64 →
    ∀ (r : MIR.Lowered.Return) (rs : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State) (d : Nat),
      r.dst = some d → r.extras = [] → r.publish = none → env 0 = BitVec.ofNat 256 n →
      ∃ k, steps (MIR.Lowered.moduleBlock o call stage0) k (r :: rs, .enter 0 0 0, env, s) =
        some (.inr (rs, .resume r.fn r.block r.rest r.term, r.env.set d (BitVec.ofNat 256 (tri n)), s))
  | 0, _, r, rs, env, s, d, hd, he, hp, h0 => ⟨2, sum_zero o call r rs env s d hd he hp h0⟩
  | m + 1, hn, r, rs, env, s, d, hd, he, hp, h0 => by
    have hm : m + 1 < 2 ^ 256 := by omega
    obtain ⟨c, e, h1, hc, he0⟩ := enter_call o call m hm r rs env s h0
    obtain ⟨k, hk⟩ := sum_returns o call m (by omega) (recFrame c) (r :: rs) e s 7 rfl rfl rfl he0
    have hb : tri m + (m + 1) < 2 ^ 256 := by have := tri_le m (by omega); omega
    have h3 := resume_ret o call m hb r rs c s d hd he hp hc
    refine ⟨2 + (k + 2), ?_⟩
    rw [steps_add 2 (k + 2) _ _ h1, steps_add k 2 _ _ hk]
    exact h3

/-- The frame \`total\` pushes when it calls the recursive function. -/
abbrev outerFrame (c : MIR.Lowered.Env) : MIR.Lowered.Return :=
  ⟨1, 2, some 8, [.effect none .mstore [.const 0, .value 8]], .ret (.const 0) (.const 32), c, [], none⟩

/-- The state \`total\` calls the recursive function in: the free memory pointer stored. -/
abbrev S0 (call : Call) : State :=
  { memory := Mem.initial.store 64 128, storage := (State.initial call).storage,
    transient := (State.initial call).transient, world := (State.initial call).world }

/-- The values \`total\` keeps in the frame it pushes. -/
abbrev C0 (call : Call) : MIR.Lowered.Env :=
  ((((MIR.Lowered.Env.set (fun _ => 0) 14 (BitVec.ofNat 256 call.calldata.size)).set 16
    (EvmRules.Evm.lt (BitVec.ofNat 256 call.calldata.size) 36)).set 18 (calldataWord call 4)).set
    2 (EvmRules.Evm.gt (calldataWord call 4) 64)).set 22
    (EvmRules.Evm.or (EvmRules.Evm.gt (calldataWord call 4) 64)
      (EvmRules.Evm.lt (BitVec.ofNat 256 call.calldata.size) 36))

/-- What \`total(n)\` returns: the 32 bytes of \`n * (n + 1) / 2\`, and the state with them stored. -/
abbrev returned (call : Call) (n : Nat) : Halt × State :=
  (Halt.ret (Mem.wordBytes (BitVec.ofNat 256 (tri n))),
    { memory := (Mem.initial.store 64 128).store 0 (BitVec.ofNat 256 (tri n)),
      storage := (State.initial call).storage, transient := (State.initial call).transient,
      world := (State.initial call).world })

/-- **\`total(n)\` on the lowered MIR**: on a call with no value, \`total\`'s selector, a full argument
word and \`n ≤ 64\`, the module returns \`n * (n + 1) / 2\`. The recursion runs through \`sum_returns\`. -/
theorem total_returns (o : Oracle) (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64) :
    MIR.Lowered.moduleLayer.Ends o stage0 call (returned call (calldataWord call 4).toNat) := by
  have hg : ¬ (64 : EvmRules.Word) < calldataWord call 4 := by
    simp only [BitVec.lt_def]; simp; omega
  have h1 : steps (MIR.Lowered.moduleBlock o call stage0) 5
      ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call)) =
      some (.inr ([outerFrame (C0 call)], .enter 0 0 0,
        MIR.Lowered.Env.set (fun _ => 0) 0 (calldataWord call 4), S0 call)) := by
    mir_run
  have he : MIR.Lowered.Env.set (fun _ => 0) 0 (calldataWord call 4) 0 =
      BitVec.ofNat 256 (calldataWord call 4).toNat := by
    simp [MIR.Lowered.Env.set]
  obtain ⟨k, hk⟩ := sum_returns o call _ hn (outerFrame (C0 call)) [] _ (S0 call) 8 rfl rfl rfl he
  have h3 : steps (MIR.Lowered.moduleBlock o call stage0) 1
      ([], .resume 1 2 [.effect none .mstore [.const 0, .value 8]] (.ret (.const 0) (.const 32)),
        (C0 call).set 8 (BitVec.ofNat 256 (tri (calldataWord call 4).toNat)), S0 call) =
      some (.inl (returned call (calldataWord call 4).toNat)) := by
    mir_run
  refine ⟨5 + (k + 1), ?_⟩
  show Machine.iterate _ _ _ = _
  rw [iterate_eq]
  apply run_of_steps
  rw [steps_add 5 (k + 1) _ _ h1, steps_add k 1 _ _ hk]
  exact h3

end SolarTV.Milestone.RecSum
