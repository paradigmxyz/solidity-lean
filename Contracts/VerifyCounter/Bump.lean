import SolarTV.CutPointHoare
import W1Proofs.Segment
import W1Proofs.Stage
import verify_counter.gen.Counter.Stage0

/-!
# bump's loop on solar's first lowered MIR, through one cut point

`bump(n)` of solar's `crates/verify/examples/Counter.sol`:

    function bump(uint256 n) external {
        require(count + n <= limit, "over");
        for (uint256 i = 0; i < n; i++) { count++; }
    }

solar keeps `count` in a value across the loop (block 1 of function 4 of `stage0`, entered
from block 7 before the first iteration and from block 10 after each), caches it at memory 128
with a written flag at 160, and writes slot 0 once after the loop. One cut point, the loop's
header, splits every run into loop-free segments, each evaluated symbolically by solar-tv's
procedures.

* `stage0_post` (partial correctness, `CutPoint.post_of_start`): every end of stage0 on a
  call of bump meets `Post`: on success slot 0 holds the old `count` plus `n`, the sum does
  not wrap and is at most slot 1 (`limit`), and every other slot is unchanged. The invariant
  `Inv` at the header is the loop's `i <= n` and `count == old(count) + i` on the values that
  carry them (values 20 and 43 from block 10), with the storage unchanged and what the
  `require` checked.
* `stage0_ends` (total correctness, `CutPoint.ends_of_start`): every call of bump ends, and
  meets `Post`: `InvT` adds the memory cache and the slot-0 read that the compiler's facts
  (`assume`) compare, so no segment is stuck, and `rank` is the variant `n - i`.
* `post_of_certified`, `ends_of_certified`: the same of any program proved to match stage0's
  ends, backwards or forwards.

The header invariant is stated here over stage0's values, from the loop's annotations; the
segments check it, so a wrong one fails by mismatch, but nothing yet derives it from
solar-verify's inferred invariant. No sorry, native_decide or bv_decide.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegOk)

def cut : MIR.Lowered.Frame → Bool := fun x =>
  match x.2.1 with
  | .enter f _ b => (f == 4 && b == 1)
  | .resume .. => false

theorem cut_enter (rs : List MIR.Lowered.Return) (f p b : Nat) (env : MIR.Lowered.Env) (s : State) :
    cut (rs, .enter f p b, env, s) = ((f == 4 && b == 1)) := rfl

theorem cut_resume (rs : List MIR.Lowered.Return) (f b : Nat) (is : List MIR.Lowered.Inst) (t : MIR.Lowered.Terminator) (env : MIR.Lowered.Env) (s : State) :
    cut (rs, .resume f b is t, env, s) = false := rfl

/-- bump's selector. -/
def IsBump (call : Call) : Prop := EvmRules.Evm.shr 224 (calldataWord call 0) = 0xb20eb4c4

/-- What bump's spec asks of an end: when it succeeds, slot 0 (`count`) holds its old value plus
the argument `n`, the sum did not wrap and is at most slot 1 (`limit`), and every other slot is
unchanged. -/
def Post (call : Call) (r : Halt × State) : Prop :=
  (r.1 = .stop ∨ ∃ d, r.1 = .ret d) →
    r.2.storage 0 = (State.initial call).storage 0 + calldataWord call 4 ∧
    (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4 ∧
    (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1 ∧
    ∀ k, k ≠ 0 → r.2.storage k = (State.initial call).storage k

def Inv (call : Call) (x : MIR.Lowered.Frame) : Prop :=
  (∃ env s, x = ([], .enter 4 7 1, env, s) ∧ s.storage = (State.initial call).storage ∧
      env 62 = calldataWord call 4 ∧ env 2 = (State.initial call).storage 0 ∧
      (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4 ∧
      (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) ∨
  (∃ env s, x = ([], .enter 4 10 1, env, s) ∧ s.storage = (State.initial call).storage ∧
      env 62 = calldataWord call 4 ∧ env 20 ≤ calldataWord call 4 ∧
      env 43 = (State.initial call).storage 0 + env 20 ∧
      (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4 ∧
      (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1)

/-- The cut test of a block a branch picks, distributed over the branch. -/
theorem ite_beq' {α : Type} [BEq α] (c : Prop) [Decidable c] (a b n : α) :
    ((if c then a else b) == n) = (if c then a == n else b == n) := by
  split <;> rfl

/-- A cut test of a block a branch picks evaluates on both branches before any case split. -/
macro "cut_test" : tactic => `(tactic|
  simp only [ite_beq', Nat.reduceBEq, ite_self, Bool.false_eq_true, ↓reduceIte, true_or, or_true])

/-- `seg_norm` with the cut test of a branch evaluated first. -/
syntax "bump_norm" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| bump_norm [$ids,*]) =>
    `(tactic| repeat (first | sym_eval | seg_eval [$ids,*] | cut_test | sym_cond))

macro "word_goal" : tactic => `(tactic| (
  first
    | rfl
    | (intro k hk; simp only [update, hk, ↓reduceIte])
    | (simp only [update, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff, EvmRules.Evm.add, *]; done)
    | (simp only [update, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff, EvmRules.Evm.add, *]; bv_omega)
    | bv_omega))

macro "hoare_leaf" : tactic => `(tactic| (
  first
    | exact True.intro
    | (unfold Post; dsimp only; intro h; rcases h with h | ⟨_, h⟩ <;> exact Halt.noConfusion h)
    | (unfold Post; dsimp only; intro _; (try simp only [EvmRules.Evm.add] at *);
        refine ⟨?_, ?_, ?_, ?_⟩ <;> word_goal)
    | (unfold Inv; left; (try simp only [EvmRules.Evm.add] at *);
        refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> word_goal)
    | (unfold Inv; right; (try simp only [EvmRules.Evm.add] at *);
        refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> word_goal)
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)))

syntax "hoare_seg" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| hoare_seg) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      bump_norm [SegOk, cut_enter, cut_resume]
      repeat' (split_cond <;> bump_norm [SegOk, cut_enter, cut_resume])
      all_goals hoare_leaf))

set_option maxHeartbeats 2000000 in
theorem seg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ k, SegOk (Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  refine ⟨40, ?_⟩
  unfold IsBump at hsel
  hoare_seg

set_option maxHeartbeats 2000000 in
theorem seg1 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (hst : s.storage = (State.initial call).storage) (h62 : env 62 = calldataWord call 4)
    (h2 : env 2 = (State.initial call).storage 0)
    (hov : (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4)
    (hlim : (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) :
    ∃ k, SegOk (Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 7 1, env, s)) := by
  refine ⟨40, ?_⟩
  hoare_seg

set_option maxHeartbeats 2000000 in
theorem seg2 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (hst : s.storage = (State.initial call).storage) (h62 : env 62 = calldataWord call 4)
    (h20 : env 20 ≤ calldataWord call 4) (h43 : env 43 = (State.initial call).storage 0 + env 20)
    (hov : (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4)
    (hlim : (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) :
    ∃ k, SegOk (Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 10 1, env, s)) := by
  refine ⟨40, ?_⟩
  hoare_seg

/-- **bump's spec of solar's first lowered MIR, on every call of bump, whatever number of times
its loop runs**: every end of stage0 on a call with bump's selector meets \`Post\`. -/
theorem stage0_post (o : Oracle) (call : Call) (hsel : IsBump call) (r : Halt × State)
    (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : Post call r := by
  obtain ⟨n, hn⟩ := e
  change Machine.iterate _ n _ = some r at hn
  rw [CutPoint.iterate_eq] at hn
  refine CutPoint.post_of_start (seg0 o call hsel) ?_ n r hn
  rintro x (⟨env, s, rfl, hst, h62, h2, hov, hlim⟩ | ⟨env, s, rfl, hst, h62, h20, h43, hov, hlim⟩)
  · exact seg1 o call env s hst h62 h2 hov hlim
  · exact seg2 o call env s hst h62 h20 h43 hov hlim

/-- \`Post\` is read off what an observer sees: it holds of an end that agrees with one it holds
of. -/
theorem Post.of_agree {call : Call} {r r' : Halt × State} (ag : Agree r r') (h : Post call r) :
    Post call r' := by
  obtain ⟨a, s⟩ := r
  obtain ⟨b, t⟩ := r'
  intro hb
  have : (a = .stop ∨ ∃ d, a = .ret d) ∧ s.storage = t.storage := by
    rcases hb with rfl | ⟨d, rfl⟩ <;> cases a <;> simp_all [Agree]
  obtain ⟨ha, hst⟩ := this
  simpa [← hst] using h ha

/-- bump's spec carried along any program whose every end is matched by an agreeing end of
stage0 (\`Certified … p stage0\`). -/
theorem post_of_certified {L : Layer} {p : L.Prog} (o : Oracle)
    (cert : Certified L MIR.Lowered.moduleLayer o p stage0 anyCall) (call : Call)
    (hsel : IsBump call) (r : Halt × State) (e : L.Ends o p call r) : Post call r := by
  obtain ⟨r0, e0, ag⟩ := cert call trivial r e
  exact (stage0_post o call hsel r0 e0).of_agree (CutPoint.Agree.symm ag)

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.post_of_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_of_certified

/-! ## Every call of bump ends

The same cut point with what the loop keeps in memory (the cached `count` at 128, the flag that
`count` was written at 160) and the slot-0 read the compiler's facts compare, so no fact fails
and no segment is stuck, and the rank `n - i` (`n + 1` on the loop's entry), which each
iteration lowers. -/

theorem load_store_apart (m : Mem) (offset address : Nat) (value : EvmRules.Word)
    (apart : address + 32 ≤ offset ∨ offset + 32 ≤ address) :
    (m.store offset value).load address = m.load address := by
  unfold Mem.store
  rw [Mem.load_expand]
  unfold Mem.load Mem.read
  congr 1
  apply List.map_congr_left
  intro i mem
  simp only [List.mem_range] at mem
  have : ¬(offset ≤ address + i ∧ address + i < offset + 32) := by omega
  simp only [this, ↓reduceIte]

theorem load_128_store_160 (m : Mem) (w : EvmRules.Word) : (m.store 160 w).load 128 = m.load 128 :=
  load_store_apart _ _ _ _ (by decide)

def InvT (call : Call) (x : MIR.Lowered.Frame) : Prop :=
  (∃ env s, x = ([], .enter 4 7 1, env, s) ∧ s.storage = (State.initial call).storage ∧
      env 62 = calldataWord call 4 ∧ env 2 = (State.initial call).storage 0 ∧
      env 30 = (State.initial call).storage 0 ∧ s.memory.load 128 = env 2 ∧
      s.memory.load 160 = 0 ∧
      (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4 ∧
      (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) ∨
  (∃ env s, x = ([], .enter 4 10 1, env, s) ∧ s.storage = (State.initial call).storage ∧
      env 62 = calldataWord call 4 ∧ env 30 = (State.initial call).storage 0 ∧
      env 20 ≤ calldataWord call 4 ∧ env 43 = (State.initial call).storage 0 + env 20 ∧
      s.memory.load 128 = env 43 ∧ s.memory.load 160 = 1 ∧
      (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4 ∧
      (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1)

/-- The loop's variant, `n - i`, as the decreases clause says, and `n + 1` on the loop's entry. -/
def rank (call : Call) : MIR.Lowered.Frame → Nat
  | (_, .enter _ p _, env, _) =>
    if p = 7 then (calldataWord call 4).toNat + 1 else (calldataWord call 4).toNat - (env 20).toNat
  | _ => 0

macro "mem_goal" : tactic => `(tactic| (
  first
    | (simp only [load_128_store_160, Mem.load_store_same, Mem.load_expand,
        MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff, EvmRules.Evm.add, *]; done)
    | word_goal))

macro "rank_goal" : tactic => `(tactic| (
  simp only [rank, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff, EvmRules.Evm.add, *] <;> bv_omega))

macro "total_leaf" : tactic => `(tactic| (
  first
    | (unfold Post; dsimp only; intro h; rcases h with h | ⟨_, h⟩ <;> exact Halt.noConfusion h)
    | (unfold Post; dsimp only; intro _; (try simp only [EvmRules.Evm.add] at *);
        refine ⟨?_, ?_, ?_, ?_⟩ <;> word_goal)
    | (refine ⟨?_, ?_⟩
       · unfold InvT; left; (try simp only [EvmRules.Evm.add] at *)
         refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mem_goal
       · first | exact True.intro | rank_goal)
    | (refine ⟨?_, ?_⟩
       · unfold InvT; right; (try simp only [EvmRules.Evm.add] at *)
         refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mem_goal
       · first | exact True.intro | rank_goal)
    | (unfold InvT; left; (try simp only [EvmRules.Evm.add] at *)
       refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mem_goal)
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)))

syntax "total_seg" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| total_seg) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      bump_norm [SegEnds, cut_enter, cut_resume]
      repeat' (split_cond <;> bump_norm [SegEnds, cut_enter, cut_resume])
      all_goals total_leaf))

open SolarTV.CutPoint (SegEnds) in
set_option maxHeartbeats 2000000 in
theorem tseg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ k, SegEnds (InvT call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  refine ⟨40, ?_⟩
  unfold IsBump at hsel
  total_seg

open SolarTV.CutPoint (SegEnds) in
set_option maxHeartbeats 2000000 in
theorem tseg1 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (hst : s.storage = (State.initial call).storage) (h62 : env 62 = calldataWord call 4)
    (h2 : env 2 = (State.initial call).storage 0) (h30 : env 30 = (State.initial call).storage 0)
    (hm128 : s.memory.load 128 = env 2) (hm160 : s.memory.load 160 = 0)
    (hov : (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4)
    (hlim : (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) :
    ∃ k, SegEnds (InvT call) (Post call) (fun y => rank call y < (calldataWord call 4).toNat + 1)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 7 1, env, s)) := by
  refine ⟨40, ?_⟩
  total_seg

open SolarTV.CutPoint (SegEnds) in
set_option maxHeartbeats 2000000 in
theorem tseg2 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (hst : s.storage = (State.initial call).storage) (h62 : env 62 = calldataWord call 4)
    (h30 : env 30 = (State.initial call).storage 0)
    (h20 : env 20 ≤ calldataWord call 4) (h43 : env 43 = (State.initial call).storage 0 + env 20)
    (hm128 : s.memory.load 128 = env 43) (hm160 : s.memory.load 160 = 1)
    (hov : (State.initial call).storage 0 ≤ (State.initial call).storage 0 + calldataWord call 4)
    (hlim : (State.initial call).storage 0 + calldataWord call 4 ≤ (State.initial call).storage 1) :
    ∃ k, SegEnds (InvT call) (Post call)
      (fun y => rank call y < (calldataWord call 4).toNat - (env 20).toNat)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 10 1, env, s)) := by
  refine ⟨40, ?_⟩
  total_seg

/-- **Every call of bump ends on solar's first lowered MIR, and meets bump's spec**, whatever
`n` is: the loop runs `n` times. -/
theorem stage0_ends (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ r, MIR.Lowered.moduleLayer.Ends o stage0 call r ∧ Post call r := by
  obtain ⟨n, r, ran, post⟩ := CutPoint.ends_of_start (rank call) (tseg0 o call hsel) (by
    rintro x (⟨env, s, rfl, hst, h62, h2, h30, hm128, hm160, hov, hlim⟩ |
      ⟨env, s, rfl, hst, h62, h30, h20, h43, hm128, hm160, hov, hlim⟩)
    · exact tseg1 o call env s hst h62 h2 h30 hm128 hm160 hov hlim
    · exact tseg2 o call env s hst h62 h30 h20 h43 hm128 hm160 hov hlim)
  refine ⟨r, ⟨n, ?_⟩, post⟩
  change Machine.iterate _ n _ = some r
  rw [CutPoint.iterate_eq]
  exact ran

/-- bump's spec carried forward along any program whose ends match stage0's
(`Certified … stage0 p`): every call of bump ends there too, and meets the spec. -/
theorem ends_of_certified {L : Layer} {p : L.Prog} (o : Oracle)
    (cert : Certified MIR.Lowered.moduleLayer L o stage0 p anyCall) (call : Call)
    (hsel : IsBump call) : ∃ r, L.Ends o p call r ∧ Post call r := by
  obtain ⟨r0, e0, post⟩ := stage0_ends o call hsel
  obtain ⟨r, e, ag⟩ := cert call trivial r0 e0
  exact ⟨r, e, post.of_agree ag⟩

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.ends_of_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ends_of_certified

end SolarTV.Milestone.VerifyCounter.Bump
