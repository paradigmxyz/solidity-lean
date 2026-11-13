import Contracts.VerifyCounter.Bump

/-!
# solar-verify's Counter on its first lowered MIR: every function

`Bump` proves bump's loop. This file proves the other functions of
`crates/verify/examples/Counter.sol` on the same module, `stage0` (solar's first lowered MIR),
each on every call of its selector, through the same cut point (which their runs never reach):

* `value_post`: a call with value does not succeed (nothing is payable);
* `count_post`, `limit_post`: the getters return slot 0 and slot 1 and leave the storage;
* `increment_post`: `increment` writes slot 0 plus one, which does not wrap;
* `max_post`: `max(a, b)` returns the larger argument and leaves the storage.

Each is partial correctness at every fuel (`CutPoint.post_of_start`), from one symbolic
evaluation of the module from its entry. No sorry, native_decide or bv_decide.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegOk)

/-- An end that succeeds: a stop or a return. -/
def Succ (r : Halt × State) : Prop := r.1 = .stop ∨ ∃ d, r.1 = .ret d

def PostValue (r : Halt × State) : Prop := ¬Succ r

def PostCount (call : Call) (r : Halt × State) : Prop :=
  Succ r → r.2.storage = (State.initial call).storage ∧
    ∃ m : Mem, r.1 = .ret ((m.store 0 ((State.initial call).storage 0)).read 0 32)

def PostLimit (call : Call) (r : Halt × State) : Prop :=
  Succ r → r.2.storage = (State.initial call).storage ∧
    ∃ m : Mem, r.1 = .ret ((m.store 0 ((State.initial call).storage 1)).read 0 32)

def PostIncrement (call : Call) (r : Halt × State) : Prop :=
  Succ r → r.2.storage = update (State.initial call).storage 0 ((State.initial call).storage 0 + 1) ∧
    (State.initial call).storage 0 + 1 ≠ 0

def PostMax (call : Call) (r : Halt × State) : Prop :=
  Succ r → r.2.storage = (State.initial call).storage ∧
    ∃ m : Mem, r.1 = .ret ((m.store 0
      (if calldataWord call 4 < calldataWord call 36 then calldataWord call 36 else calldataWord call 4)).read 0 32)

macro "fn_leaf" : tactic => `(tactic| (
  (try unfold PostValue at *); (try unfold PostCount); (try unfold PostLimit); (try unfold PostIncrement);
  (try unfold PostMax); (try unfold Succ); dsimp only
  first
    | exact True.intro
    | (intro h; rcases h with h | ⟨_, h⟩ <;> exact Halt.noConfusion h)
    | (intro _; exact ⟨rfl, _, rfl⟩)
    | (intro _; refine ⟨rfl, ?_⟩; first | (rw [if_pos (by bv_omega)]; exact ⟨_, rfl⟩) | (rw [if_neg (by bv_omega)]; exact ⟨_, rfl⟩))
    | (intro _; refine ⟨rfl, ?_⟩; simp only [EvmRules.Evm.add] at *; bv_omega)
    | (intro _; refine ⟨rfl, ?_⟩; (try simp only [EvmRules.Evm.add] at *); intro h; apply_assumption; exact h.symm)
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)))

syntax "fn_seg" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fn_seg) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      bump_norm [SegOk, cut_enter, cut_resume]
      repeat' (split_cond <;> bump_norm [SegOk, cut_enter, cut_resume])
      all_goals fn_leaf))

/-- From the entry, with no cut point on the way, every end meets `Post`. -/
theorem post_of_entry {o : Oracle} {call : Call} {Post : Halt × State → Prop}
    (start : ∃ k, SegOk (fun _ => False) Post
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0,
        MIR.Lowered.Module.startState stage0 (State.initial call))))
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : Post r := by
  obtain ⟨n, hn⟩ := e
  change Machine.iterate _ n _ = some r at hn
  rw [CutPoint.iterate_eq] at hn
  exact CutPoint.post_of_start start (fun _ h => h.elim) n r hn

set_option maxHeartbeats 2000000 in
theorem value_post (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue ≠ 0)
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : PostValue r := by
  refine post_of_entry ⟨40, ?_⟩ r e
  fn_seg

set_option maxHeartbeats 2000000 in
theorem count_post (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0x06661abd)
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : PostCount call r := by
  refine post_of_entry ⟨40, ?_⟩ r e
  fn_seg

set_option maxHeartbeats 2000000 in
theorem limit_post (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xa4d66daf)
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : PostLimit call r := by
  refine post_of_entry ⟨40, ?_⟩ r e
  fn_seg

set_option maxHeartbeats 2000000 in
theorem increment_post (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xd09de08a)
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : PostIncrement call r := by
  refine post_of_entry ⟨40, ?_⟩ r e
  fn_seg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem max_post (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0x6d5433e6)
    (r : Halt × State) (e : MIR.Lowered.moduleLayer.Ends o stage0 call r) : PostMax call r := by
  refine post_of_entry ⟨40, ?_⟩ r e
  fn_seg

end SolarTV.Milestone.VerifyCounter.Bump
