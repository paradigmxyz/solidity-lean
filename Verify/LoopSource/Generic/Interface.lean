import Verify.LoopSource.Proof.LoopErased
import Verify.LoopSource.LoopMap

/-!
# The loop record and its per-iteration step: what the loop route exports to the gas lane

A loop's **record** is what its obligations (`ForObl` / `WhileObl`, `Proof/LoopErased.lean`) are
stated over: the header `H` (a symbolic state whose fresh words are what the loop changes), the
invariant `P` and measure `m` of header valuations, the erased condition `c` and the body's tree
`bb`. Solar's loop-head manifest names the header's words (`LoopMap`, `LoopMap.lean`). The
record carries no proof; a loop's obligations are a separate proposition over it (`Obl`).

The **step** is one iteration at the header: from a valuation of the invariant where the condition
holds, to one of the invariant with a smaller measure. `ForObl.iter` gives a step for every
iteration that ends normally (`step_of_back`). The gas lane needs two consequences, which are
proved here: no chain of steps from `σ0` is longer than `m σ0` (`steps_le`), and the source loop ends
at every statement fuel from `fuelBound σ0 k` on (`forLoop_of_erased`).
-/

namespace Verify.LoopSource.Interface
open SolidCore.Solidity.Source SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop

/-- **A loop's record**: header, invariant, measure, erased condition and body tree. -/
structure LoopRecord where
  H : SymState
  P : Val → Prop
  m : Val → Nat
  c : WExpr
  bb : Br

namespace LoopRecord

/-- **The obligations of `for (init; cnd; post) body` over the record**, at body fuel `k` and
exit condition `Q`. -/
def Obl (L : LoopRecord) (k : Nat) (E : EraseEnv) (ctx : Context) (cnd : Expr) (post body : Stmt)
    (Q : Result → Prop) : Prop :=
  ForObl k E ctx cnd post body L.H L.P L.m Q L.c L.bb

/-- **One iteration at the header**: `σ` of the invariant with the condition nonzero, to `σ'` of
the invariant with a smaller measure. -/
def Step (L : LoopRecord) (σ σ' : Val) : Prop :=
  L.P σ ∧ L.c.eval σ ≠ 0 ∧ L.P σ' ∧ L.m σ' < L.m σ

/-- `n` iterations from `σ`. -/
inductive Steps (L : LoopRecord) : Nat → Val → Prop
  | done (σ : Val) : Steps L 0 σ
  | step {σ σ' : Val} {n : Nat} : L.Step σ σ' → Steps L n σ' → Steps L (n + 1) σ

/-- **No chain of iterations from `σ` is longer than its measure.** -/
theorem steps_le {L : LoopRecord} {n : Nat} {σ : Val} (h : L.Steps n σ) : n ≤ L.m σ := by
  induction h with
  | done => exact Nat.zero_le _
  | step hs _ ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih hs.2.2.2)

/-- The statement fuel from which the loop ends, from entry valuation `σ0` at body fuel `k`. -/
def fuelBound (L : LoopRecord) (σ0 : Val) (k : Nat) : Nat := L.m σ0 + k + 2

/-- **An iteration that ends normally is a step**: every runtime its leaf's state shows at `σ` is
one the header shows at the step's target. -/
theorem step_of_back {L : LoopRecord} {E : EraseEnv} {ctx : Context} {σ : Val} {S : SymState}
    (hp : L.P σ) (hc : L.c.eval σ ≠ 0) (h : Back E ctx L.H L.P L.m σ S) :
    ∃ σ', L.Step σ σ' ∧ ∀ rt, StmtRel σ E ctx rt S → StmtRel σ' E ctx rt L.H := by
  obtain ⟨σ', hp', hm, hrel⟩ := h
  exact ⟨σ', ⟨hp, hc, hp', hm⟩, hrel⟩

/-- **The loop ends from `fuelBound` on**: `forLoop_of_erased` over the record. -/
theorem forLoop_ends {L : LoopRecord} {k k0 : Nat} {E : EraseEnv} {ctx : Context} {init : Stmt}
    {cnd : Expr} {post body : Stmt} {Q : Result → Prop} (h : L.Obl k E ctx cnd post body Q)
    {rt rt1 : Runtime} (hinit : Stmt.eval k0 E.tbl ctx rt.pushScope init = .done (.ok (.normal rt1)))
    {σ0 : Val} (hp0 : L.P σ0) (hrel0 : StmtRel σ0 E ctx rt1 L.H) (fuel : Nat)
    (hf : L.fuelBound σ0 k ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel E.tbl ctx rt (.forLoop init cnd post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) ∧ Q r :=
  forLoop_of_erased h hinit hp0 hrel0 fuel hf hk0

end LoopRecord
end Verify.LoopSource.Interface

/-- info: 'Verify.LoopSource.Interface.LoopRecord.steps_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Interface.LoopRecord.steps_le

/-- info: 'Verify.LoopSource.Interface.LoopRecord.forLoop_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Interface.LoopRecord.forLoop_ends
