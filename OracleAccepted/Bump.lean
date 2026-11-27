import Contracts.VerifyCounter.BumpTotal

/-!
# Oracle allow-list corollaries: `Bump`

The simplification pass changed or removed these declarations. The oracle
(/home/hand/simp/oracle/oracle.sh with the allow-list ACCEPTED.md) accepts each change
only because the new statement is at least as strong as the base's (550ff580). Each theorem below
restates a base statement verbatim, under the same name in a `Base` namespace, and
proves it from the declaration that replaced it, in one line. Nothing imports this module.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump.Base

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- Base `tseg0`: some fuel ends the first segment; the new `tseg0` names it (40). -/
theorem tseg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) :=
  ⟨40, _root_.SolarTV.Milestone.VerifyCounter.Bump.tseg0 o call hsel⟩

/-- Base `tseg7`, from the new fixed-fuel `tseg7`. -/
theorem tseg7 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at7 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 7 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 7 1, env, s)) :=
  ⟨40, _root_.SolarTV.Milestone.VerifyCounter.Bump.tseg7 o call env s h⟩

/-- Base `tseg10`, from the new fixed-fuel `tseg10`. -/
theorem tseg10 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 10 1, env, s)) :=
  ⟨40, _root_.SolarTV.Milestone.VerifyCounter.Bump.tseg10 o call env s h⟩

/-- Base `wseg0` (removed): the new `tseg0` is its statement with `start call` unfolded. -/
theorem wseg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    SegEnds (Inferred.Inv call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 (start call)) :=
  _root_.SolarTV.Milestone.VerifyCounter.Bump.tseg0 o call hsel

end SolarTV.Milestone.VerifyCounter.Bump.Base
