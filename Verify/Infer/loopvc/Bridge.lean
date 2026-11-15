import Verify.Obligation
import SolidCore.Refinement.Generic.Loop

/-!
# From a loop cut's certificate to SolidCore's loop rule

`loopcert.py gen` proves, for a function with one loop, `obligations_valid`: every required
obligation of the function's loop cut (initiation on the entry edge, preservation and the rank's fall
on the back edge, the path obligations on the exit edge) is `Obligation.Valid`, each by `vc_smt`
and each an instance of one of the cut's templates at the run's candidate (`tK_exact`, by `rfl`).
That is a fact about solar-verify's encoding of the function. This file says what it gives about the
function's code once the encoding is bound to it, the way `Binds` (Verify/VC/Obligations.lean) binds
a loop-free function's obligations to its erased tree:

* `ForBinds obs ...` / `WhileBinds obs ...`: the per-loop binding. When the obligations `obs` are
  valid, an invariant `Inv` and a rank `rank` of SolidCore's runtime at the loop's header (the
  candidate's conjuncts and `decreases` read at the runtime) form a ranking certificate of the loop
  (`ForCert` / `WhileCert` of SolidCore/Refinement/Generic/Loop.lean) ending in `Q`.
* `forLoop_of_cut` / `whileLoop_of_cut`: a binding and valid obligations give the loop's end in
  SolidCore's interpreter, at every fuel from the certificate's bound, in a result meeting `Q`.

What is not here: a proof of `ForBinds` / `WhileBinds` from solar-verify's encoding for every loop.
Like `Binds`, it is one proof per function, about the loop's body (which is loop-free, so the
generic stage's erasure and `eval_stmt` cover its statements) and the cut's parameters; the certify
driver does not generate it yet. Until it does, a loop's certificate is a checked fact about the
encoding, and the source-to-bytecode theorem for a function with a loop needs that function's
binding (for verify_counter's `bump`, the hand-written `SourceLoop.cert` of Contracts/VerifyCounter).
-/

namespace SolarVerify.LoopCert

open SolarVerify.Vc
open SolidCore.Solidity.Source SolidCore.Refinement.Generic.Loop

/-- Every obligation of `obs` is valid: the statement `obligations_valid` of a generated loop
certificate proves for the cut's required obligations. -/
def AllValid (obs : List Obligation) : Prop := ∀ o ∈ obs, Obligation.Valid o

/-- The binding of a loop cut's obligations to a SolidCore `for` loop: valid obligations make
`Inv` and `rank` a ranking certificate of `for (; cond; post) body` ending in `Q`. -/
def ForBinds (obs : List Obligation) (k : Nat) (tbl : FunctionTable) (ctx : Context) (cond : Expr)
    (post body : Stmt) (Inv : Runtime → Prop) (rank : Runtime → Nat) (Q : Result → Prop) : Prop :=
  AllValid obs → ForCert k tbl ctx cond post body Inv rank Q

/-- The binding of a loop cut's obligations to a SolidCore `while` loop. -/
def WhileBinds (obs : List Obligation) (k : Nat) (tbl : FunctionTable) (ctx : Context)
    (cond : Expr) (body : Stmt) (Inv : Runtime → Prop) (rank : Runtime → Nat)
    (Q : Result → Prop) : Prop :=
  AllValid obs → WhileCert k tbl ctx cond body Inv rank Q

/-- **A bound loop cut whose obligations are valid ends the `for` loop in `Q`.** -/
theorem forLoop_of_cut {obs : List Obligation} {k k0 : Nat} {tbl : FunctionTable} {ctx : Context}
    {init : Stmt} {cond : Expr} {post body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat}
    {Q : Result → Prop} (hb : ForBinds obs k tbl ctx cond post body Inv rank Q)
    (hv : AllValid obs) {rt rt1 : Runtime}
    (hinit : Stmt.eval k0 tbl ctx rt.pushScope init = .done (.ok (.normal rt1))) (hinv : Inv rt1)
    (fuel : Nat) (hf : rank rt1 + 1 + k + 1 ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel tbl ctx rt (.forLoop init cond post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) ∧ Q r :=
  forLoop_of_cert (hb hv) hinit hinv fuel hf hk0

/-- **A bound loop cut whose obligations are valid ends the `while` loop in `Q`.** -/
theorem whileLoop_of_cut {obs : List Obligation} {k : Nat} {tbl : FunctionTable} {ctx : Context}
    {cond : Expr} {body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat} {Q : Result → Prop}
    (hb : WhileBinds obs k tbl ctx cond body Inv rank Q) (hv : AllValid obs) {rt : Runtime}
    (hinv : Inv rt) (fuel : Nat) (hf : rank rt + 1 + k + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel tbl ctx rt (.whileLoop cond body) = .done (.ok r) ∧ Q r :=
  whileLoop_of_cert (hb hv) hinv fuel hf

/-- info: 'SolarVerify.LoopCert.forLoop_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forLoop_of_cut

/-- info: 'SolarVerify.LoopCert.whileLoop_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whileLoop_of_cut

end SolarVerify.LoopCert
