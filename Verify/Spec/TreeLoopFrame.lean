import Verify.Spec.TreeLoop

/-!
# The loop route's statement in its named frame

`TreeLoop.onTree_ctxOfCall` gives the loop route's allowed statuses and postcondition at
`Shapes.ctxOfCall`, the context the backend stage gives a call: sender `0x2000`, the call's value,
timestamp 1, self `0x1000`. On calls without a value that is the one context `TreeLoop.ctx0`.
`certified_ctx0` restates a `Shapes.Certified` with the exported spec at `ctxOfCall` as the same
statement at the constant context `fun _ => ctx0`, for valid calls that carry no value, so a
published statement can name the fixed frame it holds in rather than leave it inside `ctxOfCall`.
Nothing here names a contract.
-/

namespace SolidCore.Spec.TreeLoop

open SolarTV SolidCore.Refinement
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep)

/-- A call without a value has the context `ctx0`. -/
theorem ctxOfCall_of_value {call : Call} (h : call.callvalue = 0) : ctxOfCall call = ctx0 := by
  simp [ctxOfCall, ctx0, h]

/-- **The exported spec at `ctxOfCall` is the exported spec in the fixed frame `ctx0`** on valid
calls without a value. -/
theorem certified_ctx0 {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} {b : Bundle} (hv : ∀ call, Valid call → call.callvalue = 0)
    (h : Shapes.Certified S p code Valid (bundleAllowed b ctxOfCall) (bundlePost b ctxOfCall idStep) G) :
    Shapes.Certified S p code Valid (bundleAllowed b fun _ => ctx0) (bundlePost b (fun _ => ctx0) idStep)
      G where
  inhabited := h.inhabited
  equiv := h.equiv
  terminates call hc := by
    obtain ⟨obs, hr, ha⟩ := h.terminates call hc
    have e := ctxOfCall_of_value (hv call hc)
    exact ⟨obs, hr, by simpa only [bundleAllowed, e] using ha⟩
  meets call hc obs hr := by
    have e := ctxOfCall_of_value (hv call hc)
    have hm := h.meets call hc obs hr
    simpa only [bundlePost, e] using hm
  resources := h.resources

end SolidCore.Spec.TreeLoop

/-- info: 'SolidCore.Spec.TreeLoop.certified_ctx0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.certified_ctx0
