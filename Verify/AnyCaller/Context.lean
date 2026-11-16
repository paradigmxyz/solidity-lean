import Verify.Spec.Contract
import SolidCore.Refinement.Generic.StageFrom

/-!
# The spec's call context for every caller

`Shapes.ctxOfCall` (Verify/ShapeSpecExport.lean) is the interface's one frame: sender `0x2000`. Here
`ctxOfCallFrom a` is the same frame sent by the account `a`, so a spec that reads `msg.sender` is
read in the context of the call's own sender, and `HoldsFrom` asks solar-verify's exported spec of
SolidCore's run sent by every account `a < 2 ^ 160` other than the contract (`solidCoreFrom a`),
each in its own context. At `callerAddress` the context is `ctxOfCall`'s literal
(`ctxOfCallFrom_callerAddress`).
-/

namespace SolidCore.Verify.AnyCaller

open SolarTV SolidCore.Refinement SolidCore.Spec

/-- The call context of a call sent by `a`: the interface's frame (the contract at `0x1000`, block
timestamp 1) with the call's sender and value. -/
def ctxOfCallFrom (a : Nat) (call : Call) : Ctx :=
  { sender := a, value := call.callvalue, timestamp := 1, self := 0x1000 }

theorem ctxOfCallFrom_sender (a : Nat) (call : Call) : (ctxOfCallFrom a call).sender = a := rfl

theorem ctxOfCallFrom_value (a : Nat) (call : Call) :
    (ctxOfCallFrom a call).value = call.callvalue := rfl

/-- At `callerAddress` it is `Shapes.ctxOfCall`'s frame. -/
theorem ctxOfCallFrom_callerAddress (call : Call) :
    ctxOfCallFrom callerAddress call =
      { sender := 0x2000, value := call.callvalue, timestamp := 1, self := 0x1000 } := rfl

/-- Two callers never share a context: a spec reading `msg.sender` tells them apart. -/
theorem ctxOfCallFrom_injective {a b : Nat} (call : Call)
    (h : ctxOfCallFrom a call = ctxOfCallFrom b call) : a = b := by
  have := congrArg Ctx.sender h
  simpa [ctxOfCallFrom] using this

/-- **The exported spec holds from every caller**, each call read in its own sender's context. -/
def HoldsFrom (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (scope : Call → Prop) (b : Bundle) (step : GhostStep) : Prop :=
  ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
    Holds (solidCoreFrom a fuel) c scope b (ctxOfCallFrom a) step

/-- A stage per caller carries `HoldsFrom` to the target, caller by caller. -/
theorem HoldsFrom.of_stage {T : Nat → Sem} {q : ∀ a, (T a).Prog} {fuel : Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {scope : Call → Prop} {b : Bundle}
    {step : GhostStep} (h : HoldsFrom fuel c scope b step)
    (st : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → Stage (solidCoreFrom a fuel) (T a) c (q a) scope) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress → Holds (T a) (q a) scope b (ctxOfCallFrom a) step :=
  fun a ha hne fs hfs => HoldsFn.of_stage (h a ha hne fs hfs) (st a ha hne)

end SolidCore.Verify.AnyCaller
