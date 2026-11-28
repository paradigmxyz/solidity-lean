import Verify.ShapeCtxGasFrom

/-!
# The gas edge from any caller, at a fuel per call

`gasEdge_ofXL` (Verify/ShapeCtxGasFrom.lean) takes one block count `N` for every valid call. Here
the count is a function of the call, `nOf call`, and the gas bound is `gasBoundL cx.base (nOf call)`
for that call: no count is shared across calls, so an unbounded family of calls (each ending
within its own count of blocks) gets a bound per call. The proof is `gasEdge_ofXL`'s, with
`forward_of_checkXLFrom` (which takes its count per call) at `nOf call`. `gasEdge_ofXL` is the
constant instance (`gasEdge_ofXL_eq`).
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Solar

/-- **The gas edge from any caller, at a fuel per call.** -/
theorem gasEdge_ofXL_at {q : Assemble.Program} {F : List Nat} {code : ByteArray}
    {cx : AssembleCtx.CtxCert} {Valid : Call → Prop} (nOf : Call → Nat)
    (asm : AssembleCtxGas.checkXL F q code cx = true) (hreads : cx.base.reads = false)
    (ends : ∀ o call, Valid call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call (nOf call)).isSome = true)
    (guard_run : ∀ o call, Valid call →
      EVM.Program.run o q call (nOf call) = EVM.Program.run o (AssembleCtxGas.guard F q) call (nOf call)) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ o, AssembleLoop.OracleOkAt a o → ∀ call, Valid call →
      ∀ gas, AssembleLoop.gasBoundL cx.base (nOf call) ≤ gas →
        ∃ obs, (evmirSem o).run q call = some obs ∧ Final.Target.runWithFrom a gas code call = some obs := by
  intro a ha hne o ho call hc gas hg
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ends o call hc)
  refine ⟨_, evmir_run_of_iterate ((guard_run o call hc).trans hr), ?_⟩
  exact AssembleCtxGas.forward_of_checkXLFrom asm a (Assemble.address_ne_self ha hne) o (fun _ => ho)
    (fun h => absurd h (by simp [hreads])) call (nOf call) r hr hg

/-- The fixed-count edge is the constant instance. -/
theorem gasEdge_ofXL_eq {q : Assemble.Program} {F : List Nat} {code : ByteArray}
    {cx : AssembleCtx.CtxCert} {N : Nat} {Valid : Call → Prop}
    (asm : AssembleCtxGas.checkXL F q code cx = true) (hreads : cx.base.reads = false)
    (ends : ∀ o call, Valid call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call N).isSome = true)
    (guard_run : ∀ o call, Valid call →
      EVM.Program.run o q call N = EVM.Program.run o (AssembleCtxGas.guard F q) call N) :
    gasEdge_ofXL (N := N) asm hreads ends guard_run = gasEdge_ofXL_at (fun _ => N) asm hreads ends guard_run :=
  rfl

/-- The message carries the gas unchanged: no truncation or wrap at any `gas : Nat`. -/
theorem messageFromWith_gas (a gas : Nat) (code : ByteArray) (call : Call) :
    (Target.messageFromWith a gas code call).gas = gas :=
  rfl

end SolidCore.Refinement.Shapes

/-- info: 'SolidCore.Refinement.Shapes.gasEdge_ofXL_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.gasEdge_ofXL_at
