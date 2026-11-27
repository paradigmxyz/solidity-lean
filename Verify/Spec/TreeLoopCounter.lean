import Verify.Spec.TreeLoopCheck
import SolidCore.Refinement.KernelRfl
import Verify.LoopSource.Equiv.EraseLoopCounterJoin
import verify_counter.gen.Counter.Spec
import verify_counter.gen.Counter.Manifest

/-!
# Counter.bump against solar-verify's exported spec, through the loop route

`bump(n)` of Certified/verify_counter/verify_counter.sol has a `for` loop, so the generic source
stage does not erase it and `holdsFn_of_tree` does not apply. This module states its whole
`Shapes.Certified` with the specification solar-verify exports for the contract
(`Certified.verify_counter.gen.Counter.Spec.Counter`: `bundleAllowed` and `bundlePost` at
`Shapes.ctxOfCall` and `Shapes.idStep`), through the loop erasure's tree:

* `bump_tree`: `brTree` of the loop erasure `EraseLoopCounter.bumpLoopBr` is `bumpTree`, the tree
  Lean printed (the kernel evaluates it);
* `bump_meets`: `bump`'s exported spec holds of that tree (`TreeMeets`, by `tree_meets`), no premise;
* `bump_loop_eq`, `bump_loopSpec`: the kernel's check of `bump`'s dispatch, widths and loop erasure,
  and that `B` is `Counter`'s export with `bump`'s spec at index 1 (`contractLoopCheck`, as
  spec_connect.py writes it; `bump_loop_renamed_eq` and `bump_loop_index0_eq`: a renamed bundle and
  the wrong index fail it) and, by `TreeLoop.loopSpec_of_check`, the loop
  route's source premises with `OnTree … Allowed` and `OnTree … Post` for the exported spec (the
  other two function specs, `increment` and `max`, have other selectors);
* `counter_join_spec`: for every `K ≤ Kmax`, `Shapes.Certified` of the source (statement fuel
  `2 ^ 256 + 8`) and the exact emitted runtime `SolarTV.Milestone.X.code` on the calls `bump(a)`,
  `a ≤ K`, with the exported spec as allowed statuses and postcondition, and the gas bound
  `K * 1414400 + 3536012`, from `bump_loopSpec` through `EraseLoopJoin.eraseLoop_certified_generated` (hence
  `eraseLoop_certified_loops`); the only premise is `K ≤ Kmax`;
* `spec_source`: the export's manifest names the file SolidCore's `Counter` was imported from, and
  the compile that emitted the bytecode names the same file with the same SHA-256;
* `post_nonvacuous`: the exported postcondition rejects a success of `bump(1)` that leaves
  `count` as it was, so `counter_join_spec` says something about `bump`;
* `bump_loop_noEnsures_eq`, `bump_loop_noInv_eq`: `contractLoopCheck` (`ExportedFor`) checks names
  and the selector only, so `B` with `bump`'s ensures or the contract invariant removed passes it;
  `noEnsures_ne`, `noInv_ne`: neither is `B`, so the check spec_connect.py writes of a generated
  module's bundle (`spec_is_fresh`: the spec module's bundle is the literal of that run's export of
  the source bytes) refuses both.

**What `counter_join_spec` covers, and what it does not.**

* **Fixed frame.** Every call is `bump(a)` with clean calldata, any storage, in the one context
  `Shapes.ctxOfCall` gives it (`TreeLoop.ctx0`): sender `0x2000`, value 0, timestamp 1, self
  `0x1000`. No other caller, value, block or address is covered.
* **Runtime only.** The source semantics is `stmtSem` on SolidCore's runtime dispatcher from the
  call's storage; deployment (the constructor) is outside the statement.
* **Pinned bytes.** The bytecode is `SolarTV.Milestone.X.code`, the runtime bytes pinned in the
  repository for this contract, not a fresh compile of this run.
* **Bounded calls.** Only arguments `a ≤ K` with `K ≤ Kmax` (`CounterGas.BumpCallBounded K`).
* **This contract's spec.** The specification is the bundle `B` solar-verify exported from
  Certified/verify_counter/verify_counter.sol, named in the statement, with `ExportedFor c B bumpSel`:
  `B` is named `Counter`, as the checked contract is, and its spec of `bump`'s selector is named
  `Counter.bump`. `succeedsIf := []` asks no call to succeed. That `B`'s clauses are the export
  of the source bytes is this module's narrower claim: it names the audited module `B` and checks
  the manifest (`spec_source`), not a fresh export; spec_connect.py's generated modules check that
  in the kernel (`spec_is_fresh`, `source_is_fresh`).
-/

namespace SolidCore.Spec.TreeLoopCounter

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity.Source
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Generic Verify.LoopSource.Equiv
open SolidCore.Spec.TreeLoop
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep)

/-- solar-verify's export of the contract's spec. -/
abbrev B : Bundle := Certified.verify_counter.gen.Counter.Spec.Counter

/-- `bump`'s exported spec. -/
def bump_spec : FnSpec := B.spec.specs[1]'(by decide)

/-- The tree of `bump`'s loop erasure, as Lean printed it. -/
def bumpTree : Tree :=
  (SolidCore.Refinement.Generic.Tree.ite (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.add) (SolidCore.Refinement.Generic.WExpr.init 0) (SolidCore.Refinement.Generic.WExpr.arg 0)) (SolidCore.Refinement.Generic.WExpr.init 0)) (SolidCore.Refinement.Generic.Tree.halt false [SolidCore.Refinement.Generic.OByte.lit 78, SolidCore.Refinement.Generic.OByte.lit 72, SolidCore.Refinement.Generic.OByte.lit 123, SolidCore.Refinement.Generic.OByte.lit 113, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 17] [] []) (SolidCore.Refinement.Generic.Tree.ite (SolidCore.Refinement.Generic.WExpr.un (SolidCore.Refinement.Generic.UnOp.iszero) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.gt) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.add) (SolidCore.Refinement.Generic.WExpr.init 0) (SolidCore.Refinement.Generic.WExpr.arg 0)) (SolidCore.Refinement.Generic.WExpr.init 1))) (SolidCore.Refinement.Generic.Tree.ite (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.add) (SolidCore.Refinement.Generic.WExpr.init 0) (SolidCore.Refinement.Generic.WExpr.sel (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.lit 0) (SolidCore.Refinement.Generic.WExpr.arg 0)) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.sub) (SolidCore.Refinement.Generic.WExpr.arg 0) (SolidCore.Refinement.Generic.WExpr.lit 0)) (SolidCore.Refinement.Generic.WExpr.lit 0))) (SolidCore.Refinement.Generic.WExpr.init 0)) (SolidCore.Refinement.Generic.Tree.halt false [SolidCore.Refinement.Generic.OByte.lit 78, SolidCore.Refinement.Generic.OByte.lit 72, SolidCore.Refinement.Generic.OByte.lit 123, SolidCore.Refinement.Generic.OByte.lit 113, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 17] [] []) (SolidCore.Refinement.Generic.Tree.ite (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.add) (SolidCore.Refinement.Generic.WExpr.lit 0) (SolidCore.Refinement.Generic.WExpr.sel (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.lit 0) (SolidCore.Refinement.Generic.WExpr.arg 0)) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.sub) (SolidCore.Refinement.Generic.WExpr.arg 0) (SolidCore.Refinement.Generic.WExpr.lit 0)) (SolidCore.Refinement.Generic.WExpr.lit 0))) (SolidCore.Refinement.Generic.WExpr.lit 0)) (SolidCore.Refinement.Generic.Tree.halt false [SolidCore.Refinement.Generic.OByte.lit 78, SolidCore.Refinement.Generic.OByte.lit 72, SolidCore.Refinement.Generic.OByte.lit 123, SolidCore.Refinement.Generic.OByte.lit 113, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 17] [] []) (SolidCore.Refinement.Generic.Tree.halt true [] [(SolidCore.Refinement.Generic.WExpr.lit 0, SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.add) (SolidCore.Refinement.Generic.WExpr.init 0) (SolidCore.Refinement.Generic.WExpr.sel (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.lt) (SolidCore.Refinement.Generic.WExpr.lit 0) (SolidCore.Refinement.Generic.WExpr.arg 0)) (SolidCore.Refinement.Generic.WExpr.bin (SolidCore.Refinement.Generic.BinOp.sub) (SolidCore.Refinement.Generic.WExpr.arg 0) (SolidCore.Refinement.Generic.WExpr.lit 0)) (SolidCore.Refinement.Generic.WExpr.lit 0)))] []))) (SolidCore.Refinement.Generic.Tree.halt false [SolidCore.Refinement.Generic.OByte.lit 8, SolidCore.Refinement.Generic.OByte.lit 195, SolidCore.Refinement.Generic.OByte.lit 121, SolidCore.Refinement.Generic.OByte.lit 160, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 32, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 4, SolidCore.Refinement.Generic.OByte.lit 111, SolidCore.Refinement.Generic.OByte.lit 118, SolidCore.Refinement.Generic.OByte.lit 101, SolidCore.Refinement.Generic.OByte.lit 114, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0, SolidCore.Refinement.Generic.OByte.lit 0] [] [])))

/-- **The loop erasure's tree is `bumpTree`.** -/
theorem bump_tree :
    brTree Contracts.VerifyCounter.Source.bumpFn (argFacts [256] 0) EraseLoopCounter.bumpLoopBr =
      some bumpTree := by
  decide +kernel

/-- **`bump`'s exported spec holds of its loop erasure's tree.** -/
theorem bump_meets : TreeMeets B bump_spec ctx0 1 bumpTree := by
  tree_meets [bumpTree, bump_spec, B, Certified.verify_counter.gen.Counter.Spec.Counter, ctx0, UnOp.eval]

/-- The kernel's check of `bump`'s dispatch, widths and loop erasure, and that `B` is `Counter`'s
export with `bump`'s spec at index 1 (spec_connect.py's `F_loop?`). -/
def bump_loop? : Bool :=
  contractLoopCheck Contracts.VerifyCounter.Source.contract? Contracts.VerifyCounter.Source.fuel
    Contracts.VerifyCounter.Source.bumpSel 1 [256] bumpTree B 1

kernel_rfl bump_loop_eq bump_loop? true using Contracts.VerifyCounter.Source.selector_eq

/-- The same check with a bundle that is not `Counter`'s (`B` renamed): refused. -/
def bump_loop_renamed? : Bool :=
  contractLoopCheck Contracts.VerifyCounter.Source.contract? Contracts.VerifyCounter.Source.fuel
    Contracts.VerifyCounter.Source.bumpSel 1 [256] bumpTree { B with spec := { B.spec with name := "Other" } } 1

kernel_rfl bump_loop_renamed_eq bump_loop_renamed? false using Contracts.VerifyCounter.Source.selector_eq

/-- The same check at index 0, `increment`'s spec, which is not of `bump`'s selector: refused. -/
def bump_loop_index0? : Bool :=
  contractLoopCheck Contracts.VerifyCounter.Source.contract? Contracts.VerifyCounter.Source.fuel
    Contracts.VerifyCounter.Source.bumpSel 1 [256] bumpTree B 0

kernel_rfl bump_loop_index0_eq bump_loop_index0? false using Contracts.VerifyCounter.Source.selector_eq

/-- **The loop route's source and spec premises for `bump`, with the exported spec**: SolidCore's
function of `bump`'s selector, its widths, its loop erasure to `bumpTree`, and the export's allowed
statuses and postcondition on that tree (the other two function specs, `increment` and `max`, have
other selectors). -/
theorem bump_loopSpec {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Contracts.VerifyCounter.Source.contract? = .ok c) :
    LoopSpec c Contracts.VerifyCounter.Source.fuel Contracts.VerifyCounter.Source.bumpSel [256] bumpTree B :=
  loopSpec_of_check hc bump_loop_eq (by decide)
    (meets_of_index (P := fun fs => TreeMeets B fs ctx0 1 bumpTree) 1 (by decide) (by decide) bump_meets)

open SolarTV.Export.Counter Verify.LoopSource.Equiv.CounterResources Verify.Gas.FixedFuel
  Verify.LoopSource.Equiv.EraseLoopJoin Contracts.VerifyCounter.Source Verify.LoopSource.MirLink
  SolidCore.Refinement.Solar in
/-- **Counter.bump, certified through the loop route with solar-verify's exported spec**: for every
`K ≤ Kmax`, the driver's whole `Shapes.Certified` of SolidCore's runtime of the source and the pinned
runtime bytes `SolarTV.Milestone.X.code` on the calls `bump(a)`, `a ≤ K`, in the fixed frame
(sender `0x2000`, value 0, timestamp 1, self `0x1000`), with the allowed statuses and postcondition
of `B`, `Counter`'s own export (`ExportedFor c B bumpSel`), and the gas bound
`K * 1414400 + 3536012`. Deployment is outside the statement. -/
theorem counter_join_spec {K : Nat} (hK : K ≤ Kmax) :
    ∃ c, contract? = .ok c ∧ ExportedFor c B bumpSel ∧
      Shapes.Certified stmtSem c SolarTV.Milestone.X.code
        (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (bundleAllowed B ctxOfCall)
        (bundlePost B ctxOfCall idStep) (fun _ => K * 1414400 + 3536012) := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨f, br, hf, hw, hret, hb, hT, -, hA, hP, hexp⟩ := bump_loopSpec hc
  obtain rfl : f = bumpFn := Option.some.inj (hf.symm.trans (shape_of hc).2.2)
  have hsame : ∀ ρ : Val, ρ.Ok → (bumpTree.eval ρ).obs = (CounterObl.T.eval ρ).obs :=
    fun ρ _ => congrArg Res.obs (Counter.tree_same bump_tree CounterObl.tree ρ)
  have hback : ∀ ρ : Val, ρ.Ok → (CounterObl.T.eval ρ).obs = (bumpTree.eval ρ).obs :=
    fun ρ hρ => (hsame ρ hρ).symm
  have h := eraseLoop_certified_generated Contracts.VerifyCounter.Source.fuel c bumpSel bumpFn [256]
    br bumpTree (by decide) hf hw hret hb hT Generated.Counter.cut .off stage0 CounterObl.le
    CounterObl.li CounterObl.leaves CounterObl.T CounterObl.I CounterObl.μ CounterObl.ss CounterObl.seqs
    CounterObl.valid hsame evm7 SolarTV.Milestone.X.code _ SolarTV.Milestone.X.cert
    SolarTV.Milestone.X.maxs (SolarTV.Milestone.X.counterLoop_mir_to_evmir Shapes.oracle)
    (fun _ _ => trivial) SolarTV.Milestone.X.check_ok
    (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (bundleAllowed B ctxOfCall)
    (bundlePost B ctxOfCall idStep)
    (fun call hv => by
      obtain ⟨σ, a, -, ha, rfl⟩ := hv
      exact ⟨σ, [a], args_one ha, rfl⟩)
    (Verify.LoopSource.Equiv.CounterGas.bounded_inhabited K)
    (onTree_of_eval hback hA) (onTree_of_eval hback hP) Counter.rec 2 2 3 K
    (fun call hv => Counter.loops Shapes.oracle hv) (G_lt hK)
  refine ⟨c, hc, hexp, ?_⟩
  have hG : (fun _ : Call => AssembleLoop.gasBoundL SolarTV.Milestone.X.cert (fixedFuel 2 2 3 K)) =
      fun _ => K * 1414400 + 3536012 := funext fun _ => G_eq K
  rw [← hG]
  exact h

/-- **The export, the source and the bytecode come from one file**: the export's manifest names the
file SolidCore's `Counter` was imported from (`SourceAst.importedSourceName`), and the compile that
emitted the stages names that file with the SHA-256 the export recorded. -/
theorem spec_source :
    Certified.verify_counter.gen.Counter.Spec.manifest.source =
        SolidCore.Refinement.Source.VerifyCounter.importedSourceName ∧
      SolarTV.Export.Counter.Manifest.sources =
        [(Certified.verify_counter.gen.Counter.Spec.manifest.source,
          Certified.verify_counter.gen.Counter.Spec.manifest.sourceSha256)] :=
  ⟨rfl, rfl⟩

/-- `B` with `bump`'s ensures removed. -/
def B_noEnsures : Bundle :=
  { B with spec := { B.spec with specs :=
      [B.spec.specs[0]'(by decide), { bump_spec with ensures := [] }, B.spec.specs[2]'(by decide)] } }

/-- `B` with the contract invariant removed. -/
def B_noInv : Bundle := { B with spec := { B.spec with invariants := [] } }

/-- The name and selector check with `bump`'s ensures removed. -/
def bump_loop_noEnsures? : Bool :=
  contractLoopCheck Contracts.VerifyCounter.Source.contract? Contracts.VerifyCounter.Source.fuel
    Contracts.VerifyCounter.Source.bumpSel 1 [256] bumpTree B_noEnsures 1

kernel_rfl bump_loop_noEnsures_eq bump_loop_noEnsures? true using Contracts.VerifyCounter.Source.selector_eq

/-- The name and selector check with the contract invariant removed. -/
def bump_loop_noInv? : Bool :=
  contractLoopCheck Contracts.VerifyCounter.Source.contract? Contracts.VerifyCounter.Source.fuel
    Contracts.VerifyCounter.Source.bumpSel 1 [256] bumpTree B_noInv 1

kernel_rfl bump_loop_noInv_eq bump_loop_noInv? true using Contracts.VerifyCounter.Source.selector_eq

/-- **Removing `bump`'s ensures gives another bundle**, so a freshness check `_ = B` (spec_connect.py's
`spec_is_fresh`, against the export's literal) refuses it. -/
theorem noEnsures_ne : B_noEnsures ≠ B := fun h =>
  absurd (congrArg (fun b : Bundle => b.spec.specs.map (·.ensures.length)) h) (by decide)

/-- **Removing the contract invariant gives another bundle**, refused the same way. -/
theorem noInv_ne : B_noInv ≠ B := fun h =>
  absurd (congrArg (fun b : Bundle => b.spec.invariants.length) h) (by decide)

open Verify.LoopSource.MirLink in
/-- **The exported postcondition is not trivial on the certified calls**: for every `K ≥ 1`, it
rejects a success of `bump(1)` from empty storage that leaves `count` at 0. -/
theorem post_nonvacuous {K : Nat} (hK : 1 ≤ K) :
    ∃ (call : Call) (obs : Observable), Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call ∧
      ¬ bundlePost B ctxOfCall idStep call obs := by
  refine ⟨bumpCall [] 1, ⟨true, [], [], fun _ => 0⟩, ⟨[], 1, hK, by decide, rfl⟩, fun h => ?_⟩
  have hpre : Pre B (B.spec.specs[1]'(by decide)) (ctxOfCall (bumpCall [] 1))
      ⟨slotValue [], Ghost.zero, 1⟩ (bumpCall [] 1) [1] := by
    refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
    · decide
    · exact SolidCore.Refinement.Shapes.selectorOf_calldata (by decide) [1] 0 []
    · have := SolidCore.Spec.words_calldata Contracts.VerifyCounter.Source.bumpSel (args := [1]) (by simp)
      simp only [bumpCall] at this ⊢
      rw [this]; decide
    · simp [ctxOfCall]
    · simp [Bundle.satAll, B, Certified.verify_counter.gen.Counter.Spec.Counter]
    · simp [Bundle.satAll, Bundle.sat, B, Certified.verify_counter.gen.Counter.Spec.Counter, eval,
        slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, slotValue]
  have := (h _ (List.getElem_mem _) _ _ hpre).1 rfl
  obtain ⟨rets, -, hens, -⟩ := this
  simp [Bundle.satAll, Bundle.sat, B, Certified.verify_counter.gen.Counter.Spec.Counter, eval,
    slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, slotValue] at hens

end SolidCore.Spec.TreeLoopCounter

/-- info: 'SolidCore.Spec.TreeLoopCounter.bump_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.bump_meets

/-- info: 'SolidCore.Spec.TreeLoopCounter.bump_loopSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.bump_loopSpec

/-- info: 'SolidCore.Spec.TreeLoopCounter.counter_join_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.counter_join_spec

/-- info: 'SolidCore.Spec.TreeLoopCounter.post_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.post_nonvacuous

/-- info: 'SolidCore.Spec.TreeLoopCounter.noEnsures_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.noEnsures_ne

/-- info: 'SolidCore.Spec.TreeLoopCounter.noInv_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.noInv_ne

/-- info: 'SolidCore.Spec.TreeLoopCounter.spec_source' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoopCounter.spec_source
