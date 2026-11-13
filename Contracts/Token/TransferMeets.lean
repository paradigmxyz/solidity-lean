import Verify.Spec.TreeMap
import Contracts.Token.VC.Transfer
import Contracts.Token.Spec.Export
import Contracts.Token.Spec.ExportWrong

/-!
# Token: `transfer`'s exported spec of its erased tree, by the generic mapping tactic

`transfer_meets` proves solar-verify's exported spec of `transfer` (`Spec/Export.lean`) of the
generic source stage's tree (`transferTree`) by `tree_meets_map` alone: no per-function proof
steps, no solver verdict. Its one hypothesis is `SlotsSeparated 0` (keccak256 separated on the
slots of `balanceOf[a]`), which `tree_meets_map` reads as `MapSlotsSeparated [0]`.

`wrong_not_meets` is the negative: the spec mutant of `scripts/verify/mutant/TokenSpecMut.sol`
(`balanceOf[to] == old(balanceOf[to]) + amount + 1`, `Spec/ExportWrong.lean`) does not hold of the
same tree, with no hypothesis: `transfer(1, 0)` from the empty storage succeeds and leaves
`balanceOf[1]` at 0.
-/

namespace SolidCore.Spec.TreeDemo.Token

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Token

abbrev spec : Bundle := SolidCore.Spec.Export.Token.Token
def transferSpec : FnSpec := spec.spec.specs[1]'(by decide)
def ctx : Ctx := { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 }

/-- The call context of every call: `ctx` with the call's value. -/
def ctxOf (call : SolarTV.Call) : Ctx := { ctx with value := call.callvalue }

set_option linter.unusedSimpArgs false in
/-- **`transfer`'s exported spec holds of its erased tree**, by `tree_meets_map`. -/
theorem transfer_meets (hsep : SlotsSeparated 0) :
    TreeMeetsFixed spec transferSpec ctx 2 transferTree := by
  have hsep' := (mapSlotsSeparated_singleton 0).2 hsep
  tree_meets_map [transferTree, transferSpec, SolidCore.Spec.TreeDemo.Token.spec,
    SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx] hsep'

/-- The mutant's spec of `transfer`. -/
def mutSpec : FnSpec := SolidCore.Spec.Export.TokenSpecMut.Token.spec.specs[1]'(by decide)

set_option linter.unusedSimpArgs false in
/-- **The spec mutant does not hold of the tree**: `transfer(1, 0)` from the empty storage
succeeds with `balanceOf[1]` still 0, and the mutant asks for 1. -/
theorem wrong_not_meets :
    ¬ TreeMeetsFixed SolidCore.Spec.Export.TokenSpecMut.Token mutSpec ctx 2 transferTree := by
  intro h
  have hp := h [1, 0] (fun _ => 0) [1, 0] ⟨fun _ => 0, Ghost.zero, 0⟩ rfl (by simp) (by simp)
    (by simp [mutSpec, SolidCore.Spec.Export.TokenSpecMut.Token, decodeWords, Ty.ofWord]) rfl
    (by simp [ctx]) (by simp [Bundle.satAll, mutSpec, SolidCore.Spec.Export.TokenSpecMut.Token])
    (by simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.TokenSpecMut.Token, eval, slotOf, mkEnv,
      Env.cur, Ghost.zero, BinOp.apply, Ty.ofBits])
  have hlt := solHash_lt'
  have hkec := keccak_solHash
  generalize solHash = H at hp hlt hkec
  simp only [transferTree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow, Nat.reduceMod, Nat.zero_mod,
    Nat.reduceLT, ite_mod_nat, ite_true, ite_false, Nat.lt_irrefl, Nat.not_lt_zero, decide_false,
    Nat.reduceAdd, Nat.reduceSub, Nat.zero_add, Nat.add_zero, ite_self, Nat.one_ne_zero, ite_false, Nat.reduceEqDiff, reduceIte] at hp
  obtain ⟨rets, -, hens, -⟩ := hp.1 rfl
  simp only [Bundle.satAll, Bundle.sat, mutSpec, SolidCore.Spec.Export.TokenSpecMut.Token,
    List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv, Env.cur, Env.bind, BinOp.apply, Ty.ofBits,
    toWord, ctx, List.getD_cons_zero, List.getD_cons_succ, hkec, ofProp_ne_zero, ite_true, ite_false,
    Nat.zero_div, Nat.zero_mod, Int.reduceMod, Int.reduceToNat] at hens
  have h2 := hens.2.1 (by decide)
  simp at h2

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_meets

/-- info: 'SolidCore.Spec.TreeDemo.Token.wrong_not_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_not_meets

end SolidCore.Spec.TreeDemo.Token
