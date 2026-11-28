import Verify.Spec.HashScope
import Contracts.Token.TransferMeets
import Contracts.Token.Spec.ExportCollide

/-!
# Token's `transfer` under keccak256 separation scoped to the call's footprint

The single-level instance of Verify/Spec/HashScope.lean: `transfer(to, amount)` touches `balanceOf`
(slot 0) at the caller and at `to`, so its premise is `ScopedSep (transferFootprint 0 caller to)`:
keccak256 injective and at least `2 ^ 128` on those two preimages, nothing about any other key.

* `collide_not_meets_scoped` (negative control): the collision spec of
  scripts/verify/keccak/TokenSpecCollide.sol (`balanceOf[to] == old(balanceOf[msg.sender]) + amount`,
  true only if the two slots coincide) fails on `transfer(1, 0)` under that call's premise.
* `transferFP_real`: that premise holds of the real keccak256 (kernel evaluation), so
  `collide_refuted` refutes the collision spec with no hypothesis left.

The legacy exported spec of Token's `transfer` (Spec/Export.lean) frames `balanceOf` at every other
address, which needs separation from every key; CERTIFICATION_TARGET.md (a1c3143) rules that frame
out, so it is not proved here under the scoped premise.
-/

namespace SolidCore.Spec.TreeDemo.Token

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Token

/-- The call's premise: keccak256 separated on `transfer`'s footprint, `balanceOf` (slot 0) of the
caller (`ctx`'s sender, `0x2000`) and of `to` (argument 0). Nothing about any other key. -/
abbrev TransferFP (args : List Nat) : Prop :=
  ScopedSep (transferFootprint 0 8192 (args.getD 0 0 % 2 ^ 160))

/-- The collision spec of `transfer`. -/
def collideSpec : FnSpec := SolidCore.Spec.Export.TokenSpecCollide.Token.spec.specs[1]'(by decide)

/-- The witness storage: the caller's balance is 5, every other slot 0. -/
def collideStore : Storage := fun k => if k = solHash 8192 0 then 5 else 0

set_option linter.unusedSimpArgs false in
/-- **A spec that needs a collision is refuted under the scoped premise**: with the premise of
`transfer(1, 0)`, that call from `collideStore` succeeds with `balanceOf[1]` still 0, and the
collision spec asks for the caller's old balance, 5. -/
theorem collide_not_meets_scoped (hP : TransferFP [1, 0]) :
    ¬ TreeMeetsFixedOn (fun ρ => TransferFP ρ.args) SolidCore.Spec.Export.TokenSpecCollide.Token
      collideSpec ctx 2 transferTree := by
  intro h
  have hP' : ScopedSep (transferFootprint 0 8192 1) := by simpa [TransferFP] using hP
  obtain ⟨hne', hge0, -⟩ := transfer_slots hP' (by decide) (by decide) (by decide)
  have hne : solHash 1 0 ≠ solHash 8192 0 := fun he => hne' (by decide) he.symm
  have hs : ∀ k, collideStore k < 2 ^ 256 := fun k => by unfold collideStore; split <;> omega
  have h1 : (1 : Nat) ≠ solHash 8192 0 := by omega
  have hp := h [1, 0] collideStore [1, 0] ⟨collideStore, Ghost.zero, 0⟩ rfl (by simp) hs
    (by simp [collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token, decodeWords, Ty.ofWord]) rfl
    (by simp [ctx]) (by simp [Bundle.satAll, collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token])
    (by simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.TokenSpecCollide.Token, eval, slotOf, mkEnv,
      Env.cur, Ghost.zero, BinOp.apply, Ty.ofBits, collideStore, h1])
    (by simpa [TransferFP] using hP)
  have hlt := solHash_lt'
  have hkec := keccak_solHash
  unfold collideStore at hp
  generalize solHash = H at hp hlt hkec hge0 hne
  simp only [transferTree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow, Nat.reduceMod, Nat.zero_mod,
    Nat.reduceLT, ite_mod_nat, ite_true, ite_false, Nat.lt_irrefl, Nat.not_lt_zero, decide_false,
    Nat.reduceAdd, Nat.reduceSub, Nat.zero_add, Nat.add_zero, ite_self, Nat.one_ne_zero, ite_false,
    Nat.reduceEqDiff, reduceIte, hne, if_true, if_false] at hp
  obtain ⟨rets, -, hens, -⟩ := hp.1 (by simp_all)
  simp only [Bundle.satAll, Bundle.sat, collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token,
    List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv, Env.cur, Env.bind, BinOp.apply, Ty.ofBits,
    toWord, ctx, List.getD_cons_zero, List.getD_cons_succ, hkec, ofProp_ne_zero, ite_true, ite_false,
    Nat.zero_div, Nat.zero_mod, Int.reduceMod, Int.reduceToNat] at hens
  have hm1 := Nat.mod_eq_of_lt (hlt 1 0)
  have hm2 := Nat.mod_eq_of_lt (hlt 8192 0)
  simp_all

/-- **The premise of `transfer(1, ·)` from `ctx`'s caller holds of the real keccak256**: the
caller's and address 1's `balanceOf` slots hash apart, both at least `2 ^ 128` (kernel evaluation of
the sponge, TrustedBase.image1 and image2). So `collide_not_meets_scoped`'s hypothesis is satisfiable. -/
theorem transferFP_real : TransferFP [1, 0] := by
  have e1 := TrustedBase.image1
  have e2 := TrustedBase.image2
  refine ⟨fun x y hx hy he => ?_, fun x hx => ?_⟩
  · simp only [transferFootprint, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
      show (8192 : Nat) = 0x2000 from rfl, show (1 % 2 ^ 160 : Nat) = 1 from rfl] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | rfl | (rw [e1, e2] at he; exact absurd he (by decide)) | (rw [e2, e1] at he; exact absurd he (by decide))
  · simp only [transferFootprint, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
      show (8192 : Nat) = 0x2000 from rfl, show (1 % 2 ^ 160 : Nat) = 1 from rfl] at hx
    rcases hx with rfl | rfl
    · rw [e2]; decide
    · rw [e1]; decide

theorem collide_refuted : ¬ TreeMeetsFixedOn (fun ρ => TransferFP ρ.args)
    SolidCore.Spec.Export.TokenSpecCollide.Token collideSpec ctx 2 transferTree :=
  collide_not_meets_scoped transferFP_real

/-- info: 'SolidCore.Spec.TreeDemo.Token.collide_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collide_refuted

end SolidCore.Spec.TreeDemo.Token
