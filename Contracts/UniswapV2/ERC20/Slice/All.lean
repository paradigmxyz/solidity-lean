import Contracts.UniswapV2.ERC20.Slice.BundleNeg
import Contracts.UniswapV2.ERC20.Slice.MutantsDebit

/-!
# UniswapV2ERC20.transfer's certified slice (E7): every module, and the axioms of its theorems

Each theorem below depends on `propext`, `Classical.choice` and `Quot.sound` at most: no `sorryAx`, no
other axiom (the kernel checks `Gen.transfer_erase_eq`, `Gen.deploy_eq` and `tree_eq` are `kernel_rfl` equations).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.targetPost_of_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetPost_of_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.tree_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.res_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms res_ok

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.res_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms res_sub

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.res_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms res_add

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.tree_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_eq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.transfer_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_meets

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.sepArgs_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sepArgs_iff

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.run_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_tree

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.transfer_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_holds

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_bundle

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.valid_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms valid_inhabited

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.nonVacuous_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonVacuous_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.nonVacuous_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonVacuous_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.self_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_ok

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.self_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_fail

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.self_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_max

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.self_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms self_short

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_bytes

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_bytes_enough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_bytes_enough

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminates

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.functional_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms functional_of_equiv

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.certified_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_of

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.bytes_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.bytes_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.bytes_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_bundle

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.bytes_target_enough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_target_enough

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.inert_not_target' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inert_not_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.log_refuted_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.log_refuted_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.log_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.log_refuted_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.ret_refuted_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.ret_refuted_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.ret_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.ret_refuted_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.ret_refuted_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.ret_refuted_bundle

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.nonVacuous_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.nonVacuous_bundle

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.debit_refuted_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.debit_refuted_seq

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.debit_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mutants.debit_refuted_target

end SolidCore.Spec.UniswapV2.ERC20.Slice
