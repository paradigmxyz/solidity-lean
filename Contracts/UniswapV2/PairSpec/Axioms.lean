import Contracts.UniswapV2.PairSpec.Negative
import Contracts.UniswapV2.PairSpec.NonVacuous

/-!
# UniswapV2Pair statement: the axiom audit

Every theorem of the pair's statement, wrapper, binding and negative controls, with the axioms the
kernel reports for it. The build fails if any gains an axiom (`#guard_msgs`): each is a subset of
propext, Classical.choice and Quot.sound; none uses sorry, native_decide or ofReduceBool. The
evaluated runs of Negative.lean (`#guard`) are not theorems and are not listed.
-/

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.inhabited

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.published_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.published_of_stages

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.bytecode_of_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.bytecode_of_statement

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.nonVacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.nonVacuous

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.bound

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.alterJump_changes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.alterJump_changes

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.altered_not_bound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.altered_not_bound

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.swapCall_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.swapCall_valid

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_swap

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_swapWrongK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_swapWrongK

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.noUpdate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.noUpdate_refused

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.wrongK_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.wrongK_refused

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.k_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.k_accepts

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.zeroBalance_ge' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.zeroBalance_ge

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.PairAllowanceApart.satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.PairAllowanceApart.satisfiable

/-- info: 'SolidCore.Refinement.Shapes.OpenFunctional.bytecode_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.OpenFunctional.bytecode_any

/-- info: 'SolidCore.Refinement.Shapes.OpenFunctional.of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.OpenFunctional.of_parts

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.skimCall_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.skimCall_valid

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_skim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_skim

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.skimUpdate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.UniswapV2.PairSpec.Negative.skimUpdate_refused
