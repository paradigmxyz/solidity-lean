import SolidCore.Verify.CounterBump
import SolidCore.Verify.Fuel

/-! Axioms of the Loom pieces SolidCore's verification builds on, and of Counter's `bump`. Each
shows only `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms MAlgExceptErr
#print axioms MAlgExceptErrProp
#print axioms MAlgExceptErr.lift_eq
#print axioms triple_bounded
#print axioms triple_while
#print axioms bounded_eq_of_variant
#print axioms TotalCorrectness.repeat_inv
#print axioms PartialCorrectness.repeat_inv
#print axioms triple_forIn_list
#print axioms StateT.wp_get
#print axioms StateT.wp_set
#print axioms ExceptT.wp_throw
#print axioms SolidCore.Verify.wp_eq_loom
#print axioms SolidCore.Verify.wp_get
#print axioms SolidCore.Verify.wp_set
#print axioms SolidCore.Verify.wp_throw
#print axioms SolidCore.Verify.triple_whileM
#print axioms SolidCore.Verify.triple_of_wp
#print axioms SolidCore.Verify.Triple.finishes
#print axioms SolidCore.Verify.tripleSome_of_wp
#print axioms SolidCore.Verify.Triple.some
#print axioms SolidCore.Verify.satisfies_of_triple
#print axioms SolidCore.Verify.CounterBump.body_step
#print axioms SolidCore.Verify.CounterBump.bump_spec
#print axioms SolidCore.Verify.runAny_isSome_iff
#print axioms SolidCore.Verify.runAny_spec
#print axioms SolidCore.Verify.runAny_of_run
#print axioms SolidCore.Verify.tripleAny_of_wp
#print axioms SolidCore.Verify.TripleAny.some
#print axioms SolidCore.Verify.implementsAny_of_some
#print axioms SolidCore.Verify.tripleAny_of_some
#print axioms SolidCore.Verify.triple_of_within
#print axioms SolidCore.Verify.Triple.any
