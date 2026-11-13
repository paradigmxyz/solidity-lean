import SolidCore.Spec.TrustedBase.Instances

/-! The axioms of the trusted base's theorems: `propext`, `Classical.choice` and `Quot.sound` at most,
and no `sorry`, `native_decide` (`Lean.ofReduceBool`) or `bv_decide`. -/

open SolidCore.Spec.TrustedBase in
section
#print axioms keccakSeparated_empty
#print axioms keccakSeparated_mapping
#print axioms not_keccakSeparated_univ
#print axioms Core.exec_dropAssumes
#print axioms Core.assumesHold_of_noAssume
#print axioms Core.spec_of_assumes
#print axioms Core.assumesHold_assumeX
#print axioms Core.not_assumesHold_assumeX
#print axioms Core.meetsContract_assign
#print axioms Core.not_meetsContract_assign
#print axioms trustedHold_nil
#print axioms trustedHold_of_holds
#print axioms follows_transcriptWith
#print axioms defaultCalls_transcriptWith
#print axioms interfaceEnsures_of_default
#print axioms viewDeterministic_of_default
#print axioms noForeignWrites_of_default
#print axioms viewDeterministic_twice
#print axioms not_viewDeterministic
#print axioms Reach.trans
#print axioms asmFree_example
#print axioms not_asmFree_example
#print axioms mulDivSummary_oz
#print axioms not_mulDivSummary_unchecked
#print axioms ozMulDiv_spec
#print axioms Hyps.plain_on
#print axioms Hyps.satisfiable
#print axioms spec_of_verdict_hyps
#print axioms Instances.asmFree_c4
#print axioms Instances.asmFree_counter
#print axioms Instances.c4_on
#print axioms Instances.counter_on
#print axioms Instances.counter_spec_of_verdict
end
