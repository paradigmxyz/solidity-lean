import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Headline
import SolidCore.Refinement.Solar.Milestone
import SolidCore.Refinement.Solar.W1Value
import SolidCore.Refinement.Solar.LoweringGeneric
import SolidCore.Refinement.Solar.Sequences
import SolidCore.Refinement.Solar.Counter.Milestone
import SolidCore.Refinement.Solar.Counter.Sequences
import SolidCore.Refinement.Solar.Counter.Every
import SolidCore.Refinement.Solar.Counter.EverySeq
import SolidCore.Refinement.Solar.Counter.Value
import SolidCore.Refinement.Solar.Counter.NegativeAt
import SolidCore.Refinement.Solar.Counter.NegativeValue
import SolidCore.Refinement.Solar.Bank.Certified
import SolidCore.Refinement.Solar.Bank.Mutants
import SolidCore.Refinement.Solar.Events.Certified

/-! Axiom pass, part 1 of 5: the headline theorems, w1/w5, counter, bank and events. The milestone
exports of w1, w4, c4 and mulx all declare `SolarTV.Export.Main`, so one environment can hold only
one of them: w1's is here, and `C4.lean`, `MulX.lean` and `W4.lean` hold the others.
counter's generic source stage (`Counter.LoweringGeneric`) declares names that
`Counter.SpecAt` and `Counter.LoweringAt` also declare, so `CounterGeneric.lean` holds it. Every
`#print axioms` below must report a subset of [propext, Classical.choice, Quot.sound], and the
sweep must report no violation. Run with `scripts/refinement/axiom-audit.sh`. -/

-- Headline.
#print axioms SolidCore.Refinement.Headline.c1
#print axioms SolidCore.Refinement.Headline.w1
#print axioms SolidCore.Refinement.Headline.w4
#print axioms SolidCore.Refinement.Headline.c4
#print axioms SolidCore.Refinement.Headline.w5
#print axioms SolidCore.Refinement.Headline.w1_staged
-- w1 and w5 (solar's w1 export).
#print axioms SolidCore.Refinement.Solar.W1.certified
#print axioms SolidCore.Refinement.Solar.W1.certifiedAt
#print axioms SolidCore.Refinement.Solar.W1.certifiedValue
#print axioms SolidCore.Refinement.Solar.W1.certifiedSeq
#print axioms SolidCore.Refinement.Solar.W1.certifiedAt_single
#print axioms SolidCore.Refinement.Solar.W1.lowering
#print axioms SolidCore.Refinement.Solar.W1.loweringAt
#print axioms SolidCore.Refinement.Solar.W1.lowering_generic
#print axioms SolidCore.Refinement.Solar.W1.loweringAt_generic
#print axioms SolidCore.Refinement.Solar.W1.lowering_value
#print axioms SolidCore.Refinement.Solar.W1.loweringAt_value
#print axioms SolidCore.Refinement.Solar.W1.loweringValue
#print axioms SolidCore.Refinement.Solar.W1.lowering_rejects_bad
#print axioms SolidCore.Refinement.Solar.W1.loweringValue_rejects
#print axioms SolidCore.Refinement.Solar.W1.check_rejects_bad
-- counter.
#print axioms SolidCore.Refinement.Solar.Counter.certified
#print axioms SolidCore.Refinement.Solar.Counter.certifiedAt
#print axioms SolidCore.Refinement.Solar.Counter.certifiedValue
#print axioms SolidCore.Refinement.Solar.Counter.certifiedEvery
#print axioms SolidCore.Refinement.Solar.Counter.certifiedSeqEvery
#print axioms SolidCore.Refinement.Solar.Counter.certifiedSeq
#print axioms SolidCore.Refinement.Solar.Counter.certifiedAt_single
#print axioms SolidCore.Refinement.Solar.Counter.total
#print axioms SolidCore.Refinement.Solar.Counter.lowering
#print axioms SolidCore.Refinement.Solar.Counter.loweringAt
#print axioms SolidCore.Refinement.Solar.Counter.loweringEvery
#print axioms SolidCore.Refinement.Solar.Counter.loweringValue
#print axioms SolidCore.Refinement.Solar.Counter.stageAt
#print axioms SolidCore.Refinement.Solar.Counter.lowering_rejects_bad
#print axioms SolidCore.Refinement.Solar.Counter.loweringAt_rejects
#print axioms SolidCore.Refinement.Solar.Counter.stageAt_rejects
#print axioms SolidCore.Refinement.Solar.Counter.assemblyValue_rejects
#print axioms SolidCore.Refinement.Solar.Counter.mutantAdd_no_walk
#print axioms SolidCore.Refinement.Solar.Counter.mutantStore_no_walk
-- bank.
#print axioms SolidCore.Refinement.Solar.Bank.certified
#print axioms SolidCore.Refinement.Solar.Bank.certifiedValue
#print axioms SolidCore.Refinement.Solar.Bank.certifiedManifest
#print axioms SolidCore.Refinement.Solar.Bank.certified'
#print axioms SolidCore.Refinement.Solar.Bank.certifiedValue'
#print axioms SolidCore.Refinement.Solar.Bank.certifiedManifest'
#print axioms SolidCore.Refinement.Solar.Bank.ethKeccakAgree
#print axioms SolidCore.Refinement.Solar.Bank.lowering
#print axioms SolidCore.Refinement.Solar.Bank.loweringValue
#print axioms SolidCore.Refinement.Solar.Bank.certifiedFrom
#print axioms SolidCore.Refinement.Solar.Bank.certifiedValueFrom
#print axioms SolidCore.Refinement.Solar.Bank.certifiedFrom'
#print axioms SolidCore.Refinement.Solar.Bank.certifiedValueFrom'
#print axioms SolidCore.Refinement.Solar.Bank.certifiedManifestFrom
#print axioms SolidCore.Refinement.Solar.Bank.certifiedManifestFrom'
#print axioms SolidCore.Refinement.Solar.Bank.loweringFrom
#print axioms SolidCore.Refinement.Solar.Bank.loweringValueFrom
#print axioms SolidCore.Refinement.Solar.Bank.mutant_hex_rejected
#print axioms SolidCore.Refinement.Solar.Bank.check_rejects_slot
#print axioms SolidCore.Refinement.Solar.Bank.check_rejects_caller
#print axioms SolidCore.Refinement.Solar.Bank.check_rejects_fixedCaller
#print axioms SolidCore.Refinement.Solar.Bank.check_rejects_topic
-- events.
#print axioms SolidCore.Refinement.Solar.Events.certified
#print axioms SolidCore.Refinement.Solar.Events.certifiedValue
#print axioms SolidCore.Refinement.Solar.Events.certifiedManifest
#print axioms SolidCore.Refinement.Solar.Events.lowering
#print axioms SolidCore.Refinement.Solar.Events.loweringValue
#print axioms SolidCore.Refinement.Solar.Events.certifiedFrom
#print axioms SolidCore.Refinement.Solar.Events.certifiedValueFrom
#print axioms SolidCore.Refinement.Solar.Events.certifiedManifestFrom
#print axioms SolidCore.Refinement.Solar.Events.loweringFrom
#print axioms SolidCore.Refinement.Solar.Events.loweringValueFrom
#print axioms SolidCore.Refinement.Solar.Events.mutant_hex_rejected
#print axioms SolidCore.Refinement.Solar.Events.check_rejects_caller
#print axioms SolidCore.Refinement.Solar.Events.check_rejects_fixedCaller
#print axioms SolidCore.Refinement.Solar.Events.check_rejects_topic
#print axioms SolidCore.Refinement.Solar.Events.check_rejects_order

#axiom_audit ".lake/axiom-closure-main.txt" "SolidCore.Refinement.Headline" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Keccak" "SolidCore.Refinement.Generic"
