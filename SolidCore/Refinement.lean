import SolidCore.Refinement.Statement
import SolidCore.Refinement.Corpus
import SolidCore.Refinement.Compose
import SolidCore.Refinement.Spec
import SolidCore.Refinement.Headline
import SolidCore.Refinement.Seq.Corpus
import SolidCore.Refinement.Solar.W1
import SolidCore.Refinement.Solar.Lowering
import SolidCore.Refinement.Solar.Milestone
import SolidCore.Refinement.Solar.LoweringGeneric
import SolidCore.Refinement.Generic.MulTest

/-!
# Refinement of solar's bytecode against SolidCore

`SolidCore.Refinement.Statement` states what it means for runtime bytecode to
implement a SolidCore contract. Each contract in `scripts/refinement/corpus/` has
a module that proves it for solar's bytecode at the commit in
`scripts/refinement/solar-rev`. `scripts/refinement/check.sh` regenerates the
bytecode and checks every proof.

`SolidCore.Refinement.Corpus` holds one generated proof per corpus contract, with
no hand-written part: `agree` compares both semantics on one call, slot by slot
on the finite set of slots either side touches, and `refines_of_all` turns
agreement on a list of calls into `Refines`. `Abi.calls` lists every call with
clean argument words, which `native_decide` checks in parts.
A contract with a `bytes`, array or struct parameter instead gets `refines_full`
on `Dyn.dynScope` (`SolidCore.Refinement.Dyn`): every canonical encoding within a
bound, checked the same way, and every malformed call data of any length below
`2 ^ 32`, which both sides reject, proved symbolically.
`C1.Refinement` is the hand-written proof for c1, kernel-checked on the EthLib
side and covering dirty argument words too; its SolidCore side uses `native_decide`, so it is in
the `SolidCoreNative` library, not this one.
-/
