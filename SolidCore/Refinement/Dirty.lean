import SolidCore.Refinement.Evm.Symex
import SolidCore.Refinement.Dirty.Source

/-!
# Dirty argument words

A call of a corpus function whose argument words are below `2 ^ 256` but not all
clean for their ABI types is rejected on both sides: SolidCore and solar's bytecode
on EthLib both revert with empty output and keep the storage.

* `SolidCore.Refinement.Evm.Calldata`: the call data `cdOf`, `Abi.Dirty`,
  cleanliness on bit vectors and the rules a symbolic run reads call data with.
* `SolidCore.Refinement.Evm.Symex`: the tactic `dirty_symex` and the lemma
  `dirty_of_frame` that turns its frame result into one about `Target.run`.
* `SolidCore.Refinement.Dirty.Source`: SolidCore's side, `run_dirty`, for every
  function whose shape `fnShapeOk` accepts, and `refines_full`, which joins the
  clean and dirty calls into one refinement.

Each corpus contract's `Corpus/<C>/Dirty.lean`, written by
`scripts/refinement/gen_proof.py`, proves EthLib's side with one `dirty_symex`
call per function, and `Corpus/<C>.lean` states `refines_full` for it.
-/
