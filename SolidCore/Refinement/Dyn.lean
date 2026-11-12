import SolidCore.Refinement.Dyn.Refines

/-!
# Dynamic ABI parameters and malformed call data

The refinement of a corpus function with a `bytes calldata`, `T[] calldata` or
struct parameter, on call data that is not a list of words.

* `SolidCore.Refinement.Dyn.Abi`: the parameters `DParam`, the canonical encodings
  `encodings` within a bound, `Malformed` call data and the scope `dynScope`.
* `SolidCore.Refinement.Dyn.Source`: SolidCore's side, `run_malformed`: for every
  function whose shape `dfnShapeOk` accepts, SolidCore's ABI decoder rejects every
  malformed call data with the empty revert.
* `SolidCore.Refinement.Dyn.Evm`: the tactic `dyn_symex`, which runs solar's bytecode
  on free call data (its size and every word it loads are symbols), and the lemma
  `malformed_of_frame` that turns its frame result into one about `Target.run`.
* `SolidCore.Refinement.Dyn.Refines`: `refines_dyn`, which joins the canonical
  encodings (checked by evaluation) and the malformed call data into one refinement
  on `dynScope`.

Each such corpus contract's `Corpus/<C>/Malformed.lean`, written by
`scripts/refinement/gen_proof.py`, proves EthLib's side with one `dyn_symex` call per
function, and `Corpus/<C>.lean` states `refines_full` on `dynScope` for it.
-/
