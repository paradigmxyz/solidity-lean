# hash-scope lane: work preserved before the reset

Branch wip/hash-scope-pre-reset in each repository, as git bundles and format-patches.

* sl-wip-hash-scope-pre-reset.bundle: solidity-lean, range storm/base (d54dabf)..wip/hash-scope-pre-reset.
  Verify/Spec/KeccakModel.lean (a model premise, now superseded: its universal slot sets are not
  the scoped premise the target asks for), the counting refutation not_nestedSlotsSeparated
  (checked: lake build Verify.Spec.KeccakModel), Contracts/Token/KeccakNeg.lean (a spec that needs
  a collision is refuted; checked), docs/KECCAK_MODEL.md, and the ERC20 premise renames (the ERC20
  Connect proofs did not close under the anchored model; not checked).
* solar-wip-hash-scope-pre-reset.bundle: solar, range storm/solar-sq (237518e9)..wip/hash-scope-pre-reset.
  check_final prints PREMISE / KECCAK_MODEL lines from the compiled statement; final.py refuses
  ad-hoc keccak premises; spec_connect.py emits the model premise (syntax-checked only).
