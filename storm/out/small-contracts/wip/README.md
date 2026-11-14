# small-contracts: work before the reset

Bundles of the lane's earlier work, before restarting from the current PR heads.

- `solidity-lean-wip.bundle`: branch `wip/small-contracts-pre-reset`, range `d54dabf..907cb13` (storm base).
- `solar-wip.bundle`: branch `wip/small-contracts-pre-reset`, range `237518e9e..e20c45070` (storm base).

Contents: generic succeeds-if proofs (`Verify/Spec/TreeSucceeds.lean`), allowed bound to the spec export
(`Verify/ShapeSpecExport.lean`), annotated sources and shape.json for events, mulx, bank, verify_token,
driver support (spec_connect succeeds-if, allowed_export, source_sem). events checked end to end by hand;
the driver run stopped at source binding (needs SOLC 0.8.35). Not CERTIFIED; superseded by the restart.
