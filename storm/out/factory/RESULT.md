# Lane factory: UniswapV2Factory end to end (partial, round 1)

Base: solidity-lean `storm/base` (d54dabf). Deliverable: `sl-factory.bundle` (`git fetch sl-factory.bundle lane/factory`,
prerequisite d54dabf) and the same commit as `0001-*.patch` (`git am` onto storm/base).

## Proved (kernel-checked, axioms only propext, Classical.choice, Quot.sound)

1. **Return data after CALL and CREATE2 in the checker with creations** (generic, not Factory-specific).
   `AssembleCut.checkCF` now accepts RETURNDATASIZE and RETURNDATACOPY in a program that creates (the
   `!c.creates` gate in `AssembleCutSim.blockOkC` is gone; STATICCALL stays refused there,
   `AssembleCut.blockOkC_noSc_creates`). `AssembleCreateSegF.segF` threads a new invariant
   `RdF code T A w rd` (the frame's return data is what every extension of the run and creation tables
   answers at the world) through every segment; each CALL cut re-establishes it from `call0_cutQ`/
   `callValue_cutQ` (`rdRel_FO_of_table`), each CREATE2 cut from `create2_cutQ` (`rdRel_FO_of_create`),
   GAS reads and logs keep it (`RdF.append`), and it starts empty (`RdF.nil`). `AssembleCreateRunF.EntF`
   carries it, so `runs_of_checkCF`, `withinRun_of_checkCF`, `assembly_of_checkCF`,
   `withinRun_mir_of_checkCF` and `holds_of_checkCF` keep their statements and now cover revert
   bubbling after a failed CALL/CREATE2 (Factory's `initialize` call). Same named hypothesis `SitesRun`.
   Checked: `lake build SolidCore.Refinement.Solar.AssembleCreateRunF AssembleRevertCall AssembleRevertCut
   AssembleCallSeg AssembleCreateExample` green; the `#guard_msgs` axiom checks in SegF/RunF pass.

2. **CREATE2 address model** `Contracts/UniswapV2/Factory/Create2.lean`:
   `create2Address_eq` (EthLib's CREATE2 address = the model at EthLib's Keccak-256, by rfl),
   `pair_inj` (same factory, init code and address ⇒ same ordered tokens), `pairAddr_comm`
   (createPair(A,B) and (B,A) derive one address), under the ONE named premise
   `KeccakModel H xs`: no collision of H on the finite list xs of inputs the statement uses, in the
   digest and in its 20 address bytes. Built with `lake env lean`; not yet in a lean_lib root.

## Note for lane keccak-model (vacuity)
Injectivity of Keccak on ALL inputs (or on all inputs of a fixed length > 32 bytes) is refutable for
the real hash by counting, so a published statement that instantiates such a premise with
`keccak256` is vacuous. Here the premise is restricted to a finite list of inputs (consistent with
the real hash: "no collision among the hashes this run computes"). The same applies to "large gaps".

## Not proved yet (exact gaps, Factory)
- **EXTCODESIZE**: solar's createPair checks `extcodesize(pair)` before `initialize`. No checker
  accepts `.env "extcodesize"`; needs a third run table (code sizes after each message) in
  `FO`, a cut lemma from EthLib's extcodesize step, and its `segF` case. Until then `checkCF` refuses
  Factory's bytecode, so the assembly status of Factory is decoded only.
- Driver: `tools/certify/asm_cert.py` has no `creates` mode and `certify.py` emits only
  `checkC`/`checkL`; needs a `checkCF` path (CALL, CREATE2, CODECOPY with known offset,
  RETURNDATASIZE/COPY, EXTCODESIZE) emitting `withinRun_mir_of_checkCF` with `SitesRun` in the statement.
- MIR→EVM IR stage proofs for Factory (solar -Zemit-lean-stages of the flattened port: 3 MIR, 13 EVM
  IR stages, runtime 5469 bytes): generated, not yet run through the driver.
- Source side: SolidCore has no CREATE2/creationCode/inline assembly; the spec (solar-verify's Factory
  5/5) is not connected. `SitesRun` (callees keep the factory account, no logs from successful
  callees) is a named hypothesis over the Pair init code, not discharged.
- Termination/resources/equivalence statuses: none claimed for Factory yet.

Statuses for Factory now: equivalence none, termination none, spec none, resources none; generic
assembly checker extended (proved).
