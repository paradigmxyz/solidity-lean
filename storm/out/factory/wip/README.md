# factory lane: work before the reset

- sl-factory-wip.bundle: solidity-lean storm/base (d54dabf) .. wip/factory-pre-reset (c3e788b).
  Contains bd695b2 (return data after CALL and CREATE2 in the assembly checker with creations;
  CREATE2 model) and a lakefile lib entry for the Factory stage proofs.
- solar-factory-wip.bundle: solar storm/solar-sq (237518e9e) .. wip/factory-pre-reset (60cf4aae1):
  certify.py --joins also forces the cut-point composition on loop-free programs.
- Not included: the generated Factory stage proofs (Certified/uniswap_v2_factory), which derive
  from GPL sources and are regenerated at build. Several Runs/Evm*.lean segment proofs were still
  failing or timing out (Evm10 hit recursion depth; Evm1 ran past its heartbeat budget) when the
  turn was interrupted; none of them is claimed proved.
