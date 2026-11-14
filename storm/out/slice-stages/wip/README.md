# slice-stages: work preserved before the reset (from the erc20-sched lane)

- solidity-lean-wip.bundle: branch wip/erc20-sched-pre-reset, prerequisite storm/base (d54dabf,
  storm/sl-storm-base.bundle). W1Proofs.Segment: the boolLit/boolAndLit dsimprocs only fold a
  literal on the left (a right literal is not definitional and the kernel refused the term);
  lakefile lib uv2_erc20 over Generated/ (not committed).
- solar-wip.bundle: branch wip/erc20-sched-pre-reset, prerequisite storm/solar-sq (237518e9).
  certify.py --cut/--segment/--no-mir-joins and --exclude through cut points (scoped segment
  proofs); cutpoints.py: per-block cuts of the scheduling stage (blocks whose scheduled stack holds
  every live value), MIR-MIR block cuts where liveness agrees, junk heights under dynamic jumps,
  segment bounding that cuts a root's subtrees; asm_ctx.py: context certificate inference for
  AssembleCtx.checkXB (untested in the kernel).

Status at the reset (UniswapV2ERC20, 3 functions, anyCall then scoped): scheduling stage split
into ~220 per-block segment proofs, most check under -M 6000 in under 60 s per module of 16;
failing: segments inside internal functions (values the scheduler recomputes), MIR place-reads
segments, and a few EVM segments. Nothing here is a finished proof.
