# refuter-6 pre-reset work

Work from the first refuter-6 run, against storm/base (solidity-lean d54dabf) and storm/solar-sq
(solar 237518e9e), saved before restarting from the current PR heads.

- sl-wip.bundle: solidity-lean branch wip/refuter-6-pre-reset (prerequisite d54dabf): Refute6/
  repro modules (Model, Variants, Shadow, Proof), a shape.json variant and the harness with its
  outputs under Refute6/harness/.
- solar-wip.bundle: solar branch wip/refuter-6-pre-reset (prerequisite 237518e9e): only the
  solidity-lean pin moved to the refuter commit.

Findings from that run (each reached strongest=True in the driver's own final.py + check_final +
leanchecker, see Refute6/harness/*.out): R1 env premise is any Prop (a premise equal to the
conclusion, or False); R4 gas bound up to 2^64-1 accepted; R5 statement inputs resolve inside
namespace Certified.NAME.Final, so an imported declaration Certified.<input name> shadows them;
R6 valid-call set narrowed to one call still certified. They are re-checked against the current
heads in ../REPORT.md.
