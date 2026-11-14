# pair-spec wip before reset

- sl-pair-spec-pre-reset.bundle: solidity-lean commits storm/base (d54dabf)..wip/pair-spec-pre-reset (4 commits: open-world statement, reentrancy admission, inputs module, trace-based ghost step for mint/burn + certify driver files). `git fetch <bundle> wip/pair-spec-pre-reset`.
- solar-pair-spec-pre-reset.bundle: solar commits storm/solar-sq (237518e9e)..wip/pair-spec-pre-reset (2 commits).
- Kernel VC discharge of the pair's solar-verify VCs was interrupted by a machine restart after 24 obligations (approve 8/8, transfer and transferFrom partial); not a result.
Superseded by the reset onto alpharush/certified-translation; see ../RESULT.md.
- PairRun.t.sol: forge test of the earlier round (untrusted evidence), superseded by Negative.lean.
