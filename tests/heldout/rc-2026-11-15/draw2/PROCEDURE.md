# Second held-out draw (H4, H5): procedure, frozen before the draw

Written and published before `draw.py` was run on any input. The first set (H1-H3, e0564a28) was
chosen by reviewer judgment, not by a seed: there is no earlier seed rule to repeat, so this draw
uses a new mechanical rule, stated here. It is made after H1 was REJECTED and H3 BLOCKED, and is
labelled as such in RC.md.

- **Pool**: every `.sol` file under `contracts/src` of Solidity by Example,
  https://github.com/Cyfrin/solidity-by-example.github.io at
  5bcdca0239409d7336a07b66a6fca8d0bcc710e6 (MIT), the same pool as the first set.
- **Fixed exclusions** (the ones SELECTION.md named before any run): the three files of the first
  set; any path matching `counter`, `erc20`, `uniswap` or `flag` (case-insensitive); files without
  `SPDX-License-Identifier: MIT`.
- **Eligibility**: the file, unedited, passes the generic driver's own source envelope:
  `envelope()` of `tools/certify/generic.py` at solar 800d78a98b9e64612c742d5038e7e2ec35dd52b4, run
  on the AST of solc 0.8.35 (sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4),
  with no contract named (so the file must hold exactly one concrete contract), no invariants and
  `natspec=False`. Nothing else decides eligibility: no rule about getters, mappings, `delete`,
  return values or any other known gap. No file is trimmed.
- **Seed**: the sha256 of H1's `record.json`,
  `4758becf4ea3dc5ccb0ed92b8d3e17aa2573bcbb810ec04acbd19d6741adc96e`, produced by the held-out
  runner's run and not chosen by the reviewer.
- **Order**: eligible files ranked by `sha256(seed + "\n" + path)` (hex, ascending). H4 is the
  first, H5 the second. If a drawn file then fails at any stage, that is its verdict: it is
  reported, and not replaced.
- **Specs**: written by the reviewer after the draw and before any driver run, under the same
  rules as SELECTION.md (`@custom:succeeds-if` and `@custom:ensures` per declared function, minimal,
  no frame), added as NatSpec lines only.

Reproduce: `python3 -I draw.py <solar@800d78a9> <solidity-by-example@5bcdca02> <solc-0.8.35>
4758becf4ea3dc5ccb0ed92b8d3e17aa2573bcbb810ec04acbd19d6741adc96e > draw.json`.
