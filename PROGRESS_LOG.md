# Progress Log

- 2026-05-11 10:40:00 PDT - baseline - copied `/Users/dan/Projects/solid-core` and `/Users/dan/Projects/solid-core-yulcore` into `/Users/dan/Public/solid-core-spine` without nested `.git` repositories and committed the combined baseline as `a55a0e1`.
- 2026-05-11 10:40:00 PDT - deletion - removed public example-specific compiler surfaces from the active tree: legacy compiler, MVP, source-to-FullYul bridge, parity subjects, Yul example data, parity CLI, Foundry harnesses, nested packages, and old package-local docs.
- 2026-05-11 10:40:00 PDT - architecture - created one public layer/pass spine under `SolidCore.Spine`; root `SolidCore` now imports only the spine and reusable source/target semantic layers.
- 2026-05-11 11:10:54 PDT - test - added root `tests/` area for EVM parity, shared cases, future source replay, and future end-to-end proof checks; restored Forge parity harness outside the public compiler spine.
- 2026-05-11 11:20:27 PDT - consolidation - collapsed the lower public spine to generated Yul subset -> stack CFG -> bytecode -> EVM; removed symbolic/full-Yul pass targets from active ownership.
- 2026-05-11 11:22:16 PDT - test - command `LEAN_NUM_THREADS=1 $HOME/.elan/bin/lake build SolidCore SolidCoreYulCore evm_parity` and `python3 tests/bin/evm_parity.py forge`; result green with 21 Forge parity tests passed.
- 2026-05-11 11:22:40 PDT - deletion - removed unimported `SolidCoreYulCore/SolidityLayout.lean`; future layout facts should enter through the active `L04_Layout` spine.
- 2026-05-11 11:33:37 PDT - coordination - added lightweight `supervisor` log and softened ownership rules so agents can make small adjacent edits while still watching for vacuous theorem paths.
- 2026-05-11 11:36:28 PDT - relocation - moved project directory from `/Users/dan/Public/solid-core-spine` to `/Users/dan/Projects/solid-core-spine`; updated coordination path.
