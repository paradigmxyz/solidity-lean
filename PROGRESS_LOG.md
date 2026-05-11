# Progress Log

- 2026-05-11 10:40:00 PDT - baseline - copied `/Users/dan/Projects/solid-core` and `/Users/dan/Projects/solid-core-yulcore` into `/Users/dan/Public/solid-core-spine` without nested `.git` repositories and committed the combined baseline as `a55a0e1`.
- 2026-05-11 10:40:00 PDT - deletion - removed public example-specific compiler surfaces from the active tree: legacy compiler, MVP, source-to-FullYul bridge, parity subjects, Yul example data, parity CLI, Foundry harnesses, nested packages, and old package-local docs.
- 2026-05-11 10:40:00 PDT - architecture - created one public layer/pass spine under `SolidCore.Spine`; root `SolidCore` now imports only the spine and reusable source/target semantic layers.
