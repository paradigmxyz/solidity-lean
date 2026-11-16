# Admission packet: Counter loop route, clean-room driver replay

Status: **not admitted.** This document records what the replay needs. Nothing was built or run to
write it. The route stays parked at a56262ce until a new decision. The packet names one input that
does not exist yet (section 2): a driver commit that holds both the certify driver and the
loop-head emitter. Until that input exists, the only result this packet admits is the explicit
failure verdict in section 5.

## 1. Declared inputs

| Input | Value |
|---|---|
| Driver (paradigmxyz/solar, `tools/certify/certify`) | `800d78a98b9e64612c742d5038e7e2ec35dd52b4` ("fix(certify): bind archived inputs to the pinned inputs") |
| Loop-head producer (paradigmxyz/solar, branch `alpharush/t1-loop-heads`) | `fd53f637ef69065f897a1760726c254ccd7f9aa2`, version string `0.8.38+commit.fd53f637.solar.0.3.0-dev`. **Not an ancestor of 800d78a9** (`git merge-base --is-ancestor` fails). |
| solidity-lean base | `44572c150176365fa5e0d56ae6c59a7a443f8122` |
| Loop route proof tree (solidity-lean `alpharush/t4-loopvc-rc`) | `675964ccd0908ca1728879aaf8ec20cc1cc966bb` (proofs), replay receipt e13cda49, park record a56262ce |
| Source | `Verify/LoopSource/RC/inputs/Counter.sol`, sha256 `f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326` |
| Spec | `natspec`: the solar-verify annotations in the source are the spec (`/// @custom:invariant count <= limit`, `@custom:ensures` on the constructor and functions). The driver records `spec.sha256` = the source digest above. The loop route's extracted-spec digest (MANIFEST.json `spec."Counter.sol"`) is `e285303d4d4ba8706f75c48218e151f4b2a1d1690fd9a10e365f06c4e15a0e7f`. |
| Loop-head map | `RC/Counter/Counter.loop-heads.json`, sha256 `f4cc0bcfe06953ec5f17efd19830c87b81e858e0b550c458eb99c3a31d707e9f` (from solidity-lean ee66e071 `Certified/record/loop-heads-counter/`) |
| VC script | smt sha256 `2c92f3bcd927369da89250662bd5a6174d3c06d0c3c38f5021509fe8810036e3`, vc sha256 `648d461056fe1649754b1ec259c2d1c48e8db8a4c11e5af281e73796399bc96a`; options `only=Counter.bump`, `strict=false`, `timeout_ms=10000` |
| Toolchains | Lean `leanprover/lean4:v4.35.0`; z3 5.4.1; Rust as locked by the driver (`cargo build --locked --bin solar`); `SOLC` = solc 0.8.35 (the driver's pinned solc for AST binding) |

This is not the driver's own example `tools/certify/examples/counter.sol` (sha256 28af3c6b…, a different contract).

Command:

```
tools/certify/certify Counter.sol natspec --solidity-lean <worktree> --base 44572c15 \
  --work runs/counter-loop-work --record-dir runs/counter-loop \
  --packages-from <worktree> --probe-cache <worktree>
```

Environment:

- `LEAN_NUM_THREADS=1`, `CARGO_BUILD_JOBS=2`, `SOLC` as above.
- The driver sets these itself: `LEAN_MEMORY=6000`, `CERTIFY_ALLOW_UNPINNED=1`, `CERTIFY_CLEAN_BUILD=1`, `CERTIFY_SOLAR_SHA256` = the binary it built.
- **`CERTIFY_REPLAY_TRUST_UPSTREAM` is unset.** The driver also removes it, with `SOLAR`, `CERTIFY_SKIP_BUILD` and `CERTIFY_ALLOW_FOREIGN_SOLAR`, from the environment of `scripts/certify` (`tools/certify/generic.py:1028`). So leanchecker replays every module of the closure, upstream lake packages included, and **trusted=0 is required.** Any module trusted by directory is a provenance caveat and blocks the strongest status.

## 2. Package manifest and closure

The replay closure is every module the published statement imports, transitively. That means the
toolchain's `lib/lean` plus every package below. The driver copies `.lake/packages` from
`--packages-from` and replays each module with leanchecker; the driver alone fixes the exact module
count when it plans the closure. The prior InvOkFlat prebuild listed about 6,180 build jobs for the
EthLib proof modules alone.

| Package | Origin | Rev |
|---|---|---|
| mathlib | github.com/leanprover-community/mathlib4 | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| batteries | github.com/leanprover-community/batteries | 66e469188fe07963e5cf666c7d4433f45b8131c5 |
| aesop | github.com/leanprover-community/aesop | 4a174c490d8707121c4a9290800489f105d85e07 |
| Qq | github.com/leanprover-community/quote4 | dce0ad79c486cb1fb504af04f953c3466b0c6db8 |
| plausible | github.com/leanprover-community/plausible | dfa4f38190d07c37e315953e08b90fe2d95b3c24 |
| proofwidgets | github.com/leanprover-community/ProofWidgets4 | df72b022e558978a1c50264cfc4d7fec86fa8e04 |
| importGraph | github.com/leanprover-community/import-graph | a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93 |
| LeanSearchClient | github.com/leanprover-community/LeanSearchClient | d6b4c7be5be75ec4917c873ac50c756dc1436372 |
| Cli | github.com/leanprover/lean4-cli | c24fe6078c630e89b489bffe59b3e20ac30d12c8 |
| cslib | github.com/leanprover/cslib | 5b56df99362532c46e1175381fbbdd755bd56030 |
| EthLib | github.com/ethereum/EthLib | 2cd5d14a6a2f6fd22ef6b68423e45cfa3a21001a |
| VCVio | github.com/Verified-zkEVM/VCVio | bbf05eeeedf84c5f98baaf5ab846f2d2479cc8ab |
| PolyFun | github.com/Verified-zkEVM/PolyFun | 4181c82238142d9b73403fbf4c4b13e1a801e400 |
| QuantumFoundations | github.com/lean-crypto-foundations/QuantumFoundations | 901aaab7967ceecd2240d0b38bbde7cf3e2c14ac |
| evm-interaction | path `vendor/evm-interaction` at base 44572c15 | tree 9d1080e8d36e71ac163d6ebb93e956b5d74f92e1 |
| evmyul | path `vendor/evmyul` at base 44572c15 | tree 2d7a8e2da88354427547b89ea8e7160d4b2daa76 |

The 18 loop-route files (CheckRaw, LoopMap, the Counter and Gcd Script/Obligations/Map modules,
Receipt, Headline, HeadlineCheck, LoopVC, LoopBinding, LoopErased, the four generators and
replay.sh) come from 675964cc. Their digests are in `RC/MANIFEST.json` `modules`.

Available now:

- All 16 packages at the revs above, in a prebuilt writable copy of the base. The EthLib proof oleans are about 99.8% built: 6170 of 6180 jobs finished before the last kill.
- Source, map, VC script, z3 5.4.1, Lean 4.35.0.
- The driver checkout at 800d78a9.
- A solar build at fd53f637, the one that emitted the map.

Missing:

1. **A single driver commit that contains both 800d78a9's `tools/certify` and fd53f637's loop-head emitter.** Without it, the binary the driver builds cannot emit the loop-head map, and nothing ties the map to that binary. The map's author owns that interface, so producing this commit is a request to them, not a patch in this lane.
2. **A whole-statement link from the source loop theorem to the driver's `Statement`.** Today `body_runs_vc` is a source-semantics theorem. No module states it against the MIR loop cut point or the bytecode the driver certifies.
3. **A fixed-fuel `stage_of_runs` for a loop body.** The driver's gas bound comes from `gas_need` (`tools/certify/generic.py:613`), which reads the last stage through `shape_gen.last_stage` (`tools/certify/shape_gen.py:48`). That reads a fixed stage count, and a loop whose trip count depends on storage does not have one.

## 3. Isolated worktree and the path writer

- **Base:** a fresh `git worktree` of solidity-lean `44572c15`, with the 18 files from 675964cc checked out over it. Its own `.lake/packages`, copied from the prebuilt set and writable, so lake can rebuild proof oleans in place. That was the cause of the ABORTED-env exit 1, when the packages were read-only. The driver gets its own worktree at the declared driver commit and its own `CARGO_TARGET_DIR`.
- **Single writer:** one process, `tools/certify/certify` and its children, run under the one-heavy-job lock (`flock` on the lane's lock file). Nothing else writes the worktree, its `.lake`, the driver tree or the run directories while it runs. The proof build runs in the driver's mount namespace, where HOME is read-only except the package's `.lake`.
- **Allowed patches:** none to the driver, the base or the packages. The only files layered on the base are the 18 loop-route files at their MANIFEST digests. Any other difference fails admission, and the driver's `clean_tree.py` and fingerprinting enforce that.

## 4. Resources and keepalive

**Measured so far** (`ru_maxrss` is the largest single child, not the whole process tree):

| Run | Wall | Largest child RSS |
|---|---|---|
| Linked-package source-only replay (34 checks) | 484.7 s | 5,380,124 KB |
| InvOkFlat certify run that exited 1 (driver 800d78a9) | 2,159.9 s | 5,395,244 KB |

The 2,159.9 s run's sampled system-wide peak was 4,167,152 KB used. There is no whole-tree
measurement yet.

**Expected:**

- **Peak tree RSS:** at most about 7 GiB. That is one Lean process at `LEAN_MEMORY=6000` with `LEAN_NUM_THREADS=1`, plus lake, the driver and z3. The admission budget is 8 GiB tree RSS, so the run must record a sampled whole-tree peak (sum of RSS over the process group every 5 s) next to `ru_maxrss`.
- **Wall time:** remaining EthLib prebuild minutes; `cargo build` about 10–20 min; certify, including the full leanchecker replay of the closure, 1–3 h (est.). Budget 4 h.

**Hand capacity:** 5 CPUs, 14 GiB RAM (13 GiB free when idle), 54 GiB free disk. One heavy job at a time.

**What killed the prior runs.** None of them failed in the work itself. Each death was the host
machine pausing or restarting after the agent turn that started it had ended:

- r1 twice: killed or stopped.
- r2 first try: died at prebuild 5638/5647, with the last log line at 05:01 UTC.
- r2 restart, the one allowed restart: died at 6170/6180, with the last log line at 06:09 UTC. The host was found with 0 min uptime at 06:39 UTC.

A tracked background keepalive (`tail --pid`) was running during the last two. It did not keep the
host up once the turn ended, and the live preview could not be shared. The separate ABORTED-env
exit 1 came from a read-only package set, and section 3 removes that cause. The restart is
exhausted. A new attempt needs a new decision.

**Keepalive plan, and why a repeat would not hit the same failure:**

1. **Keep the turn open for the whole run.** The deaths happened only after a turn ended. The run is started and watched from within one turn that waits on the process until it exits. If a turn's wall limit is shorter than the run, the run does not start: admission fails rather than relying on the host staying up.
2. **Make the run resumable at no cost to the claim.** The proof oleans persist across restarts: r2's restart resumed at about 5640 and got about 530 modules further. So finish the package prebuild first, as its own step, and gate the certify run on it being complete (`lake -R build` reports nothing left to do). The certify step then starts from a warm cache, and a replay that is cut short leaves no partial verdict. The driver replays every module from scratch in every run, so a warm cache does not weaken the trusted=0 replay.
3. **Treat a death as ABORTED-env, never as a retry.** Any host restart (uptime below the run's age) records ABORTED-env with the last log line and needs a new decision, as at a56262ce.

## 5. Acceptance target

**Pass:** the driver prints `CERTIFIED` and exits 0, and the record shows all of the following:

- `statuses.replay` with every closure module replayed by leanchecker in this run, and **trusted = 0**: no module trusted by directory and no provenance caveat.
- Axioms of the published statement and of `Contracts.VerifyCounter.LoopVC.body_runs_vc` exactly `[propext, Classical.choice, Quot.sound]`.
- The **exact expected-type binding** of the loop theorem at each level:
  - MIR: the loop-head map's cut point, from the declared driver's own binary, matches `Counter.loop-heads.json` (f4cc0bcf…).
  - Runtime: the bytecode the driver certifies is the one whose `Statement` includes the loop body's `BodyRuns` claim at fuel ≥ 2^256 + 8.
  - Gas: the statement's gas bound comes from a fixed-fuel `stage_of_runs` for the loop, not from `last_stage`'s fixed stage count.

  Each binding is checked by `example : <declared type> := <theorem>` in a module that imports no proof modules, as in `RC/HeadlineCheck.lean`.
- `record.json` sha256 published with the run's receipts.

**Explicit failure verdict:** otherwise the run is `REJECTED` and names the first stage that fails:

- a missing driver that holds both commits (section 2, item 1);
- no MIR or bytecode link (item 2);
- no loop gas stage (item 3);
- a replay leftover or a trusted module;
- an axiom outside the list;
- a resource budget exceeded.

With the inputs available today, the expected verdict is `REJECTED` at item 1, and this packet does
not claim otherwise.

**The 34/34 receipt is not full closure.** The replay receipt at e13cda49 (34/34 checks, exit 0,
484.7 s) replayed the loop route's own modules on a fresh worktree, but it **linked
`.lake/packages` from the base package set.** It did not leanchecker-replay the upstream packages,
did not run the certify driver, and binds only source semantics: no MIR, bytecode or gas. It is
evidence for the source theorem only. It is **not** a trusted=0 full-closure replay and not an
end-to-end certificate.
