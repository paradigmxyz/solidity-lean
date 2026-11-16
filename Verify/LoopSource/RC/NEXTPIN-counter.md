# Next-pin packet: Counter loop route on one driver commit

Status: **PARKED. Nothing was built or run to write this packet.** It names the driver commit that
holds both the RC2 certify driver and the loop-head emitter, and the identities a later admission
must check. Putting both commits in one tree closes neither open proof edge (section 5).

## 1. Driver commit

| Item | Value |
|---|---|
| Repository | paradigmxyz/solar. fd53f637 is a solar commit (its parent 800d78a9 is in solar), so the solar RC2 driver is the base and solidity-lean stays at 49d1d7f5. |
| Base (RC2 driver) | `0479b90a422245bf77facc51ea17b960ed5c5851` ("chore(certify): pin solidity-lean with returned-word tree_meets") |
| Cherry-picked | `fd53f637ef69065f897a1760726c254ccd7f9aa2` ("feat(verify): emit a loop-head manifest"): the loop-head producer. |
| Dependencies picked | **None.** fd53f637 has one parent, 800d78a9, and 800d78a9 is already an ancestor of 0479b90a (`git merge-base --is-ancestor 800d78a9 0479b90a` exits 0). So fd53f637 needs no commit that 0479b90a lacks. |
| Conflicts | None. The pick applied cleanly with no hunks resolved by hand. |
| New driver commit | `02e629fc2f13432860dc9918f273ffbaf09ee548`, branch `alpharush/t1-nextpin-counter-b`, parent 0479b90a, signed |
| Patch identity | `git patch-id --stable` is `8037ed7eb2de7129e259220c6965cb1bdff15d7d` for both fd53f637 and 02e629fc. The tree is `2588c9f60abeb70a1211e7f77e4c21e1dc289eb6`, equal to a local `git cherry-pick -x fd53f637` onto 0479b90a. |

Branch note: the branch name `alpharush/t1-nextpin-counter` in solar points at
`bb626f8ad085b129b4f65267de64157584a18258`, the parent of 0479b90a. That ref was left over from a
publish attempt that created the ref without a commit. It holds no commit of this packet, and
replacing it would need a force push, so the driver lives on `alpharush/t1-nextpin-counter-b`.
Ignore the bare `-counter` ref.

Ancestry:

```
$ git merge-base --is-ancestor 0479b90a422245bf77facc51ea17b960ed5c5851 02e629fc2f13432860dc9918f273ffbaf09ee548; echo $?
0
$ git merge-base --is-ancestor fd53f637ef69065f897a1760726c254ccd7f9aa2 02e629fc2f13432860dc9918f273ffbaf09ee548; echo $?
1
$ git rev-list --count 0479b90a422245bf77facc51ea17b960ed5c5851..02e629fc2f13432860dc9918f273ffbaf09ee548
1
$ git show fd53f637 | git patch-id --stable; git show 02e629fc | git patch-id --stable
8037ed7eb2de7129e259220c6965cb1bdff15d7d fd53f637ef69065f897a1760726c254ccd7f9aa2
8037ed7eb2de7129e259220c6965cb1bdff15d7d 02e629fc2f13432860dc9918f273ffbaf09ee548
```

fd53f637 is not an ancestor, because a cherry-pick makes a new commit. What ties 02e629fc to fd53f637 is
the equal patch-id: the same change, on the RC2 driver instead of 800d78a9.

Scoped diff against the RC2 driver (only `crates/verify`; `tools/certify` and `scripts/certify` are byte-identical to 0479b90a):

```
$ git diff --stat 0479b90a 02e629fc
 crates/verify/src/loop_heads.rs                    | 194 +++++++++++++++++++++
 crates/verify/src/main.rs                          |  89 ++++++++++
 crates/verify/src/vc.rs                            |  11 ++
 crates/verify/src/vc/infer.rs                      |   4 +
 crates/verify/src/vc/loop_head.rs                  | 102 +++++++++++
 crates/verify/tests/cases.rs                       |  67 +++++++
 .../tests/cases/loop_heads/Counter.loop-heads.json |  85 +++++++++
 crates/verify/tests/cases/loop_heads/Counter.sol   |  37 ++++
 8 files changed, 589 insertions(+)
```

## 2. Counter / InvOkFlat identities

All digests are sha256, recomputed from solidity-lean `alpharush/t4-loopvc-rc` at
`9236e32e135f3b2174bfb792421b271f513e15cc` and from solar 02e629fc.

| Identity | Path | sha256 |
|---|---|---|
| Source | `Verify/LoopSource/RC/inputs/Counter.sol` | `f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326` |
| Source (same bytes in the driver's test case) | solar `crates/verify/tests/cases/loop_heads/Counter.sol` | `f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326` |
| Spec (natspec: the driver records the source digest) | `Counter.sol` | `f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326` |
| Spec (loop route's extracted spec, MANIFEST.json `spec."Counter.sol"`) | | `e285303d4d4ba8706f75c48218e151f4b2a1d1690fd9a10e365f06c4e15a0e7f` |
| Options | `{"dry_run":false,"only":"Counter.bump","strict":false,"timeout_ms":10000}` (sorted keys, no spaces) | `ba151de58b53f19043a2b7f060d5954bae4026e59094c1a66715f1bb36192b1c` |
| Map (emitted by fd53f637) | `Verify/LoopSource/RC/Counter/Counter.loop-heads.json` | `f4cc0bcfe06953ec5f17efd19830c87b81e858e0b550c458eb99c3a31d707e9f` |
| Map (expected from 02e629fc, **predicted**) | the same file with `"compiler"` = `0.8.38+commit.02e629fc.solar.0.3.0-dev` | `8362f8636b433bf035b072d39dfa5b028664e6fddcbc574037dbc34866381014` |
| Map (driver test fixture, dry run) | solar `crates/verify/tests/cases/loop_heads/Counter.loop-heads.json` | `389679fcc2b873b487ca7604fee9181054a72d18920c88fc54355bdba3ab4b3e` |
| Map module | `Verify/LoopSource/RC/Counter/Map.lean` | `a529fbc2073e91f9d9444926a485693737e4f4ed5988c974d5c1a6e2e5a1d5a3` |
| VC script module | `Verify/LoopSource/RC/Counter/Script.lean` | `b5a81d4b0136b0e4e2c8c360a456f3d9a7d8f665e35c6fb2d7993db8e7db1e4e` |
| Obligations | `Verify/LoopSource/RC/Counter/Obligations.lean` | `840b98bcfa6405be1ee5834c1e6c6edf4857466f84d41b1b215e2276b54b915f` |
| VC (smt, vc) | MANIFEST.json `vc.counter` | smt `2c92f3bcd927369da89250662bd5a6174d3c06d0c3c38f5021509fe8810036e3`, vc `648d461056fe1649754b1ec259c2d1c48e8db8a4c11e5af281e73796399bc96a` |
| Invariants | `Verify/LoopSource/counter_bump.invariants.json` | `5f430947184c1c2e047264eca05b766de45fc79caa1831a78c7bad19fe908449` |

The map digest includes the `compiler` string. A map that 02e629fc emits therefore cannot
equal f4cc0bcf byte for byte. The predicted digest 8362f863 assumes the only change is that string.
That is a prediction, not a measurement. The fixture differs from f4cc0bcf only in its placeholder
compiler string, `dry_run: true` and `status: unknown`. Admission must name which form it checks:
the exact bytes the new binary emits, or the map with `compiler` normalized, compared with f4cc0bcf.

## 3. Expected binary

| Item | Value |
|---|---|
| Expected `binary_commit` | `02e629fc2f13432860dc9918f273ffbaf09ee548` |
| Expected version string | `0.8.38+commit.02e629fc.solar.0.3.0-dev` |
| Binary sha256 | **UNBUILT.** |
| solidity-lean base | `49d1d7f5d9b74165486bd9f634202bee1a3633eb` (44572c15 is an ancestor) |

Nothing was built while the acc5-siblingok run holds the heavy slot. The 0479b90a binary's
acceptance (acc5) does **not** carry over to 02e629fc. It is a different binary, built from a tree
with 589 more lines in `crates/verify`, and it needs its own certify run and fresh-clone replay.

## 4. Writers, patches and dependencies

- **Path writers:** T4 alone writes `Verify/LoopSource/**` in solidity-lean. T1 alone writes the
  driver branch `alpharush/t1-nextpin-counter-b` in solar. This packet is the only file T1 adds
  under `Verify/LoopSource/`, on its own branch, for T4 to take or replace.
- **Allowed in the driver:** 0479b90a plus fd53f637's change as 02e629fc, and nothing else. No patch to
  `tools/certify`, `scripts/certify`, the base or the lake packages.
- **Allowed in solidity-lean:** base 49d1d7f5 plus the loop-route files at their MANIFEST.json
  `modules` digests (9236e32e). Any other difference fails admission.
- **Dependencies:** the 16 lake packages at the revs in `ADMISSION-counter.md` section 2; Lean
  `leanprover/lean4:v4.35.0`; z3 5.4.1; solc 0.8.35 for AST binding; Rust as locked by
  `cargo build --locked --bin solar`.

## 5. Open proof edges

Both are **OPEN**. Building 02e629fc closes neither.

- **(a) OPEN: source loop to MIR/runtime expected-type link.** `body_runs_vc` is a theorem about
  source semantics. No module states it against the MIR loop cut point or the bytecode the driver
  certifies, and there is no whole-statement link to the driver's `Statement`. 02e629fc only lets
  the certifying binary emit the loop-head map. It proves nothing about that map.
- **(b) OPEN: fixed-fuel gas stage.** The driver's gas bound reads a fixed stage count
  (`gas_need` through `shape_gen.last_stage`). A loop whose trip count depends on storage has no
  fixed stage count, and no fixed-fuel `stage_of_runs` exists for a loop body.

The only change the pick makes is that the first missing input of `ADMISSION-counter.md`
(a driver commit holding both) now exists, unbuilt. With today's inputs, the expected verdict is still
`REJECTED`, now at the MIR/runtime link (a) instead of at the missing driver.

## 6. Admission prerequisites still missing

1. **Whole-tree resource and keepalive admission:** a sampled whole-tree peak RSS within the 8 GiB
   budget, plus a keepalive plan that does not rely on the host staying up after a turn ends
   (`ADMISSION-counter.md` section 4).
2. **Acknowledgement that the earlier restart is used up:** the InvOkFlat r2 restart ended
   ABORTED-env (`RC/runs/invokflat/`). Any new attempt needs a new decision. It is not a retry.
3. A build of 02e629fc and its binary sha256, after the heavy slot is free.
4. Closure of edges (a) and (b), or an explicit scope that admits the route without them.

**Counter stays PARKED.**
