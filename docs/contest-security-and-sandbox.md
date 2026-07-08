# Divergence Contest — Security & Sandbox Requirements

This is the operational security contract for running the adjudicator as a
**public, self-serve, programmatically-checked** endpoint (e.g. behind
optimizationarena.com). It complements the design (`competition-design.md`) and
the adversarial review (`competition-design-review.md`).

The contest is **for fun / leaderboard only** — there is no monetary component —
but the adjudicator still executes **attacker-controlled code** on our
infrastructure, so the untrusted-execution boundary must be treated as hostile.

## 1. Trust boundary

Everything in a submission is untrusted attacker input:

| Input | How it is used | Hazard |
|---|---|---|
| `src/*.sol` | compiled by solc; **deployed and called** under `forge test` (measurement); imported into Lean and `#eval`-ed | cheatcode calls forging the oracle; resource bombs; Lean injection via the imported program |
| `test/*.t.sol` | compiled + run under `forge test` (real-behavior check) | `ffi` / cheatcodes → host RCE / forged EVM state |
| `claim.json` | drives entry call, env, fuel, observed slots | Lean string injection (names), fuel bombs, malformed shapes crashing the process |
| `foundry.toml` | **NOT trusted** — never used verbatim | `ffi=true`, `fs_permissions` |

## 2. Controls enforced in code (this repo)

These landed with the hardening pass and are exercised by `contest/run_samples.py`:

- **Cheatcode detection is address-centred, over BOTH `src/` and `test/`, before
  any Forge run** (`reject_gate.scan_cheatcodes`). The trust boundary is *any
  call to the cheatcode address* `0x7109…1D12D` (or the `"hevm cheat code"`
  seed), by any syntactic form — `vm.*`, an aliased handle
  (`CVm c = CVm(HEVM_ADDRESS); c.ffi()`), or a raw
  `address(0x7109…).call(...)`. `src/` may not reference the cheat address at
  all; `test/` may only use the env-pinning whitelist with literal args
  (mirrored into the Solidus env). Default-deny.
- **Forge runs never use the submitter's `foundry.toml`.** Both the
  real-behavior check (`harness_bridge.run_forge_test`) and the measurement
  (`measure.py`) generate a pinned profile with `ffi = false` and a minimal
  `fs_permissions` (measurement grants **write to exactly one output file,
  located OUTSIDE the project tree**; the real-behavior run grants nothing).
- **Untrusted claim fields are validated before reaching codegen**
  (`adjudicate.py`): `entry.contract` / `entry.function` must be Solidity
  identifiers (blocks Lean string-literal injection in **all** paths, including
  OVER_ACCEPT); `fuel` must be an integer in `[1, 100000]`; `entry.args` and
  `observed_slots` are shape/range-checked, returning `REJECT_MALFORMED` instead
  of crashing.
- **Inconclusive Solidus failures are not gaps.** A Lean **timeout** or
  resource-exhaustion signal is classified `NEEDS_REVIEW` (non-qualifying), never
  an automatic `COVERAGE_GAP` (a poisoned `fuel` or an OOM bomb cannot
  manufacture a leaderboard hit).
- **Timeouts** on every solc / forge / lean subprocess (`timeout` argument).

## 3. Controls that MUST be provided by the deployment (not in code)

Per-subprocess Python `rlimit`s are insufficient against a determined adversary;
the isolation boundary must be the **container / sandbox**. Before opening the
endpoint publicly, the runner MUST provide:

1. **Container isolation per submission** — a fresh, ephemeral container (or
   microVM) per adjudication, destroyed afterward. No shared writable state
   between submissions.
2. **No network egress** from the adjudication container. (Even with `ffi`
   disabled, defense in depth: solc/forge/lean should never reach the network.)
3. **Read-only root filesystem** except a per-submission scratch tmpfs with a
   **disk quota**; the submission and all generated files live only there.
4. **Resource quotas**: memory limit, CPU/pids limit, and a **wall-clock kill**
   above the per-tool timeout. Lean `#eval` and `forge` are the expensive steps;
   cap both.
5. **Rate-limiting / queueing** per identity — each submission is a full
   solc+forge+lean build and is a cheap amplification target.
6. **Pinned tool versions by digest.** solc 0.8.35, a fixed forge build, and the
   built Lean toolchain must be pinned by container image digest — the canonical
   env (`contest/env.py`) was *measured* against specific builds and Foundry
   default drift silently moves the oracle.
7. **Human review of `NEEDS_REVIEW`** (and of any component the comparator routes
   to review, e.g. custom-error reverts) before it is shown as a leaderboard
   result.

## 4. Residual precision limits (documented, not security holes)

- **Custom-error reverts**: the EVM side decodes an unknown selector to
  `revert|raw:0x…` while Solidus renders `revert|custom:Name:…`; such a
  comparison is routed to review, not auto-classified.
- **Coarse function-level taint** in the semantic exclusion detectors (§1.2) errs
  toward OOS (may over-reject, never under-rejects into a fake gap).

## 5. Pre-public checklist

- [ ] §3 container isolation + quotas + no-egress in place.
- [ ] Tool versions pinned by image digest; `env.py` re-measured against them.
- [ ] Known-gaps registry (`known_gaps.py`) loaded with every internally-known
      open divergence, so day-one submissions of known gaps dedup.
- [ ] `NEEDS_REVIEW` / review-routed components have a human queue.
- [ ] At least one **real** (un-simulated) gap per lane driven end-to-end.
