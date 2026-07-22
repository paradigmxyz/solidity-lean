# Testing a divergence submission locally

This directory is a **self-contained** copy of the divergence-contest harness:
the reject gate, the adjudicator, the observable extractor/comparator, and a
suite of worked `samples/`. You can run it yourself to check a submission
*before* sending it to the contest — the adjudicator here is the same logic the
contest runs.

A **divergence** is a single Solidity program where the Lean model
(`solidity-lean`) disagrees with the reference implementation (**solc 0.8.35**
compiled + executed on a real EVM). Two qualifying kinds in v1:

| Lane | Verdict | Meaning |
|---|---|---|
| **S** | `SOUNDNESS_GAP` | solc **rejects** the program but solidity-lean **accepts** and runs it (over-accept), OR both accept but solidity-lean computes a **wrong observable** (wrong-value / wrong-revert). |
| **C** | `COVERAGE_GAP` | solc **accepts** and runs the program but solidity-lean **fails closed** (over-reject / missing feature). |

Anything else (`NO_DIVERGENCE`, `REJECTED_OOS`, `REJECT_MALFORMED`, `INVALID`)
does **not** qualify; the adjudicator prints the specific reason.

## Prerequisites

1. **Build the Lean model** (from the repo root):
   ```bash
   lake build
   ```
   (Installs the pinned Lean toolchain via `lean-toolchain` and builds
   `SolidCore`. First build is slow; subsequent runs are incremental.)

2. **Pinned solc 0.8.35** — the contest is defined against this exact version.
   The easiest way is [`solc-select`](https://github.com/crytic/solc-select):
   ```bash
   pipx install solc-select        # or: pip install solc-select
   solc-select install 0.8.35
   solc-select use 0.8.35          # puts a 0.8.35 `solc` on your PATH
   ```
   > ⚠️ A different solc on your PATH will silently produce wrong verdicts.
   > If `solc --version` is not `0.8.35`, either `solc-select use 0.8.35`,
   > set `SOLC=/abs/path/to/solc-0.8.35`, or pass `--solc /abs/path`.

3. **Foundry** (`forge`) — https://getfoundry.sh . `forge --version` should work.
   Set `FORGE=/abs/path/to/forge` or pass `--forge` if it isn't on your PATH.

The harness resolves each tool in this order: explicit env var
(`SOLC` / `FORGE`) → the maintainer's pinned path (ignored on your machine) →
your `PATH`. So with `solc-select use 0.8.35` + Foundry installed, it just works.

## Sanity check — run the sample suite

```bash
python -m contest.run_samples
```
This adjudicates every fixture in `samples/` and asserts each one lands on its
expected verdict (proves every classification path end-to-end on your machine).

## Adjudicate one submission

```bash
python -m contest.adjudicate path/to/submission
# tool overrides if needed:
python -m contest.adjudicate path/to/submission --solc /abs/solc-0.8.35 --forge /abs/forge
```
A qualifying divergence prints e.g.:
```
=== VERDICT: COVERAGE_GAP (lane C) | qualifies=True ===
```

Other useful entry points:
```bash
python -m contest.reject_gate path/to/*.sol      # just the in-scope reject gate
python -m contest.exclusion_register             # the out-of-scope exclusions + version
python -m contest.known_gaps                      # already-known divergences (a dup of one = REJECTED_OOS)
```

## Submission layout

```
submission/
  src/*.sol        Flattened source(s), NO `import` directives. All contracts the
                   interaction needs; v1 is a SINGLE concrete contract (libraries
                   and interfaces don't count against that — they're inlined/erased).
  test/*.t.sol     A Forge test that deploys, performs the entry interaction, and
                   asserts the REAL solc+EVM observable. Must PASS on solc 0.8.35 +
                   Foundry. Plain `require`-based assertions are fine.
  foundry.toml     Minimal profile (see any samples/*/foundry.toml).
  claim.json       Metadata (below).
```

### `claim.json`

```json
{
  "lane": "C",
  "entry": {
    "contract": "T",
    "function": "f",
    "args": [1],
    "constructor_args": [],
    "value": 0
  },
  "expected_divergence": "One or two sentences: what solc+EVM do vs what solidity-lean does, and why it diverges.",
  "declared_observable": { "kind": "return_value", "normal_form": "success|w:1" },
  "feature": "short-kebab-case-feature-name",
  "register_version_seen": "1.6.0"
}
```
- `lane` — `"S"` or `"C"` (see the table above).
- `entry` — how to invoke: the concrete `contract`, the `function`, its `args`,
  `constructor_args`, and `value` (wei). The `test/` must exercise this same
  interaction. Args cover scalars (`2`, `{"int": -8}`, `true`, `{"word": n}`,
  `{"bytes": "0x…"}`, strings) **and arrays/structs as JSON lists**
  (arbitrarily nested — validated per element/member and ABI-encoded
  type-directed, so both engines receive the same logical call). Return and
  revert channels are decoded recursively too (nested-dynamic included), and a
  **reverting constructor** is measured as the `deployrevert|…` observable —
  none of these need restructuring any more. An **external function-typed
  parameter** (register 1.6) takes a 2-element `[address, selector]` list
  (address < 2^160, selector < 2^32) — both engines receive the same
  (address, selector) pair; INSPECTING it (`.address`/`.selector`) is
  measured, CALLING it is still X-EXTCALL. A plain `.staticcall` to a
  **literal precompile address 1..10** is in scope too (answered with the
  real precompile output on both engines). Still out of scope:
  internal-function-typed / domain-unboundable parameters (X-INTFNARG),
  internal function values in the return/revert channel (X-INTFNVAL), and all
  other external calls + contract creation (X-EXTCALL — incl. plain/valued
  `.call`, delegatecall, `{gas:..}` options, and computed staticcall
  receivers) until the v2 responder.
- `declared_observable` — your *claim* of the real observable. It is only a
  misreport cross-check; the adjudicator **measures** the true EVM observable
  itself (`measure.py`), so a wrong claim can't sneak a non-divergence through.
- `feature` — a short tag for your finding.
- `register_version_seen` — the exclusion-register version you built against
  (`python -m contest.exclusion_register` prints the current one).

### Environment & cheatcodes (what the oracle pins)

The comparison uses **one canonical environment** = Foundry's real defaults
(`block.number=1`, `block.timestamp=1`, `block.chainid=31337`, basefee 0, etc.),
mirrored identically into the solidity-lean `#eval` and the Foundry measurement.
Only an allow-list of cheatcodes is permitted (with **literal** args), so the
value can be mirrored: `vm.roll/warp/chainId/fee/prevrandao`,
`vm.prank/startPrank/stopPrank`, `vm.deal`. Everything else on `vm.*`
(`store`, `load`, `mockCall`, `ffi`, `etch`, `expectRevert`, …) → submission
rejected. `console.*` logging is an ignored no-op. See `README.md` for the full
policy and the design docs under `docs/`.

## Worked examples

Every subdirectory of `samples/` is a complete, adjudicable submission — copy
the one whose lane/shape matches yours as a starting template (e.g. a lane-C
over-reject, a lane-S wrong-value, a `no_divergence` control).
