#!/usr/bin/env python3
"""Sample-suite runner - proves every adjudication path classifies correctly.

Runs one submission per classification and asserts the expected verdict:

  * oos_gasleft    -> REJECTED_OOS  (X-GASLEFT, hidden in a callee)   [FULL run]
  * no_divergence  -> NO_DIVERGENCE (Solidus agrees with solc+EVM)    [FULL run]
  * coverage_gap   -> COVERAGE_GAP  (lane C, Solidus fail-closed)     [SIMULATED
                       Solidus step - see below]
  * soundness_gap  -> SOUNDNESS_GAP (lane S, wrong-value)             [SIMULATED
                       Solidus step - see below]

FULL run = the real pipeline: pinned solc + Foundry + the built Solidus (Lean
#eval) execute end-to-end.

SIMULATED Solidus step = the real STRUCTURE + REAL-BEHAVIOR (Forge) + REJECT GATE
run against pinned solc/Foundry, but `harness_bridge.run_solidus_observable` is
monkeypatched to return a simulated Solidus result. This is necessary and
honest: the live coverage/soundness gaps that would drive these branches are
being FIXED on sibling branches, so there is no live gap to point at. The
simulation exercises the exact classifier decision tree (adjudicate steps 3a/3c)
with a representative fail-closed / mismatching Solidus observable. Clearly
marked here and in each sample's claim.json ("synthetic": true).

Also unit-tests the dedup fingerprint machinery (§6.2) against the pre-loaded
G-register.
"""

from __future__ import annotations

import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parent
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from contest import adjudicate as adj
from contest import harness_bridge as hb
from contest import known_gaps as kg
from contest import observable as obs


SAMPLES = _HERE / "samples"


def _print(name: str, ok: bool, detail: str) -> None:
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}: {detail}")


def run_full(name: str, expected_verdict: str, timeout: int = 500) -> tuple[bool, str]:
    report = adj.adjudicate(SAMPLES / name, timeout=timeout)
    ok = report.verdict == expected_verdict
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"pays_out={report.pays_out} :: {report.reason[:160]}")
    return ok, detail


def run_simulated(name: str, expected_verdict: str, expected_lane: str,
                  sim: hb.SolidusResult, timeout: int = 400,
                  expect_component: str | None = None,
                  expect_duplicate: str | None = None) -> tuple[bool, str]:
    """Run the real pipeline but with run_solidus_observable monkeypatched."""
    original = hb.run_solidus_observable
    adj_original = adj.hb.run_solidus_observable

    def fake(*_a, **_k):
        return sim

    hb.run_solidus_observable = fake  # type: ignore
    adj.hb.run_solidus_observable = fake  # type: ignore
    try:
        report = adj.adjudicate(SAMPLES / name, timeout=timeout)
    finally:
        hb.run_solidus_observable = original  # type: ignore
        adj.hb.run_solidus_observable = adj_original  # type: ignore

    ok = report.verdict == expected_verdict and report.lane == expected_lane
    if expect_component is not None:
        comp = (report.evidence.get("comparison", {}) or {}).get("differing_component")
        ok = ok and comp == expect_component
    if expect_duplicate is not None:
        ok = ok and report.duplicate_of == expect_duplicate
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"pays_out={report.pays_out} dup={report.duplicate_of} "
              f"fp={report.fingerprint} :: {report.reason[:160]}")
    return ok, detail


def dedup_unit_tests() -> tuple[bool, str]:
    """Directly exercise the dedup fingerprint machinery (§6.2)."""
    checks = []
    # A live G1-shaped wrong-value soundness gap must dedup to G1.
    key_g1 = ("return_value", "using-operator-nonbuiltin-body", "wrong-value")
    checks.append(("G1 exact", kg.match_fingerprint("S", key_g1) is not None
                   and kg.match_fingerprint("S", key_g1).id == "G1"))
    # A G13-shaped over-reject coverage gap must dedup to G13.
    key_g13 = ("typecheck", "over_reject", "nested-tuple-LHS")
    checks.append(("G13 exact", kg.match_fingerprint("C", key_g13) is not None
                   and kg.match_fingerprint("C", key_g13).id == "G13"))
    # A novel fingerprint must NOT match anything.
    key_novel = ("import", "unimplemented", "TotallyNovelNodeXYZ")
    checks.append(("novel unmatched", kg.match_fingerprint("C", key_novel) is None))
    # Relaxed (cluster-hint) match by feature token.
    checks.append(("G1 relaxed", kg.match_relaxed("S", "using-operator-nonbuiltin-body")
                   is not None))
    ok = all(v for _n, v in checks)
    detail = ", ".join(f"{n}={'ok' if v else 'BAD'}" for n, v in checks)
    return ok, detail


def observable_unit_tests() -> tuple[bool, str]:
    """Exercise the observable comparator directly (§3.4)."""
    checks = []
    a = obs.parse_observable("success|w:5")
    b = obs.parse_observable("success|w:5")
    c = obs.parse_observable("success|w:6")
    checks.append(("equal", obs.compare_observables(a, b).equal))
    diff = obs.compare_observables(a, c)
    checks.append(("wrong-value", not diff.equal
                   and diff.differing_component == "wrong-value"))
    rv = obs.compare_observables(obs.parse_observable("success|w:0"),
                                 obs.parse_observable("revert|panic:17"))
    checks.append(("revert-vs-success", rv.differing_component == "revert-vs-success"))
    ok = all(v for _n, v in checks)
    detail = ", ".join(f"{n}={'ok' if v else 'BAD'}" for n, v in checks)
    return ok, detail


def main() -> int:
    results: list[tuple[str, bool, str]] = []

    # --- unit-level checks (fast) ---
    ok, d = observable_unit_tests()
    results.append(("observable-comparator (unit)", ok, d))
    _print("observable-comparator (unit)", ok, d)

    ok, d = dedup_unit_tests()
    results.append(("dedup-fingerprints (unit)", ok, d))
    _print("dedup-fingerprints (unit)", ok, d)

    # --- SIMULATED-Solidus classifier paths (real gate + forge) ---
    cov_sim = hb.SolidusResult(
        ok=False, stage="import", fail_closed=True, observable=None,
        message="importer exit_1: unimplemented Solidity AST nodes present: "
                "SyntheticUnsupportedNode")
    ok, d = run_simulated("coverage_gap", "COVERAGE_GAP", "C", cov_sim)
    results.append(("coverage_gap (SIMULATED Solidus)", ok, d))
    _print("coverage_gap (SIMULATED Solidus)", ok, d)

    snd_sim = hb.SolidusResult(
        ok=True, stage="run", fail_closed=False,
        observable=obs.parse_observable("success|w:999"),
        message="ran to completion")
    ok, d = run_simulated("soundness_gap", "SOUNDNESS_GAP", "S", snd_sim,
                          expect_component="wrong-value")
    results.append(("soundness_gap (SIMULATED Solidus)", ok, d))
    _print("soundness_gap (SIMULATED Solidus)", ok, d)

    # --- FULL end-to-end runs (real solc + Foundry + Solidus/Lean) ---
    ok, d = run_full("oos_gasleft", "REJECTED_OOS")
    results.append(("oos_gasleft (FULL)", ok, d))
    _print("oos_gasleft (FULL)", ok, d)

    ok, d = run_full("no_divergence", "NO_DIVERGENCE")
    results.append(("no_divergence (FULL)", ok, d))
    _print("no_divergence (FULL)", ok, d)

    print("\n=== SUMMARY ===")
    all_ok = True
    for name, ok, _d in results:
        all_ok = all_ok and ok
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
    print(f"\n{'ALL SAMPLES CLASSIFIED CORRECTLY' if all_ok else 'SOME SAMPLES FAILED'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
