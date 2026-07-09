#!/usr/bin/env python3
"""Sample-suite runner - proves every adjudication path classifies correctly.

Runs one submission per classification and asserts the expected verdict:

  * oos_gasleft    -> REJECTED_OOS  (X-GASLEFT, hidden in a callee)   [FULL run]
  * no_divergence  -> NO_DIVERGENCE (Solidus agrees with solc+EVM)    [FULL run]
  * soundness (REAL) -> SOUNDNESS_GAP (lane S, wrong-value)           [FULL run +
                       one-unit fault injection at the observable boundary]
  * coverage_gap   -> COVERAGE_GAP  (lane C, Solidus fail-closed)     [SIMULATED
                       Solidus step - see below]

FULL run = the real pipeline: pinned solc + Foundry + the built Solidus (Lean
#eval) execute end-to-end.

Gap-testing methodology (how we test the DETECTOR without leaving bugs in
Solidus — the maintainer's requirement):

  1. POSITIVE CONTROL (no_divergence): a real contract, full pipeline, asserts
     the two engines AGREE. Proves the pipeline runs clean.
  2. SOUNDNESS DETECTOR (real Solidus run + injected delta): `no_divergence` is
     run through the ENTIRE live pipeline (real import -> typecheck -> elaborate
     -> execute -> render on the Solidus side; real solc+Foundry measurement on
     the EVM side), then the measured EVM observable is perturbed by ONE UNIT at
     the observable boundary (`observable.perturb_leading_value`, via the
     `_selftest_perturb_evm` seam). The comparator+classifier must then emit
     SOUNDNESS_GAP(wrong-value). This exercises the full detection path against a
     genuine Solidus execution while leaving Solidus itself BUG-FREE — the delta
     lives in the test harness, never in SolidCore.
  3. COVERAGE DETECTOR (real run + injected fail-closed): `no_divergence` is run
     through the ENTIRE live pipeline (real solc + Foundry + Solidus import ->
     typecheck -> execute), then a fail-closed is INJECTED at the Solidus result
     boundary (`_selftest_perturb_solidus`) — the "inserted bug": Solidus fails
     closed on a solc-accepted program, exactly what a coverage gap is. The
     classifier must emit COVERAGE_GAP (lane C). Real pipeline, bug-free Solidus.
     When a genuine open importer/over-reject gap is available it can be pinned as
     a fixture whose expected verdict FLIPS to NO_DIVERGENCE once fixed (via the
     known-fixed list) — so a real bug is never kept alive just to test detection.

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
              f"qualifies={report.qualifies} :: {report.reason[:160]}")
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
              f"qualifies={report.qualifies} dup={report.duplicate_of} "
              f"fp={report.fingerprint} :: {report.reason[:160]}")
    return ok, detail


def run_real_soundness_selftest(timeout: int = 500) -> tuple[bool, str]:
    """REAL end-to-end soundness-detector test (methodology step 2).

    Runs `no_divergence` through the FULL live pipeline, then injects a one-unit
    delta into the measured EVM observable. The full comparator+classifier must
    return SOUNDNESS_GAP(wrong-value). This proves the detection path works over
    a genuine Solidus execution with ZERO bugs in Solidus."""
    report = adj.adjudicate(
        SAMPLES / "no_divergence", timeout=timeout,
        _selftest_perturb_evm=obs.perturb_leading_value)
    comp = (report.evidence.get("comparison", {}) or {}).get("differing_component")
    ok = (report.verdict == "SOUNDNESS_GAP" and report.lane == "S"
          and comp == "wrong-value" and report.qualifies)
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"component={comp} qualifies={report.qualifies} :: {report.reason[:140]}")
    return ok, detail


def run_real_coverage_selftest(timeout: int = 500) -> tuple[bool, str]:
    """REAL end-to-end coverage-detector test (methodology step 3, bug-injection).

    Runs `no_divergence` through the FULL live pipeline (real solc + Foundry +
    Solidus import/typecheck/execute), then INJECTS a fail-closed at the Solidus
    result boundary (the "inserted bug": Solidus fails closed on a solc-accepted
    program, which is exactly what a coverage gap looks like). The classifier must
    return COVERAGE_GAP (lane C). This exercises the lane-C detection path over a
    genuine pipeline run with ZERO bugs in Solidus — the injected fail-closed
    lives in the test harness, never in SolidCore."""
    def inject_bug(_solidus: hb.SolidusResult) -> hb.SolidusResult:
        return hb.SolidusResult(
            ok=False, stage="import", fail_closed=True, observable=None,
            message=("importer exit_1: unimplemented Solidity AST nodes present: "
                     "SelfTestInjectedCoverageProbe"),
            inconclusive=False)

    report = adj.adjudicate(SAMPLES / "no_divergence", timeout=timeout,
                            _selftest_perturb_solidus=inject_bug)
    ok = (report.verdict == "COVERAGE_GAP" and report.lane == "C"
          and report.qualifies)
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"qualifies={report.qualifies} fp={report.fingerprint} "
              f":: {report.reason[:140]}")
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

    # --- FULL end-to-end runs (real solc + Foundry + Solidus/Lean) ---
    # REAL detector tests: full live pipeline + fault injection at the result
    # boundary (methodology steps 2 & 3). No bug in Solidus.
    ok, d = run_real_soundness_selftest()
    results.append(("soundness-detector (REAL run + injected delta)", ok, d))
    _print("soundness-detector (REAL run + injected delta)", ok, d)

    ok, d = run_real_coverage_selftest()
    results.append(("coverage-detector (REAL run + injected fail-closed)", ok, d))
    _print("coverage-detector (REAL run + injected fail-closed)", ok, d)

    ok, d = run_full("oos_gasleft", "REJECTED_OOS")
    results.append(("oos_gasleft (FULL)", ok, d))
    _print("oos_gasleft (FULL)", ok, d)

    ok, d = run_full("no_divergence", "NO_DIVERGENCE")
    results.append(("no_divergence (FULL)", ok, d))
    _print("no_divergence (FULL)", ok, d)

    # X-EXTCALL: external calls are unmodeled in v1 -> REJECTED_OOS (not a gap).
    ok, d = run_full("external_call", "REJECTED_OOS")
    results.append(("external_call OOS (FULL)", ok, d))
    _print("external_call OOS (FULL)", ok, d)

    # events + storage parity control: emits an event + writes storage; Solidus
    # and solc+EVM must agree on event topics/data and observed slots.
    ok, d = run_full("events_storage", "NO_DIVERGENCE")
    results.append(("events_storage parity (FULL)", ok, d))
    _print("events_storage parity (FULL)", ok, d)

    # --- ATTACK samples (v1.1 hardening; must now be caught) ---------------
    # P0 #1: a lying declared observable -> adjudication uses the MEASURED EVM
    # observable (== Solidus) -> NO_DIVERGENCE, NOT a fake SOUNDNESS_GAP.
    ok, d = run_full("fake_oracle", "NO_DIVERGENCE")
    results.append(("fake_oracle ATTACK (FULL)", ok, d))
    _print("fake_oracle ATTACK (FULL)", ok, d)

    # P0 #2: entry returns block.timestamp -> env PINNED on both sides ->
    # NO_DIVERGENCE (not a spurious env wrong-value).
    ok, d = run_full("env_divergence", "NO_DIVERGENCE")
    results.append(("env_divergence ATTACK (FULL)", ok, d))
    _print("env_divergence ATTACK (FULL)", ok, d)

    # P0 #2: entry returns blockhash(0) -> unpinnable env fact -> REJECTED_OOS
    # (SEM-ENV), not a spurious SOUNDNESS_GAP.
    ok, d = run_full("env_blockhash", "REJECTED_OOS")
    results.append(("env_blockhash ATTACK (FULL)", ok, d))
    _print("env_blockhash ATTACK (FULL)", ok, d)

    # P0 #3: test forges storage via vm.store -> banned cheatcode -> REJECTED.
    ok, d = run_full("cheatcode_banned", "REJECTED_OOS")
    results.append(("cheatcode_banned ATTACK (FULL)", ok, d))
    _print("cheatcode_banned ATTACK (FULL)", ok, d)

    # P0 #3: test pins timestamp via vm.warp -> allowed + MIRRORED into the
    # Solidus env -> both see 12345 -> NO_DIVERGENCE (correct verdict).
    ok, d = run_full("cheatcode_allowed", "NO_DIVERGENCE")
    results.append(("cheatcode_allowed ALLOWED (FULL)", ok, d))
    _print("cheatcode_allowed ALLOWED (FULL)", ok, d)

    print("\n=== SUMMARY ===")
    all_ok = True
    for name, ok, _d in results:
        all_ok = all_ok and ok
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
    print(f"\n{'ALL SAMPLES CLASSIFIED CORRECTLY' if all_ok else 'SOME SAMPLES FAILED'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
