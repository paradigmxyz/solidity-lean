#!/usr/bin/env python3
"""Sample-suite runner - proves every adjudication path classifies correctly.

Runs one submission per classification and asserts the expected verdict:

  * oos_gasleft    -> REJECTED_OOS  (X-GASLEFT, hidden in a callee)   [FULL run]
  * no_divergence  -> NO_DIVERGENCE (solidity-lean agrees with solc+EVM)    [FULL run]
  * soundness (REAL) -> SOUNDNESS_GAP (lane S, wrong-value)           [FULL run +
                       one-unit fault injection at the observable boundary]
  * coverage_gap   -> COVERAGE_GAP  (lane C, solidity-lean fail-closed)     [SIMULATED
                       solidity-lean step - see below]

FULL run = the real pipeline: pinned solc + Foundry + the built solidity-lean (Lean
#eval) execute end-to-end.

Gap-testing methodology (how we test the DETECTOR without leaving bugs in
solidity-lean — the maintainer's requirement):

  1. POSITIVE CONTROL (no_divergence): a real contract, full pipeline, asserts
     the two engines AGREE. Proves the pipeline runs clean.
  2. SOUNDNESS DETECTOR (real solidity-lean run + injected delta): `no_divergence` is
     run through the ENTIRE live pipeline (real import -> typecheck -> elaborate
     -> execute -> render on the solidity-lean side; real solc+Foundry measurement on
     the EVM side), then the measured EVM observable is perturbed by ONE UNIT at
     the observable boundary (`observable.perturb_leading_value`, via the
     `_selftest_perturb_evm` seam). The comparator+classifier must then emit
     SOUNDNESS_GAP(wrong-value). This exercises the full detection path against a
     genuine solidity-lean execution while leaving solidity-lean itself BUG-FREE — the delta
     lives in the test harness, never in SolidCore.
  3. COVERAGE DETECTOR (real run + injected fail-closed): `no_divergence` is run
     through the ENTIRE live pipeline (real solc + Foundry + solidity-lean import ->
     typecheck -> execute), then a fail-closed is INJECTED at the solidity-lean result
     boundary (`_selftest_perturb_solidity_lean`) — the "inserted bug": solidity-lean fails
     closed on a solc-accepted program, exactly what a coverage gap is. The
     classifier must emit COVERAGE_GAP (lane C). Real pipeline, bug-free solidity-lean.
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
                  sim: hb.SolidityLeanResult, timeout: int = 400,
                  expect_component: str | None = None,
                  expect_duplicate: str | None = None) -> tuple[bool, str]:
    """Run the real pipeline but with run_solidity_lean_observable monkeypatched."""
    original = hb.run_solidity_lean_observable
    adj_original = adj.hb.run_solidity_lean_observable

    def fake(*_a, **_k):
        return sim

    hb.run_solidity_lean_observable = fake  # type: ignore
    adj.hb.run_solidity_lean_observable = fake  # type: ignore
    try:
        report = adj.adjudicate(SAMPLES / name, timeout=timeout)
    finally:
        hb.run_solidity_lean_observable = original  # type: ignore
        adj.hb.run_solidity_lean_observable = adj_original  # type: ignore

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
    a genuine solidity-lean execution with ZERO bugs in solidity-lean."""
    report = adj.adjudicate(
        SAMPLES / "no_divergence", timeout=timeout,
        _selftest_perturb_evm=obs.perturb_leading_value)
    comp = (report.evidence.get("comparison", {}) or {}).get("differing_component")
    ok = (report.verdict == "SOUNDNESS_GAP" and report.lane == "S"
          and comp == "wrong-value" and report.qualifies)
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"component={comp} qualifies={report.qualifies} :: {report.reason[:140]}")
    return ok, detail


def run_real_storage_selftest(timeout: int = 500) -> tuple[bool, str]:
    """REAL end-to-end BROAD-STORAGE soundness-detector test (contest #8).

    Runs `ctor_storage` through the FULL live pipeline (constructor state +
    whole-storage-map comparison, no declared slots), then injects a one-unit
    delta into the measured EVM storage map. The comparator+classifier must
    return SOUNDNESS_GAP(wrong-state). Proves the broad-storage detection path
    works over a genuine solidity-lean execution with ZERO bugs in solidity-lean."""
    report = adj.adjudicate(
        SAMPLES / "ctor_storage", timeout=timeout,
        _selftest_perturb_evm=obs.perturb_storage_slot)
    comp = (report.evidence.get("comparison", {}) or {}).get("differing_component")
    ok = (report.verdict == "SOUNDNESS_GAP" and report.lane == "S"
          and comp == "wrong-state" and report.qualifies)
    detail = (f"verdict={report.verdict} lane={report.lane} "
              f"component={comp} qualifies={report.qualifies} :: {report.reason[:140]}")
    return ok, detail


def run_real_coverage_selftest(timeout: int = 500) -> tuple[bool, str]:
    """REAL end-to-end coverage-detector test (methodology step 3, bug-injection).

    Runs `no_divergence` through the FULL live pipeline (real solc + Foundry +
    solidity-lean import/typecheck/execute), then INJECTS a fail-closed at the solidity-lean
    result boundary (the "inserted bug": solidity-lean fails closed on a solc-accepted
    program, which is exactly what a coverage gap looks like). The classifier must
    return COVERAGE_GAP (lane C). This exercises the lane-C detection path over a
    genuine pipeline run with ZERO bugs in solidity-lean — the injected fail-closed
    lives in the test harness, never in SolidCore."""
    def inject_bug(_solidity_lean: hb.SolidityLeanResult) -> hb.SolidityLeanResult:
        return hb.SolidityLeanResult(
            ok=False, stage="import", fail_closed=True, observable=None,
            message=("importer exit_1: unimplemented Solidity AST nodes present: "
                     "SelfTestInjectedCoverageProbe"),
            inconclusive=False)

    report = adj.adjudicate(SAMPLES / "no_divergence", timeout=timeout,
                            _selftest_perturb_solidity_lean=inject_bug)
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


def inconclusive_classification_unit_tests() -> tuple[bool, str]:
    """A non-zero Lean exit (after a SUCCESSFUL import) is DEFAULT-INCONCLUSIVE:
    routed to human review, never auto-minted as a COVERAGE_GAP (audit finding —
    the old allow-list FAILED OPEN on OOM-kills / empty stderr / unlisted crashes).

    A genuine program-level reject does NOT surface as a non-zero Lean exit: an
    unsupported NODE is caught at the IMPORT stage (stage="import"), and a
    typecheck/runtime reject is PRINTED as `solidity-lean-reject` (exit 0, handled by
    the observable parser). So there is no "clean lean-exit reject" case — every
    non-zero lean exit here is toolchain/resource/harness noise -> inconclusive.
    The genuine coverage-gap path is exercised by the coverage-detector REAL run."""
    checks = []
    # Previously-listed noise: still inconclusive.
    noise = [
        "error: evm-interaction: package directory not found: /x/../evm-interaction",
        "error: no such file or directory (os error 2)",
        "lake: unknown package 'SolidCore'",
        "unknown constant 'SolidCore.Solidity.Checked'",
        "(deep recursion detected)",
        "deterministic timeout reached",
    ]
    # Previously FAIL-OPEN (unlisted) -> minted a fake gap; must now be inconclusive.
    formerly_fail_open = [
        "",                                   # OOM-killer SIGKILL: empty stderr
        "Killed",                             # kernel OOM
        "No space left on device",
        "PANIC at ... libc++abi: terminating",
        "Segmentation fault (core dumped)",
        "elan: command failed",
        "some unrecognized crash text",       # arbitrary -> default inconclusive
    ]
    for msg in noise + formerly_fail_open:
        label = (msg[:24] or "<empty>")
        checks.append((label, hb.lean_failure_inconclusive(msg)))
    ok = all(v for _n, v in checks)
    detail = ", ".join(f"{n}={'ok' if v else 'BAD'}" for n, v in checks)
    return ok, detail


def hardening_unit_tests() -> tuple[bool, str]:
    """Guard the false-positive fixes from the audit (all pure-function paths)."""
    from contest import adjudicate as A
    from contest import reject_gate as G
    checks: list[tuple[str, bool]] = []

    # entry.value validation: non-int / negative / >uint256 / bool -> rejected.
    checks.append(("value-ok", A._valid_value(0) == 0 and
                   A._valid_value((1 << 256) - 1) == (1 << 256) - 1))
    checks.append(("value-bad", all(A._valid_value(v) is None
                   for v in ("abc", -1, 1 << 256, True, 1.5))))

    # run-stage executable-failure wrapper (out-of-fuel/non-termination) is the
    # ambiguous marker routed to NEEDS_REVIEW; a real import reject is not.
    checks.append(("execfail-yes", A._is_executable_failure(
        'TypeError.unsupported "checked executable contract call C"')))
    checks.append(("execfail-no", not A._is_executable_failure(
        "unimplemented nodes present: Mapping")))

    # Lean Repr un-escape reverses the revert-string asymmetry.
    checks.append(("unescape-quote",
                   hb._unescape_lean_repr('revert|error:a\\"b') == 'revert|error:a"b'))
    checks.append(("unescape-noop",
                   hb._unescape_lean_repr('success|w:0') == 'success|w:0'))
    checks.append(("unescape-dblbackslash",
                   hb._unescape_lean_repr('x\\\\n') == 'x\\n'))

    # inconclusive is now default-True (fail-closed toward review).
    checks.append(("inconclusive-default",
                   hb.lean_failure_inconclusive("") is True and
                   hb.lean_failure_inconclusive("anything") is True))

    # Obfuscated cheat-address constant expression is caught by folding.
    CHEAT = G.CHEAT_ADDR
    hexlit = lambda v: {"nodeType": "Literal", "kind": "number", "value": hex(v)}
    lit = lambda v: {"nodeType": "Literal", "kind": "number", "value": str(v)}
    obf = {"nodeType": "BinaryOperation", "operator": "+",
           "leftExpression": hexlit(CHEAT - 1), "rightExpression": lit(1)}
    checks.append(("cheat-obf", G._is_cheat_ref(obf) is True))
    checks.append(("cheat-exact", G._is_cheat_ref(hexlit(CHEAT)) is True))
    checks.append(("cheat-clean", G._is_cheat_ref(hexlit(0xDEAD)) is False))
    rt = {"nodeType": "BinaryOperation", "operator": "+",
          "leftExpression": {"nodeType": "Identifier", "name": "x"},
          "rightExpression": lit(1)}
    checks.append(("cheat-runtime", G._is_cheat_ref(rt) is False))

    # bytesN parity (round 2): EVM left-aligned head word must render to the same
    # right-aligned w: value solidity-lean emits.
    checks.append(("bytes4-align",
                   obs.render_word_for_type(0x01020304 << 224, "bytes4") == "w:16909060"))
    checks.append(("bytes1-align",
                   obs.render_word_for_type(0xAB << 248, "bytes1") == f"w:{0xAB}"))
    checks.append(("bytes32-noshift",
                   obs.render_word_for_type(0x01020304, "bytes32") == "w:16909060"))
    checks.append(("uint-unchanged",
                   obs.render_word_for_type(42, "uint256") == "w:42"))
    # function-pointer returns are out of the comparable subset.
    checks.append(("fn-return-oos",
                   adj._comparable_return_type("function () external") is False))
    checks.append(("uint-return-ok",
                   adj._comparable_return_type("uint256") is True and
                   adj._comparable_return_type("bytes4") is True))

    # Revert-channel scope (this fix): array/struct/tuple custom-error params are
    # NOT in the comparable subset (so a `wrong-revert` mismatch on them is fenced
    # to REJECTED_OOS, not a fake SOUNDNESS_GAP), while scalar params still compare.
    checks.append(("err-array-oos",
                   adj._comparable_return_type("uint256[]") is False and
                   adj._comparable_return_type("uint256[3]") is False and
                   adj._comparable_return_type("struct C.S") is False))
    checks.append(("err-scalar-ok",
                   adj._comparable_return_type("uint256") is True and
                   adj._comparable_return_type("address") is True))
    # And demonstrate the actual render mismatch the gate protects against: the EVM
    # side decodes `error E(uint256[])` with [1,2,3] via the dynamic-bytes arm to a
    # raw-bytes string, NOT Solidus's `custom:E:[w:1,w:2,w:3]` — equal behavior,
    # different string, hence out of scope.
    _sel = "aabbccdd"
    _rev = bytes.fromhex(_sel) + (0x20).to_bytes(32, "big") \
        + (3).to_bytes(32, "big") \
        + b"".join(n.to_bytes(32, "big") for n in (1, 2, 3))
    _nf = obs.evm_revert_normal_form(
        "0x" + _rev.hex(), errors={_sel: ("E", ["uint256[]"])})
    checks.append(("err-array-render-differs",
                   _nf != "revert|custom:E:[w:1,w:2,w:3]"
                   and _nf.startswith("revert|custom:E:")))

    # deal last-wins parity (this audit): a repeated vm.deal to the SAME address
    # must mirror to the SAME balance on both engines. The solidity-lean list lookup
    # is FIRST-wins while Foundry vm.deal is last-wins, so effective_deals must
    # dedup to the LAST amount per address (else a fake wrong-value SOUNDNESS_GAP).
    from contest import env as _cenv
    _ov = _cenv.EnvOverrides()
    _ov.deals = [(0xAAAA, 100), (0xBBBB, 5), (0xAAAA, 200)]
    checks.append(("deal-lastwins",
                   dict(_ov.effective_deals()) == {0xAAAA: 200, 0xBBBB: 5}))
    checks.append(("deal-lastwins-lean",
                   _ov.lean_balances() == "[(43690, 200), (48059, 5)]"))
    checks.append(("deal-empty-unchanged",
                   _cenv.EnvOverrides().effective_deals() == []))

    # bytes32 arg must be the WORD form: the {bytes} form is ABI-encoded DYNAMICALLY
    # (offset word 0x20) but a static bytes32 param reads the head word, diverging
    # from solidity-lean's Value.bytes -> a fabricated call. Word form OK; {bytes} out.
    checks.append(("bytes32-word-ok",
                   adj._arg_domain_error({"word": 0x1122}, "bytes32", {}) is None))
    checks.append(("bytes32-bytes-rejected",
                   adj._arg_domain_error({"bytes": "0x" + "11" * 32}, "bytes32", {})
                   is not None))
    # dynamic bytes/string still accept {bytes} (they ARE dynamically encoded).
    checks.append(("bytes-dyn-ok",
                   adj._arg_domain_error({"bytes": "0x1122"}, "bytes", {}) is None))

    # claim-field type confusion: a non-object claim.json / non-object entry must
    # be REJECT_MALFORMED, not an uncaught crash (audit finding).
    import tempfile as _tf, json as _json
    def _mkclaim(obj):
        d = _tf.mkdtemp(prefix="contest-load.")
        (Path(d) / "src").mkdir()
        (Path(d) / "src" / "S.sol").write_text("contract S {}")
        (Path(d) / "test").mkdir()
        (Path(d) / "claim.json").write_text(_json.dumps(obj))
        return Path(d)
    _sub1, _rep1 = adj.load_submission(_mkclaim([1, 2, 3]))
    checks.append(("claim-nonobject", _sub1 is None and
                   _rep1 is not None and _rep1.verdict == "REJECT_MALFORMED"))
    _sub2, _rep2 = adj.load_submission(_mkclaim({"lane": "S", "entry": 5}))
    checks.append(("entry-nonobject", _sub2 is None and
                   _rep2 is not None and _rep2.verdict == "REJECT_MALFORMED"))
    _sub3, _rep3 = adj.load_submission(
        _mkclaim({"lane": "S", "entry": "contract function"}))
    checks.append(("entry-string", _sub3 is None and
                   _rep3 is not None and _rep3.verdict == "REJECT_MALFORMED"))

    # Advisory delta-shape cluster hint (dedup-evasion mitigation): a KNOWN lane-S
    # over_accept gap (G2..G12 all share component=over_accept, delta=over-accept)
    # re-skinned with a NOVEL feature dodges match_relaxed but must still surface in
    # cluster_by_delta — WITHOUT being auto-marked duplicate_of (delta over-clusters).
    _cluster = kg.cluster_by_delta("S", "over_accept", "over-accept")
    checks.append(("delta-cluster-nonempty",
                   len(_cluster) >= 2 and "G2" in _cluster))
    # It is advisory-only: match on a novel feature token returns no exact/relaxed hit.
    checks.append(("reskin-dodges-relaxed",
                   kg.match_relaxed("S", "totally-novel-feature-string") is None))
    # And a genuinely novel delta family clusters to nothing.
    checks.append(("novel-delta-empty",
                   kg.cluster_by_delta("S", "return_value", "no-such-delta") == []))
    # Lane C never produces a delta cluster (its middle token is adjudicator-derived).
    checks.append(("laneC-no-cluster",
                   kg.cluster_by_delta("C", "typecheck", "over_reject") == []))

    ok = all(v for _n, v in checks)
    detail = ", ".join(f"{n}={'ok' if v else 'BAD'}" for n, v in checks)
    return ok, detail


def main() -> int:
    results: list[tuple[str, bool, str]] = []

    # --- unit-level checks (fast) ---
    ok, d = observable_unit_tests()
    results.append(("observable-comparator (unit)", ok, d))
    _print("observable-comparator (unit)", ok, d)

    ok, d = inconclusive_classification_unit_tests()
    results.append(("inconclusive-classification (unit)", ok, d))
    _print("inconclusive-classification (unit)", ok, d)

    ok, d = dedup_unit_tests()
    results.append(("dedup-fingerprints (unit)", ok, d))
    _print("dedup-fingerprints (unit)", ok, d)

    ok, d = hardening_unit_tests()
    results.append(("false-positive-hardening (unit)", ok, d))
    _print("false-positive-hardening (unit)", ok, d)

    # --- FULL end-to-end runs (real solc + Foundry + solidity-lean/Lean) ---
    # REAL detector tests: full live pipeline + fault injection at the result
    # boundary (methodology steps 2 & 3). No bug in solidity-lean.
    ok, d = run_real_soundness_selftest()
    results.append(("soundness-detector (REAL run + injected delta)", ok, d))
    _print("soundness-detector (REAL run + injected delta)", ok, d)

    ok, d = run_real_coverage_selftest()
    results.append(("coverage-detector (REAL run + injected fail-closed)", ok, d))
    _print("coverage-detector (REAL run + injected fail-closed)", ok, d)

    ok, d = run_real_storage_selftest()
    results.append(("storage-detector (REAL run + injected slot delta)", ok, d))
    _print("storage-detector (REAL run + injected slot delta)", ok, d)

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

    # scalar custom-error revert parity (audit round 3 left the scalar path only
    # unit-tested): f() reverts with `Bad(42, true)` (uint256 + bool, both in the
    # faithfully-comparable ABI subset, so X-RETABI does NOT fire). Both engines
    # render `revert|custom:Bad:w:42,w:1` -> NO_DIVERGENCE (proves the scalar
    # custom-error revert compares end-to-end, not a fabricated wrong-revert gap).
    ok, d = run_full("custom_error_scalar", "NO_DIVERGENCE")
    results.append(("custom_error_scalar revert parity (FULL)", ok, d))
    _print("custom_error_scalar revert parity (FULL)", ok, d)

    # events + storage parity control: emits an event + writes storage; solidity-lean
    # and solc+EVM must agree on event topics/data and observed slots.
    ok, d = run_full("events_storage", "NO_DIVERGENCE")
    results.append(("events_storage parity (FULL)", ok, d))
    _print("events_storage parity (FULL)", ok, d)

    # constructor state + BROAD storage auto-detection (contest #8): the entry
    # call runs against the post-construction state (initializer + ctor writes),
    # and the WHOLE storage map — including a mapping's hashed slot — is compared
    # on both engines with NO submitter-declared observed_slots.
    ok, d = run_full("ctor_storage", "NO_DIVERGENCE")
    results.append(("ctor_storage broad-storage (FULL)", ok, d))
    _print("ctor_storage broad-storage (FULL)", ok, d)

    # constructor ARGUMENTS: both engines deploy with the same decoded args
    # (EVM appends to creationCode; solidity-lean -> constructWithContext).
    ok, d = run_full("ctor_args", "NO_DIVERGENCE")
    results.append(("ctor_args (FULL)", ok, d))
    _print("ctor_args (FULL)", ok, d)

    # regression: msg.sender inside the constructor must be the canonical sender
    # on both engines (the EVM deploy is pranked), not the test-harness address.
    ok, d = run_full("ctor_msg_sender", "NO_DIVERGENCE")
    results.append(("ctor_msg_sender (FULL)", ok, d))
    _print("ctor_msg_sender (FULL)", ok, d)

    # regression: `new T[](n)` / `new bytes(n)` are memory allocations, NOT
    # external creations — X-EXTCALL must not fire (returns a scalar -> compared).
    ok, d = run_full("mem_alloc", "NO_DIVERGENCE")
    results.append(("mem_alloc (FULL)", ok, d))
    _print("mem_alloc (FULL)", ok, d)

    # array return type is outside the comparable ABI subset -> REJECTED_OOS.
    ok, d = run_full("array_return", "REJECTED_OOS")
    results.append(("array_return X-RETABI (FULL)", ok, d))
    _print("array_return X-RETABI (FULL)", ok, d)

    # bytesN (N<32) return parity (audit round 2): a bytes4 return must classify
    # NO_DIVERGENCE, not a fake SOUNDNESS_GAP from EVM left- vs Lean right-alignment.
    ok, d = run_full("bytesn_return", "NO_DIVERGENCE")
    results.append(("bytesn_return parity (FULL)", ok, d))
    _print("bytesn_return parity (FULL)", ok, d)

    # mixed-scalar multi-return differential probe (round 8): a single tuple return
    # of int256/uint128/address/bytes4 must render identically on both engines
    # (i:-7,w:42,w:4660,w:2864434397) -> NO_DIVERGENCE. Exercises signed-int,
    # sub-256 uint, address, and bytesN rendering TOGETHER (no other sample does).
    ok, d = run_full("multi_return", "NO_DIVERGENCE")
    results.append(("multi_return mixed-scalar parity (FULL)", ok, d))
    _print("multi_return mixed-scalar parity (FULL)", ok, d)

    # mapping-slot + indexed-event differential probe (round 9): deposit() writes
    # balances[0x1234]=100 and emits Deposit(indexed who, amount). Both engines must
    # agree on the keccak-derived mapping slot AND the indexed/non-indexed event
    # topics/data -> NO_DIVERGENCE (keccak storage-slot + event parity).
    ok, d = run_full("map_event", "NO_DIVERGENCE")
    results.append(("map_event mapping+event parity (FULL)", ok, d))
    _print("map_event mapping+event parity (FULL)", ok, d)

    # delimiter-laden string-return probe (round 10): f() returns "a|b:c##EVT##d".
    # Both engines must HEX-encode it (b:0x617c623a632323455654232364) so the
    # embedded |/:/##EVT## cannot desync the comparator, and solidity-lean must
    # model the string as Value.bytes (not the r: reprStr fallback) -> NO_DIVERGENCE.
    ok, d = run_full("string_return", "NO_DIVERGENCE")
    results.append(("string_return delimiter-safety (FULL)", ok, d))
    _print("string_return delimiter-safety (FULL)", ok, d)

    # fabricated gap: args count != function param count -> REJECT_MALFORMED,
    # NOT a qualifying COVERAGE_GAP from Solidus failing closed on the bad call.
    ok, d = run_full("arg_count_mismatch", "REJECT_MALFORMED")
    results.append(("arg_count_mismatch (FULL)", ok, d))
    _print("arg_count_mismatch (FULL)", ok, d)

    # fabricated gap: an out-of-domain scalar arg (dirty bool) -> REJECT_MALFORMED.
    ok, d = run_full("arg_domain", "REJECT_MALFORMED")
    results.append(("arg_domain (FULL)", ok, d))
    _print("arg_domain (FULL)", ok, d)

    # --- ATTACK samples (v1.1 hardening; must now be caught) ---------------
    # P0 #1: a lying declared observable -> adjudication uses the MEASURED EVM
    # observable (== solidity-lean) -> NO_DIVERGENCE, NOT a fake SOUNDNESS_GAP.
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
    # solidity-lean env -> both see 12345 -> NO_DIVERGENCE (correct verdict).
    ok, d = run_full("cheatcode_allowed", "NO_DIVERGENCE")
    results.append(("cheatcode_allowed ALLOWED (FULL)", ok, d))
    _print("cheatcode_allowed ALLOWED (FULL)", ok, d)

    # Round 11 probe: checked uint256 overflow (2^256-1 + 1) must revert with
    # Panic(0x11) on BOTH engines -> revert|panic:17 -> NO_DIVERGENCE. Guards
    # panic-code parity so a code mismatch can't bank a fake wrong-revert gap.
    ok, d = run_full("panic_overflow", "NO_DIVERGENCE")
    results.append(("panic_overflow PARITY (FULL)", ok, d))
    _print("panic_overflow PARITY (FULL)", ok, d)

    # Round 12 probe: checked division by zero (f(1,0)) must revert with
    # Panic(0x12) -> revert|panic:18 on BOTH engines. A DISTINCT panic code from
    # the overflow probe -> confirms per-operation panic-code parity, not just 0x11.
    ok, d = run_full("panic_divzero", "NO_DIVERGENCE")
    results.append(("panic_divzero PARITY (FULL)", ok, d))
    _print("panic_divzero PARITY (FULL)", ok, d)

    # Round 13 probe: array out-of-bounds read (f(5) on a length-2 storage array)
    # must revert with Panic(0x32) -> revert|panic:50 on BOTH engines. A NON-
    # arithmetic panic path (bounds check) + a constructor-populated dynamic
    # storage array read -> confirms panic-code parity generalizes beyond math.
    ok, d = run_full("panic_oob", "NO_DIVERGENCE")
    results.append(("panic_oob PARITY (FULL)", ok, d))
    _print("panic_oob PARITY (FULL)", ok, d)

    # Round 14 probe: a failing assert() (f(0) fails assert(a != 0)) must revert
    # with Panic(0x01) -> revert|panic:1 on BOTH engines. The assertion-failure
    # code path -> confirms it renders as Panic(0x01), NOT Error(string)/empty.
    ok, d = run_full("panic_assert", "NO_DIVERGENCE")
    results.append(("panic_assert PARITY (FULL)", ok, d))
    _print("panic_assert PARITY (FULL)", ok, d)

    # Round 15 probe: payable entry called with msg.value. entry.value=1000 flows
    # into BOTH the Foundry call{value:...} and the mirrored solidity-lean env ->
    # f() returns msg.value -> success|w:1000 on BOTH. Guards the value channel:
    # a wei desync (wrong/zero value on one side) would be a fake wrong-value gap.
    ok, d = run_full("payable_value", "NO_DIVERGENCE")
    results.append(("payable_value PARITY (FULL)", ok, d))
    _print("payable_value PARITY (FULL)", ok, d)

    print("\n=== SUMMARY ===")
    all_ok = True
    for name, ok, _d in results:
        all_ok = all_ok and ok
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
    print(f"\n{'ALL SAMPLES CLASSIFIED CORRECTLY' if all_ok else 'SOME SAMPLES FAILED'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
