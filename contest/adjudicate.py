#!/usr/bin/env python3
"""Adjudicator - the two-lane decision tree (design §4) and CLI entrypoint.

    python -m contest.adjudicate <submission-dir>

A submission directory (design §5.1):

    submission/
      src/*.sol              flattened source(s), NO import directives
      test/*.t.sol           a Forge test asserting the REAL solc+EVM behavior
      foundry.toml           minimal Foundry project config
      claim.json             { lane, entry:{contract,function,args,value},
                               expected_divergence, declared_observable, ... }

Decision tree (halt at first terminal verdict):

  0. STRUCTURE CHECK           -> REJECT_MALFORMED on missing pieces
  1. REAL-BEHAVIOR CHECK       -> INVALID if the Forge test does not PASS
     1a. OVER_ACCEPT sub-case  -> solc must REJECT (skip Forge)
  2. REJECT GATE (§2)          -> REJECTED_OOS on any exclusion hit
  3. RUN SOLIDUS + CLASSIFY:
     (a) fail-closed, solc ran -> COVERAGE_GAP (lane C)  [missing-feature/over-reject]
     (b) OVER_ACCEPT + Solidus runs solc-rejected prog -> SOUNDNESS_GAP (lane S)
     (c) Solidus runs, observable EQUAL   -> NO_DIVERGENCE
                          observable DIFFERS -> SOUNDNESS_GAP (lane S)
  + DEDUP (§6): terminal gaps get a root-cause fingerprint; a match against the
    known-open-gaps list => DUPLICATE annotation.

Qualifying verdicts (count for the leaderboard): COVERAGE_GAP (lane C),
SOUNDNESS_GAP (lane S). Everything else (INVALID, REJECTED_OOS, NO_DIVERGENCE,
REJECT_MALFORMED) does not qualify and returns the specific reason.

This is a for-fun contest: qualifying submissions earn a place on the public
leaderboard.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from . import env as cenv
from . import exclusion_register as reg
from . import harness_bridge as hb
from . import known_gaps as kg
from . import measure as meas
from . import observable as obs
from . import reject_gate as gate


NAMESPACE_PREFIX = "SolidCore.Solidity.SolcAstImport.Contest"


# ---------------------------------------------------------------------------
# Verdict container
# ---------------------------------------------------------------------------

@dataclass
class Report:
    verdict: str
    lane: Optional[str] = None           # "C" | "S" | None
    reason: str = ""
    evidence: dict[str, Any] = field(default_factory=dict)
    fingerprint: Optional[dict[str, Any]] = None
    duplicate_of: Optional[str] = None
    register_version: str = reg.REGISTER_VERSION
    known_gaps_version: str = kg.KNOWN_GAPS_VERSION

    @property
    def qualifies(self) -> bool:
        """True if this verdict counts for the leaderboard (a real gap)."""
        return self.verdict in ("COVERAGE_GAP", "SOUNDNESS_GAP")

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "verdict": self.verdict,
            "lane": self.lane,
            "reason": self.reason,
            "qualifies": self.qualifies,
            "register_version": self.register_version,
            "known_gaps_version": self.known_gaps_version,
            "evidence": self.evidence,
        }
        if self.fingerprint is not None:
            d["fingerprint"] = self.fingerprint
        if self.duplicate_of is not None:
            d["duplicate_of"] = self.duplicate_of
        return d


# ---------------------------------------------------------------------------
# Submission loading (step 0)
# ---------------------------------------------------------------------------

@dataclass
class Submission:
    root: Path
    claim: dict[str, Any]
    sources: list[Path]
    forge_root: Path


def load_submission(root: Path) -> tuple[Optional[Submission], Optional[Report]]:
    if not root.is_dir():
        return None, Report("REJECT_MALFORMED",
                            reason=f"submission dir not found: {root}")
    claim_path = root / "claim.json"
    if not claim_path.is_file():
        return None, Report("REJECT_MALFORMED", reason="missing claim.json")
    try:
        claim = json.loads(claim_path.read_text())
    except json.JSONDecodeError as exc:
        return None, Report("REJECT_MALFORMED", reason=f"claim.json invalid JSON: {exc}")

    src_dir = root / "src"
    sources = sorted(src_dir.glob("*.sol")) if src_dir.is_dir() else []
    if not sources:
        return None, Report("REJECT_MALFORMED", reason="no src/*.sol sources")

    if not (root / "test").is_dir() and claim.get("lane") != "S":
        # lane S OVER_ACCEPT may legitimately have no runnable test (solc rejects)
        if not claim.get("_over_accept"):
            return None, Report("REJECT_MALFORMED", reason="missing test/ directory")

    for key in ("lane", "entry"):
        if key not in claim:
            return None, Report("REJECT_MALFORMED", reason=f"claim.json missing '{key}'")
    entry = claim["entry"]
    for key in ("contract", "function"):
        if key not in entry:
            return None, Report("REJECT_MALFORMED", reason=f"claim.entry missing '{key}'")
    if claim["lane"] not in ("C", "S"):
        return None, Report("REJECT_MALFORMED", reason="claim.lane must be 'C' or 'S'")

    return Submission(root=root, claim=claim, sources=sources, forge_root=root), None


# ---------------------------------------------------------------------------
# Fingerprint of a terminal verdict (§6.2)
# ---------------------------------------------------------------------------

def coverage_fingerprint(solidus: hb.SolidusResult) -> tuple:
    """lane C: (fail_stage, fail_reason_class, minimal_node_type_or_field)."""
    stage = solidus.stage  # import | lean | run
    msg = solidus.message
    if stage == "import":
        # classify the importer fail() reason (design §2)
        if "unimplemented" in msg:
            reason_class = "unimplemented"
        elif "unclassified" in msg:
            reason_class = "unclassified"
        elif "unknown" in msg:
            reason_class = "unknown_scalar"
        elif "excluded" in msg:
            reason_class = "excluded"  # register/importer drift bug (§2)
        else:
            reason_class = "import_fail"
        token = _first_token(msg)
        return (stage, reason_class, token)
    if stage == "run":
        return ("typecheck", "over_reject", _first_token(msg))
    return ("elaboration", "elab_reject", _first_token(msg))


def _first_token(msg: str) -> str:
    """Extract a STABLE, collision-resistant node-type/field identity from a fail
    message (review D-2).

    Importer fail() messages have the shape
        "... nodes present: NodeA, NodeB"
        "... child fields present: Parent.field"
    Rather than take only the first word (which collides when two different gaps
    both bottom out in, say, `Mapping`, and is order-sensitive when solc lists
    several nodes), we collect ALL tokens after the last "present:", keep dotted
    field paths intact, dedupe and SORT them, and join — so the identity is
    deterministic and distinguishes distinct node/field sets."""
    if "present:" in msg:
        tail = msg.rsplit("present:", 1)[1]
        toks = [t.strip("() ") for t in tail.replace(",", " ").split()]
        toks = [t for t in toks if t and t.lower() not in ("and", "or")]
        if toks:
            return "+".join(sorted(set(toks)))
    for word in msg.replace(":", " ").replace(",", " ").split():
        if word[:1].isupper() and word.isalnum() and word not in ("Solidity", "AST"):
            return word
    return msg.strip().split(":")[0][:48] if msg else "unknown"


def soundness_fingerprint(comparison: obs.ObservableComparison,
                          feature: str) -> tuple:
    """lane S: (observable_component, minimal_feature, delta_shape)."""
    component = comparison.differing_component or "unknown"
    if component == "wrong-value":
        obs_component = "return_value"
    elif component in ("wrong-panic", "wrong-revert", "revert-vs-success"):
        obs_component = "revert_data"
    else:
        obs_component = component
    return (obs_component, feature, component)


def _annotate_dedup(report: Report, lane: str, key: tuple, feature_token: str) -> None:
    report.fingerprint = {"lane": lane, "key": list(key),
                          "key_str": "|".join(str(k) for k in key)}
    hit = kg.match_fingerprint(lane, key) or kg.match_relaxed(lane, feature_token)
    if hit is not None:
        report.duplicate_of = hit.id
        report.reason += (f"  [DUPLICATE of known gap {hit.id}: {hit.feature}]")


# ---------------------------------------------------------------------------
# The pipeline (steps 1-3)
# ---------------------------------------------------------------------------

def adjudicate(root: Path, tools: Optional[hb.ToolPaths] = None,
               work_dir: Optional[Path] = None, timeout: int = 400,
               skip_forge: bool = False,
               _selftest_perturb_evm: Optional[Any] = None,
               _selftest_perturb_solidus: Optional[Any] = None) -> Report:
    """Adjudicate a submission (design §4).

    ``_selftest_perturb_evm`` / ``_selftest_perturb_solidus`` are TEST-ONLY seams
    (contest/run_samples.py): callables applied to the measured EVM observable /
    the real Solidus result to INJECT a synthetic divergence, so the
    divergence-DETECTION paths (SOUNDNESS_GAP / COVERAGE_GAP) can be exercised
    end-to-end over a real pipeline run WITHOUT leaving a bug in Solidus. Both
    MUST be None in real adjudication."""
    tools = tools or hb.ToolPaths()
    submission, malformed = load_submission(root)
    if malformed is not None:
        return malformed
    assert submission is not None
    claim = submission.claim
    entry = claim["entry"]
    lane = claim["lane"]
    over_accept = bool(claim.get("_over_accept") or
                       (lane == "S" and claim.get("mode") == "OVER_ACCEPT"))

    work = work_dir or Path(tempfile.mkdtemp(prefix="contest-adjudicate."))
    work.mkdir(parents=True, exist_ok=True)
    evidence: dict[str, Any] = {"submission": str(root), "lane_claimed": lane}

    # -- Step 0a: VALIDATE UNTRUSTED CLAIM FIELDS before any codegen ---------
    # Names reach generated Lean; fuel reaches the interpreter; args reach the
    # renderer. All are attacker-controlled (review findings 3/4/5).
    if not _valid_identifier(entry.get("contract")):
        return Report("REJECT_MALFORMED", reason=(
            f"entry.contract is not a valid identifier: {entry.get('contract')!r}"),
            evidence=evidence)
    if not _valid_identifier(entry.get("function")):
        return Report("REJECT_MALFORMED", reason=(
            f"entry.function is not a valid identifier: {entry.get('function')!r}"),
            evidence=evidence)
    fuel = _valid_fuel(claim.get("fuel", 64))
    if fuel is None:
        return Report("REJECT_MALFORMED", reason=(
            f"claim.fuel must be an integer in [1, {_FUEL_CAP}]"), evidence=evidence)
    args_lean, args_err = _safe_render_args(entry.get("args", []))
    if args_lean is None:
        return Report("REJECT_MALFORMED", reason=args_err or "bad args",
                      evidence=evidence)
    slots, slots_err = _valid_slots(claim.get("observed_slots", []))
    if slots is None:
        return Report("REJECT_MALFORMED", reason=slots_err or "bad observed_slots",
                      evidence=evidence)

    # -- Step 0b: CHEATCODE GATE over BOTH src AND test, BEFORE any Forge run.
    # The trust boundary is any call to the cheatcode ADDRESS from any submitted
    # code executed under `forge test` (adversarial-review findings 1 & 2). We
    # scan src too, because measure.py DEPLOYS and calls the entry contract — a
    # cheatcode call from the entry contract forges the measured EVM observable.
    # This MUST run before Forge/measurement so untrusted code never executes
    # with a cheatcode reference the gate would have caught.
    env_ov = cenv.EnvOverrides()
    env_ov.value = int(entry.get("value", 0) or 0)
    try:
        src_asts = gate.get_source_asts(submission.sources, tools.solc)
    except Exception as exc:  # solc failure on adversarial source (finding 5)
        return Report("REJECT_MALFORMED", reason=(
            f"solc could not analyze the submitted sources: {exc}"),
            evidence=evidence)
    test_asts = _test_asts(submission.root, tools.solc)
    src_scan = gate.scan_src_cheatcodes(src_asts)
    test_scan = gate.scan_test_cheatcodes(test_asts)
    evidence["cheatcodes"] = {
        "src_banned": [h.to_dict() for h in src_scan.banned],
        "test_banned": [h.to_dict() for h in test_scan.banned],
        "unmirrorable": [h.to_dict() for h in
                         (src_scan.unmirrorable + test_scan.unmirrorable)],
        "overrides": test_scan.overrides.to_dict(),
    }
    banned = src_scan.banned + test_scan.banned
    if banned:
        ids = ", ".join(sorted({h.id for h in banned}))
        where = "src" if src_scan.banned else "test"
        return Report("REJECTED_OOS", reason=(
            f"submission {where} references the cheatcode address / uses a "
            f"banned cheatcode ({ids}); state/oracle-forging cheatcodes are not "
            "allowed (default-deny)"), evidence=evidence)
    if test_scan.unmirrorable:
        return Report("REJECTED_OOS", reason=(
            "test uses a whitelisted cheatcode with a non-literal argument that "
            "cannot be mirrored into the Solidus env (v1 requires literals)"),
            evidence=evidence)
    # merge the mirrored overrides, preserving the entry value.
    test_scan.overrides.value = env_ov.value
    env_ov = test_scan.overrides

    # -- Step 1 / 1a: REAL-BEHAVIOR CHECK ------------------------------------
    measured: Optional[meas.Measurement] = None
    if over_accept:
        # error_code pins the reject to a semantic cause (review L-1 / P1).
        code = claim.get("solc_error_code") or claim.get("solc_reject_error_code")
        ok, status = hb.run_solc_rejects_source(
            submission.sources[0], work / "solc-rejects", error_code=code,
            tools=tools, timeout=timeout)
        evidence["solc_rejects"] = status
        if not ok:
            return Report("INVALID", reason=(
                "OVER_ACCEPT claim but pinned solc did NOT reject the program "
                f"as declared ({status})"), evidence=evidence)
    elif not skip_forge:
        mc = claim.get("forge_match_contract")
        mt = claim.get("forge_match_test")
        ok, status = hb.run_forge_test(
            submission.forge_root, work / "forge", match_contract=mc,
            match_test=mt, tools=tools, timeout=timeout)
        evidence["forge"] = status
        if not ok:
            return Report("INVALID", reason=(
                "claimed behavior does not reproduce on pinned solc 0.8.35 + "
                f"Foundry (forge={status})"), evidence=evidence)
        # -- MEASURE the EVM observable from an actual Forge run (P0 #1) -----
        sig = meas.entry_signature(
            _src_for(submission.sources, entry["contract"], tools.solc)
            or submission.sources[0], entry["contract"], entry["function"],
            tools.solc)
        if sig is None:
            return Report("REJECT_MALFORMED", reason=(
                f"entry {entry['contract']}.{entry['function']} not found / has "
                "no function selector in the compiled AST"), evidence=evidence)
        measured, mstatus = meas.measure_evm(
            sig, entry.get("args", []), env_ov, work / "measure",
            forge=tools.forge, solc=tools.solc, repo=tools.repo, timeout=timeout,
            slots=slots)
        evidence["evm_measurement"] = (measured.raw if measured else mstatus)
        if measured is None:
            return Report("INVALID", reason=(
                f"could not measure the EVM observable from the Forge run "
                f"({mstatus})"), evidence=evidence)
        # Mirror the deployed entry address into the Solidus env so
        # address(this) agrees by construction (review E-1).
        env_ov.self_addr = measured.self_addr
    else:
        evidence["forge"] = "skipped"

    # -- Step 2: REJECT GATE (whole submission) ------------------------------
    gate_verdict = gate.run_gate(submission.sources, solc=tools.solc,
                                 enforce_v1_multi=True)
    evidence["gate"] = gate_verdict.to_dict()
    if not gate_verdict.is_pass:
        ids = ", ".join(sorted({h.id for h in gate_verdict.hits}))
        return Report("REJECTED_OOS", reason=(
            f"reject gate fired: {ids} (intentional exclusion, out of scope)"),
            evidence=evidence)

    # -- Step 3: RUN SOLIDUS -------------------------------------------------
    # (v1 single-contract: the responder-free ownCall path.)
    src = _source_of_contract(submission.sources, entry["contract"], tools.solc)
    if src is None:
        return Report("REJECT_MALFORMED", reason=(
            f"entry contract {entry['contract']!r} not found in submitted sources"),
            evidence=evidence)
    namespace = f"{NAMESPACE_PREFIX}.{_sanitize(root.name)}"
    solidus = hb.run_solidus_observable(
        src, entry["contract"], entry["function"], entry.get("args", []),
        work / "solidus", namespace, fuel=fuel,
        tools=tools, timeout=timeout, env=env_ov, slots=slots)
    if _selftest_perturb_solidus is not None:  # coverage bug-injection self-test
        solidus = _selftest_perturb_solidus(solidus)
        evidence["selftest_solidus_perturbed"] = True
    evidence["env"] = env_ov.to_dict()
    evidence["solidus"] = {
        "ok": solidus.ok, "stage": solidus.stage,
        "fail_closed": solidus.fail_closed, "message": solidus.message[:1000],
        "observable": solidus.observable.raw if solidus.observable else None,
    }

    # (3b) OVER_ACCEPT: Solidus ran a program solc rejected -> lane S.
    if over_accept:
        if solidus.ok:
            report = Report("SOUNDNESS_GAP", lane="S", reason=(
                "Solidus imports+typechecks+runs a program that pinned solc "
                "REJECTS (over-accept)"), evidence=evidence)
            key = ("over_accept", claim.get("feature", "over-accept"), "over-accept")
            _annotate_dedup(report, "S", key, claim.get("feature", "over-accept"))
            return report
        # Solidus also rejected: agrees with solc -> not a gap.
        return Report("NO_DIVERGENCE", reason=(
            "both pinned solc and Solidus reject the program (agree)"),
            evidence=evidence)

    # (3a) Solidus FAILS CLOSED while solc accepted+ran -> lane C coverage gap.
    if solidus.fail_closed:
        # An INCONCLUSIVE failure (timeout / resource exhaustion / harness crash,
        # incl. a poisoned fuel) is NOT evidence of a missing feature (review
        # finding 3). Never auto-qualify it; route to maintainer review.
        if solidus.inconclusive:
            return Report("NEEDS_REVIEW", reason=(
                "Solidus run failed inconclusively (timeout / resource "
                f"exhaustion), not a clean reject: {solidus.message[:300]}"),
                evidence=evidence)
        finger = coverage_fingerprint(solidus)
        if finger[1] == "excluded":
            return Report("REJECTED_OOS", reason=(
                "importer reports an EXCLUDED node the gate did not catch "
                "(register/importer drift - gate bug, §2), not a coverage gap"),
                evidence=evidence)
        # Sub-kind follows the importer/typecheck REASON CLASS, not the stage
        # (review D-1): a type/elaboration reject of a solc-accepted program is
        # an over-reject; unimplemented/unclassified/unknown is a missing feature.
        reason_class = finger[1]
        sub_kind = ("over_reject" if reason_class in ("over_reject", "typecheck_reject")
                    else "missing_feature")
        evidence["coverage_reason_class"] = reason_class
        report = Report("COVERAGE_GAP", lane="C", reason=(
            f"Solidus fails closed ({solidus.stage}: {sub_kind}, "
            f"{reason_class}) on an in-scope, solc-accepted program"),
            evidence=evidence)
        _annotate_dedup(report, "C", finger, finger[2])
        return report

    # (3c) Solidus ran to completion -> compare against the MEASURED EVM
    # observable (review P0 #1: the oracle is the Forge run, NOT the claim).
    if measured is None:
        return Report("REJECT_MALFORMED", reason=(
            "no measured EVM observable available (Forge measurement did not "
            "run); cannot adjudicate a soundness claim without the oracle"),
            evidence=evidence)
    evm_obs = obs.evm_observable(
        measured.ok, measured.ret_hex, sig.return_types,
        events=measured.events, storage=measured.storage)
    if _selftest_perturb_evm is not None:  # fault-injection self-test only
        evm_obs = _selftest_perturb_evm(evm_obs)
        evidence["selftest_perturbed"] = True
    evidence["evm_observable"] = evm_obs.to_dict()
    # declared_observable is now only a sanity cross-check (misreport hint).
    declared_norm = (claim.get("declared_observable", {}) or {}).get("normal_form")
    if declared_norm and declared_norm.strip() != evm_obs.raw.strip():
        evidence["declared_mismatch"] = {
            "declared": declared_norm, "measured": evm_obs.raw,
            "note": "submitter's declared_observable disagrees with the measured "
                    "EVM observable; adjudication uses the MEASURED value."}
    assert solidus.observable is not None
    comparison = obs.compare_observables(solidus.observable, evm_obs)
    evidence["comparison"] = comparison.to_dict()

    if comparison.equal:
        return Report("NO_DIVERGENCE", reason=(
            "Solidus observable equals the solc+EVM observable (agree)"),
            evidence=evidence)

    feature = claim.get("feature", "unspecified-feature")
    report = Report("SOUNDNESS_GAP", lane="S", reason=(
        f"Solidus runs but the observable DIFFERS "
        f"({comparison.differing_component}): solidus={solidus.observable.raw} "
        f"vs solc+EVM={evm_obs.raw}"), evidence=evidence)
    key = soundness_fingerprint(comparison, feature)
    _annotate_dedup(report, "S", key, feature)
    return report


def _sanitize(name: str) -> str:
    return "".join(c if c.isalnum() else "_" for c in name).strip("_") or "Sub"


import re as _re

_IDENT_RE = _re.compile(r"^[A-Za-z_$][A-Za-z0-9_$]*$")


def _valid_identifier(name: object) -> bool:
    """A Solidity identifier — enforced on entry.contract / entry.function in
    ALL paths BEFORE either name is interpolated into generated Lean (review
    finding 4: an unchecked name could close the Lean string literal and inject
    code)."""
    return isinstance(name, str) and bool(_IDENT_RE.match(name))


_FUEL_CAP = 100_000


def _valid_fuel(value: object) -> Optional[int]:
    """Return a validated fuel (positive int <= cap), or None if malformed
    (review finding 3: an attacker-controlled `fuel` of -1 / 10**12 either fails
    to elaborate or times out, and was mis-scored as a coverage gap)."""
    try:
        fuel = int(value)
    except (TypeError, ValueError):
        return None
    if fuel < 1 or fuel > _FUEL_CAP:
        return None
    return fuel


_MAX_SLOTS = 64


def _valid_slots(slots: object) -> tuple[Optional[list[int]], Optional[str]]:
    """Validate claim.observed_slots: a list of <=64 non-negative uint256 storage
    slots to compare (§3.4 component 5). Empty/absent means storage is not
    compared. Attacker-controlled -> validated before reaching codegen."""
    if slots is None:
        return [], None
    if not isinstance(slots, list) or len(slots) > _MAX_SLOTS:
        return None, f"observed_slots must be a list of <= {_MAX_SLOTS} slots"
    out: list[int] = []
    for s in slots:
        try:
            v = int(s)
        except (TypeError, ValueError):
            return None, f"observed_slots entry not an integer: {s!r}"
        if v < 0 or v >= (1 << 256):
            return None, f"observed_slots entry out of uint256 range: {s!r}"
        out.append(v)
    return out, None


def _safe_render_args(args: object) -> tuple[Optional[str], Optional[str]]:
    """Render entry args to a Lean list, catching any malformed shape (review
    finding 5: `render_lean_arg` raises on unsupported forms and would crash the
    adjudicator instead of returning REJECT_MALFORMED)."""
    if not isinstance(args, list):
        return None, f"entry.args must be a list, got {type(args).__name__}"
    try:
        return obs.render_lean_args(args), None
    except (ValueError, TypeError, KeyError) as exc:
        return None, f"malformed entry.args: {exc}"


def _test_asts(root: Path, solc: str) -> list[gate.SourceAst]:
    """solc ASTs of the submission's TEST files (review P0 #3 cheatcode scan).

    Test files import ``../src/*``, so they are compiled together with the src
    sources (multi_source_asts) for imports to resolve."""
    test_dir = root / "test"
    if not test_dir.is_dir():
        return []
    test_files = sorted(test_dir.glob("*.sol"))
    src_files = sorted((root / "src").glob("*.sol")) if (root / "src").is_dir() else []
    if not test_files:
        return []
    return gate.multi_source_asts(test_files, test_files + src_files, solc)


def _src_for(sources: list[Path], contract: str, solc: str) -> Optional[Path]:
    return _source_of_contract(sources, contract, solc)


def _source_of_contract(sources: list[Path], contract: str, solc: str) -> Optional[Path]:
    for src in sources:
        try:
            _name, ast = gate._IMPORTER.run_solc_ast(solc, src)
        except Exception:
            continue
        for node in gate.iter_nodes(ast):
            if node.get("nodeType") == "ContractDefinition" and node.get("name") == contract:
                return src
    return None


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Adjudicate a divergence-contest submission")
    p.add_argument("submission", type=Path)
    p.add_argument("--solc", default=hb.DEFAULT_SOLC)
    p.add_argument("--forge", default=hb.DEFAULT_FORGE)
    p.add_argument("--lake", default=hb.DEFAULT_LAKE)
    p.add_argument("--timeout", type=int, default=400)
    p.add_argument("--work-dir", type=Path, default=None)
    p.add_argument("--skip-forge", action="store_true",
                   help="skip the Forge real-behavior check (debug only)")
    p.add_argument("--json", action="store_true", help="emit JSON only")
    args = p.parse_args(argv)

    tools = hb.ToolPaths(solc=args.solc, forge=args.forge, lake=args.lake)
    report = adjudicate(args.submission, tools=tools, work_dir=args.work_dir,
                        timeout=args.timeout, skip_forge=args.skip_forge)
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        print(json.dumps(report.to_dict(), indent=2))
        print(f"\n=== VERDICT: {report.verdict}"
              + (f" (lane {report.lane})" if report.lane else "")
              + f" | qualifies={report.qualifies} ===", file=sys.stderr)
    return 0 if report.qualifies or report.verdict == "NO_DIVERGENCE" else 1


if __name__ == "__main__":
    raise SystemExit(_main())
