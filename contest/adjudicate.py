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

Paying verdicts: COVERAGE_GAP (lane C), SOUNDNESS_GAP (lane S). Everything else
(INVALID, REJECTED_OOS, NO_DIVERGENCE, REJECT_MALFORMED) does not pay and
returns the specific reason.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from . import exclusion_register as reg
from . import harness_bridge as hb
from . import known_gaps as kg
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
    def pays_out(self) -> bool:
        return self.verdict in ("COVERAGE_GAP", "SOUNDNESS_GAP")

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "verdict": self.verdict,
            "lane": self.lane,
            "reason": self.reason,
            "pays_out": self.pays_out,
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
    """Extract a stable minimal node-type/field token from a fail message.

    Importer fail() messages have the shape
        "... nodes present: SomeNode"
        "... child fields present: Parent.field"
    so the identifying token is the first item AFTER the last "present:". We
    skip the boilerplate ("Solidity", "AST", ...) preceding it."""
    if "present:" in msg:
        tail = msg.split("present:", 1)[1]
        for word in tail.replace(",", " ").split():
            word = word.strip("()")
            if word:
                return word
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
               skip_forge: bool = False) -> Report:
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

    # -- Step 1 / 1a: REAL-BEHAVIOR CHECK ------------------------------------
    if over_accept:
        contains = claim.get("solc_reject_contains", "Error:")
        # a single-source over-accept: assert solc rejects the (first) source
        ok, status = hb.run_solc_rejects_source(
            submission.sources[0], work / "solc-rejects", contains=contains,
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
        work / "solidus", namespace, fuel=int(claim.get("fuel", 64)),
        tools=tools, timeout=timeout)
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
        finger = coverage_fingerprint(solidus)
        if finger[1] == "excluded":
            return Report("REJECTED_OOS", reason=(
                "importer reports an EXCLUDED node the gate did not catch "
                "(register/importer drift - gate bug, §2), not a coverage gap"),
                evidence=evidence)
        sub_kind = ("over_reject" if solidus.stage == "run" else "missing_feature")
        report = Report("COVERAGE_GAP", lane="C", reason=(
            f"Solidus fails closed ({solidus.stage}: {sub_kind}) on an in-scope, "
            f"solc-accepted program"), evidence=evidence)
        _annotate_dedup(report, "C", finger, finger[2])
        return report

    # (3c) Solidus ran to completion -> compare observables.
    declared = claim.get("declared_observable", {})
    evm_norm = declared.get("normal_form")
    if not evm_norm:
        return Report("REJECT_MALFORMED", reason=(
            "claim.declared_observable.normal_form is required to compare "
            "(the Forge-validated solc+EVM observable in normal form)"),
            evidence=evidence)
    evm_obs = obs.parse_observable(evm_norm)
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
              + f" | pays_out={report.pays_out} ===", file=sys.stderr)
    return 0 if report.pays_out or report.verdict == "NO_DIVERGENCE" else 1


if __name__ == "__main__":
    raise SystemExit(_main())
