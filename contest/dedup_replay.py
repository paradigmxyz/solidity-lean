"""Fix-time dedup via differential replay against a patched reference build.

WHY (design, discussed with Dan 2026-07-09)
--------------------------------------------
Same-root-cause dedup at SUBMISSION time is effectively undecidable: "are these
two submissions the same bug?" means "do they share a root cause", which means
understanding the bug -- manual, and defeated by cosmetic re-skinning. The dedup
key that actually matters economically is instead

    "does the SAME fix kill both?"

and THAT is computable -- just not at submission time. Defer it to FIX time, where
it becomes an exact, nearly-free, engine-derived oracle:

  * E0  = the current solidity-lean (carries all the known gaps).
  * E1  = a REFERENCE build = E0 + fixes for the known gaps (G1..G22).
  * Re-run a qualifying submission against E1:
      - divergence VANISHES under E1  -> it was covered by a known-gap fix
                                         => DUPLICATE of a known gap.
      - divergence PERSISTS under E1  -> not covered by any known fix
                                         => genuinely NOVEL.

This keys on ENGINE-BEHAVIOR-UNDER-PATCH, not on anything the submitter controls,
so it is immune to re-skinning (renaming, reordering, wrapping a reason in
abi.encodePacked, novelty-inflating the `feature` tag, ...). The EVM observable is
engine-independent (it is the measured ground truth), so replaying against E1 only
re-runs the SOLIDITY-LEAN side and re-compares against the same EVM observable.

For dedup AMONG fresh novel submissions (no known fix yet), the same trick batches:
admit all, hold payout, and when the first novel bug is FIXED, re-run the other
unpaid novel submissions against the newly-patched engine; every one that vanishes
was a duplicate of that fix -> collapses into one payout class. `collapse_classes`
models that batch step given a sequence of (submission, post-fix) replays.

STATUS: harness-side prototype. The reference build E1 is supplied by the caller
(a path to a patched checkout); producing the actual gap-fixes lives in
SolidCore/** and is out of scope for this module. The classifier + collapse logic
below are pure and fully unit-tested; `replay_against_reference` wires them to the
real adjudicator with dependency injection so it is testable without a second Lean
build.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Optional


# Dedup classes a qualifying submission can land in after a reference replay.
NOVEL = "novel"              # still diverges under E1 with the SAME fingerprint
DUPLICATE = "duplicate"      # divergence closed under E1 -> a known-gap duplicate
SHIFTED = "shifted"          # still diverges under E1 but with a DIFFERENT
                             # fingerprint -> the reference fix changed behavior
                             # without fully closing it; route to human review
INCONCLUSIVE = "inconclusive"  # E1 run was inconclusive (crash/timeout/needs-review)
NOT_IN_POOL = "not-in-pool"  # E0 did not qualify -> not a dedup candidate at all


@dataclass
class DedupVerdict:
    """The result of replaying one qualifying submission against reference E1."""
    dedup_class: str
    e0_verdict: str
    e1_verdict: str
    e0_fingerprint: Optional[str] = None
    e1_fingerprint: Optional[str] = None
    reason: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "dedup_class": self.dedup_class,
            "e0_verdict": self.e0_verdict,
            "e1_verdict": self.e1_verdict,
            "e0_fingerprint": self.e0_fingerprint,
            "e1_fingerprint": self.e1_fingerprint,
            "reason": self.reason,
        }


def _qualifies(report: Any) -> bool:
    return getattr(report, "qualifies", False)


def _verdict(report: Any) -> str:
    return getattr(report, "verdict", "UNKNOWN")


def _is_inconclusive(report: Any) -> bool:
    # A reference replay that lands in NEEDS_REVIEW / REJECT_MALFORMED (e.g. the E1
    # build errored, timed out, or the sample no longer builds under it) is NOT
    # evidence either way -- never silently collapse or keep it; surface for review.
    return _verdict(report) in ("NEEDS_REVIEW", "REJECT_MALFORMED", "INVALID")


def fingerprint_key(report: Any) -> Optional[str]:
    """A stable, adjudicator-DERIVED identity for the divergence (never the
    submitter's `feature` tag). Prefers the report fingerprint's key_str; falls
    back to the comparison's differing_component. Two submissions exploiting the
    same engine defect share this key even when re-skinned."""
    fp = getattr(report, "fingerprint", None)
    if isinstance(fp, dict):
        ks = fp.get("key_str")
        if ks:
            return str(ks)
        key = fp.get("key")
        if isinstance(key, (list, tuple)):
            return "|".join(str(x) for x in key)
    ev = getattr(report, "evidence", None) or {}
    comp = ev.get("comparison") if isinstance(ev, dict) else None
    if isinstance(comp, dict) and comp.get("differing_component"):
        return f"component:{comp['differing_component']}"
    return None


def classify_dedup(e0_report: Any, e1_report: Any) -> DedupVerdict:
    """Classify a submission by replaying its E0 adjudication against reference E1.

    Only a QUALIFYING E0 verdict is a dedup candidate. The decision is driven by
    whether the divergence still qualifies under E1 (the patched build):

      * E0 not qualifying                 -> NOT_IN_POOL
      * E1 inconclusive                   -> INCONCLUSIVE (human review)
      * E1 no longer qualifies            -> DUPLICATE (a known-gap fix closed it)
      * E1 qualifies, same fingerprint    -> NOVEL (reference did not touch it)
      * E1 qualifies, different fingerprint-> SHIFTED (partial; human review)
    """
    e0_fp = fingerprint_key(e0_report)
    e1_fp = fingerprint_key(e1_report)
    e0_v, e1_v = _verdict(e0_report), _verdict(e1_report)

    if not _qualifies(e0_report):
        return DedupVerdict(NOT_IN_POOL, e0_v, e1_v, e0_fp, e1_fp,
                            "E0 did not qualify; not a dedup candidate")
    if _is_inconclusive(e1_report):
        return DedupVerdict(INCONCLUSIVE, e0_v, e1_v, e0_fp, e1_fp,
                            "reference replay inconclusive; route to review")
    if not _qualifies(e1_report):
        return DedupVerdict(DUPLICATE, e0_v, e1_v, e0_fp, e1_fp,
                            "divergence closed under the reference build "
                            "-> duplicate of a known gap")
    if e0_fp is not None and e1_fp is not None and e0_fp == e1_fp:
        return DedupVerdict(NOVEL, e0_v, e1_v, e0_fp, e1_fp,
                            "still diverges under E1 with the same fingerprint "
                            "-> genuinely novel")
    return DedupVerdict(SHIFTED, e0_v, e1_v, e0_fp, e1_fp,
                        "still diverges under E1 but the fingerprint changed "
                        "-> reference partially altered behavior; human review")


@dataclass
class PayoutClass:
    """One dedup equivalence class -> at most one payout (first-to-file wins)."""
    key: str
    members: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {"key": self.key, "members": list(self.members)}


def collapse_classes(items: list[tuple[str, DedupVerdict]]) -> list[PayoutClass]:
    """Collapse (submission_id, DedupVerdict) pairs into payout classes.

    DUPLICATE / NOT_IN_POOL submissions do not form new classes (they collapse
    onto a known gap or fall out of the pool). NOVEL / SHIFTED submissions group
    by their adjudicator-derived fingerprint, so re-skins of the same novel defect
    share a class; INCONCLUSIVE items get their own singleton review class.

    Ordering is preserved (first-to-file within a class is the earliest member),
    so the caller can pay the first member of each class and reject the rest."""
    classes: dict[str, PayoutClass] = {}
    order: list[str] = []

    def _bucket(key: str) -> PayoutClass:
        if key not in classes:
            classes[key] = PayoutClass(key=key)
            order.append(key)
        return classes[key]

    for sub_id, dv in items:
        if dv.dedup_class in (DUPLICATE, NOT_IN_POOL):
            continue  # collapses onto a known gap / not a candidate -> no payout
        if dv.dedup_class == INCONCLUSIVE:
            _bucket(f"review:{sub_id}").members.append(sub_id)
            continue
        # NOVEL / SHIFTED: group by fingerprint (fall back to the id if absent).
        key = dv.e1_fingerprint or dv.e0_fingerprint or f"unkeyed:{sub_id}"
        _bucket(key).members.append(sub_id)

    return [classes[k] for k in order]


def replay_against_reference(
        sample_dir: Path,
        reference_repo_root: Path,
        *,
        adjudicate_fn: Optional[Callable[..., Any]] = None,
        tool_factory: Optional[Callable[..., Any]] = None,
        **adjudicate_kwargs: Any) -> DedupVerdict:
    """Adjudicate ``sample_dir`` against the current build (E0) and the reference
    build E1 (rooted at ``reference_repo_root``), then classify.

    ``adjudicate_fn`` / ``tool_factory`` are injectable so this is unit-testable
    without a second Lean build; in production they default to the real
    ``contest.adjudicate.adjudicate`` and ``contest.harness_bridge.ToolPaths``.
    Only the solidity-lean side differs between E0 and E1 -- the EVM observable is
    engine-independent -- so E1's verdict reflects purely whether the reference
    fixes closed this submission's divergence."""
    if adjudicate_fn is None:
        from . import adjudicate as _adj
        adjudicate_fn = _adj.adjudicate
    if tool_factory is None:
        from . import harness_bridge as _hb
        tool_factory = _hb.ToolPaths

    e0_report = adjudicate_fn(sample_dir, **adjudicate_kwargs)
    # A non-qualifying E0 is not a dedup candidate; skip the (expensive) E1 run.
    if not _qualifies(e0_report):
        return classify_dedup(e0_report, e0_report)

    e1_tools = tool_factory(repo=Path(reference_repo_root))
    e1_report = adjudicate_fn(sample_dir, tools=e1_tools, **adjudicate_kwargs)
    return classify_dedup(e0_report, e1_report)


def _main() -> int:
    import argparse
    import json
    parser = argparse.ArgumentParser(
        description="Fix-time dedup: replay a qualifying submission against a "
                    "patched REFERENCE build (E1) to tell a known-gap DUPLICATE "
                    "from a genuinely NOVEL divergence.")
    parser.add_argument("submission", type=Path,
                        help="submission dir (src/ test/ foundry.toml claim.json)")
    parser.add_argument("--reference-build", type=Path, required=True,
                        help="path to a fully-built reference checkout E1 "
                             "(= current build + known-gap fixes)")
    args = parser.parse_args()
    verdict = replay_against_reference(args.submission, args.reference_build)
    print(f"=== DEDUP: {verdict.dedup_class.upper()} "
          f"(E0={verdict.e0_verdict}, E1={verdict.e1_verdict}) ===")
    print(json.dumps(verdict.to_dict(), indent=2))
    # duplicate/not-in-pool -> non-payout (exit 0); novel/shifted/inconclusive
    # -> a human/payout action is warranted (exit 1 signals "needs attention").
    return 0 if verdict.dedup_class in (DUPLICATE, NOT_IN_POOL) else 1


if __name__ == "__main__":
    raise SystemExit(_main())
