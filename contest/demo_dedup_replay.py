"""Runnable end-to-end demo of fix-time dedup replay against two REAL Lean builds.

Adjudicates a sample against a "buggy" build E0 (which diverges from EVM) and then
replays it against a reference build to classify DUPLICATE (reference fixes the
divergence) vs NOVEL (reference still diverges). Unlike the unit tests in
run_samples.py (which inject a fake adjudicate_fn), this drives the real adjudicator
against two on-disk builds, so it needs both to be fully built.

Reproduction used in development (round 29):
  * E0 buggy build   = a worktree with SolidCore Interpreter RevertData.overflow
                       patched to `panic 0x99` (wrong overflow panic code).
  * FIXED reference  = main (correct `panic 0x11`).
  * SAME  reference  = the buggy build itself (a reference that does NOT fix it).
  * sample           = contest/samples/panic_overflow.
  Result: E0 -> SOUNDNESS_GAP (wrong-panic); vs FIXED -> DUPLICATE; vs SAME -> NOVEL.

Usage:
  python3 -m contest.demo_dedup_replay \
      --buggy   /path/to/buggy-build \
      --reference /path/to/reference-build \
      --sample  contest/samples/panic_overflow
"""
from __future__ import annotations

import argparse
from pathlib import Path

from . import adjudicate as adj
from . import harness_bridge as hb
from . import dedup_replay as dr


def _run(sample: Path, repo: Path):
    return adj.adjudicate(sample, tools=hb.ToolPaths(repo=repo))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--buggy", type=Path, required=True,
                    help="build E0 that diverges from EVM on the sample")
    ap.add_argument("--reference", type=Path, required=True,
                    help="reference build E1 to replay against (the 'fixed' engine)")
    ap.add_argument("--sample", type=Path, required=True, help="submission dir")
    args = ap.parse_args()

    print(f"Adjudicating {args.sample.name} against E0 (buggy build)...")
    e0 = _run(args.sample, args.buggy)
    comp = e0.evidence.get("comparison", {}) or {}
    print(f"  E0 verdict={e0.verdict} qualifies={e0.qualifies} fp={dr.fingerprint_key(e0)}")
    print(f"  solidity-lean={comp.get('solidity_lean_observable', {}).get('normal_form')}")
    print(f"  evm         ={comp.get('evm_observable', {}).get('normal_form')}")

    print(f"\nReplaying against reference build {args.reference}...")
    e1 = _run(args.sample, args.reference)
    print(f"  E1 verdict={e1.verdict} qualifies={e1.qualifies}")

    verdict = dr.classify_dedup(e0, e1)
    print(f"\n=== DEDUP: {verdict.dedup_class.upper()} ===  :: {verdict.reason}")
    return 0 if verdict.dedup_class in (dr.DUPLICATE, dr.NOT_IN_POOL) else 1


if __name__ == "__main__":
    raise SystemExit(main())
