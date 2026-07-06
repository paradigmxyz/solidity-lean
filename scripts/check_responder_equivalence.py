#!/usr/bin/env python3
"""Stage-2 responder equivalence check (Phase 5 propagation plan §2 step 4).

For every manifest witness that embeds fixture-oracle rows (`lowLevelCallResults`
/ `contractCreationResults` in its `expr`), regenerate the witness with each
tree-folding checked entry point name-swapped to its `*RespCheck` twin. The twin
folds the SAME interaction tree under `ScriptedResponder.ofContext` (the derived
scripted responder) instead of `contextAnswer` (the fixture oracle). If every
twinned witness still prints the case's expected value, then folding under the
derived responder is observationally identical to folding under the retired
`contextAnswer` — across every oracle-bearing witness's results AND the recorded
external-interaction transcripts its assertions check. This is a rigorous,
manifest-preserving validation lane (it does NOT modify manifest.json).

Usage:
  scripts/check_responder_equivalence.py [--solc PATH] [--lake PATH]
"""
from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_forge_interpreter_harness as H  # noqa: E402

# CheckedContract / CheckedProgram tree-folding entry points that have a
# `*RespCheck` twin (same argument shape). `contract` (pure lookup) and
# `functionCalldata` (pure ABI encoding, no tree) are deliberately excluded.
SWAP_ENTRIES = [
    "CheckedContract.callFunctionWithContext",
    "CheckedContract.callTargetWithContext",
    "CheckedContract.constructFrom",
    "CheckedContract.construct",
    "CheckedContract.callCalldataAtFromWithContext",
    "CheckedContract.callCalldata",
    "CheckedProgram.constructContractWithContext",
]


def swap_entries(expr: str) -> str:
    out = expr
    for name in SWAP_ENTRIES:
        # Match the entry name only when it is NOT followed by another identifier
        # char (so `construct` never matches `constructFrom`, `callCalldata`
        # never matches `callCalldataAtFromWithContext`, etc.).
        pattern = re.compile(re.escape(name) + r"(?![A-Za-z0-9_])")
        out = pattern.sub(name + "RespCheck", out)
    return out


def has_oracle(expr: str) -> bool:
    return "lowLevelCallResults" in expr or "contractCreationResults" in expr


def run_case(case, repo, variables, timeout) -> tuple[str, list[str]]:
    """Returns (status, failures). status in {'pass','skip','fail'}."""
    lean = case.get("lean")
    if not isinstance(lean, dict):
        return "skip", []
    evals = [e for e in lean.get("evals", []) if has_oracle(e.get("expr", ""))]
    if not evals:
        return "skip", []

    ok, status, generated = H.run_solc_import(case, repo, variables, timeout)
    if not ok:
        return "fail", [f"solc_ast_{status}"]

    imports = lean.get("imports", [])
    if isinstance(lean.get("import"), str):
        imports = [lean["import"]]
    lines = [f"import {i}" for i in imports]
    if generated:
        lines += ["", generated]

    expected, labels = [], []
    for e in evals:
        twin = swap_entries(e["expr"])
        lines.append(f"#eval {twin}")
        expected.append(e["expect"])
        labels.append(e.get("label", "?"))

    case_tmp = Path(variables["case_tmp"])
    lean_file = case_tmp / "responder-equiv.lean"
    H.write_text(lean_file, "\n".join(lines) + "\n")
    out_log = case_tmp / "responder-equiv.stdout.log"
    err_log = case_tmp / "responder-equiv.stderr.log"
    cmd = [variables["lake"], "env", "lean", str(lean_file)]
    try:
        code = H.run_capture(cmd, repo, timeout, out_log, err_log)
    except Exception as exc:  # noqa: BLE001
        return "fail", [f"lean_exc_{exc}"]
    if code != 0:
        tail = err_log.read_text(errors="replace").strip().splitlines()[-6:]
        return "fail", [f"lean_exit_{code}", *tail]

    actual = [l.strip() for l in out_log.read_text().splitlines() if l.strip()]
    actual_tail = actual[-len(expected):] if expected else []
    fails = []
    for label, exp, act in zip(labels, expected, actual_tail):
        if act != exp:
            fails.append(f"{label}: expected {exp!r} got {act!r}")
    return ("fail" if fails else "pass"), fails


def main(argv=None) -> int:
    repo = H.repo_root()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", default="tests/forge-harness/manifest.json")
    parser.add_argument("--solc")
    parser.add_argument("--lake")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest)
    if not manifest_path.is_absolute():
        manifest_path = repo / manifest_path
    manifest = H.load_manifest(manifest_path)
    solc = H.resolve_executable("solc", args.solc)
    lake = H.resolve_executable("lake", args.lake)

    outdir = Path(tempfile.mkdtemp(prefix="responder-equiv.",
                                   dir=os.environ.get("TMPDIR") or None))
    selected = set(args.only)

    total = passed = skipped = 0
    failures = []
    for case in manifest["cases"]:
        name = case.get("name", "?")
        if selected and name not in selected:
            continue
        case_tmp = outdir / name
        case_tmp.mkdir(parents=True, exist_ok=True)
        variables = {
            "case_tmp": str(case_tmp),
            "solc": solc,
            "lake": lake,
            "repo": str(repo),
        }
        status, fails = run_case(case, repo, variables, args.timeout)
        if status == "skip":
            skipped += 1
            continue
        total += 1
        if status == "pass":
            passed += 1
            print(f"case_equiv={name} responder_equivalent=yes")
        else:
            failures.append((name, fails))
            print(f"case_equiv={name} responder_equivalent=NO")
            for f in fails:
                print(f"    {f}")

    print(f"responder_equivalence_check={'pass' if not failures else 'fail'}")
    print(f"oracle_cases={total} equivalent={passed} skipped_non_oracle={skipped}")
    if failures:
        print(f"failed_cases={[n for n, _ in failures]}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
