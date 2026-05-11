#!/usr/bin/env python3
"""Manage pinned Foundry suites for Lean EVM equivalence work."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tomllib
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = ROOT / "tests" / "evm" / "forge-parity" / "foundry-suites.toml"
SKIP_DIRS = {".git", "cache", "lib", "node_modules", "out"}
CHEATCODE_RE = re.compile(r"\b(?:vm|hevm)\.([A-Za-z_][A-Za-z0-9_]*)\s*\(")
TEST_FUNCTION_RE = re.compile(r"\bfunction\s+((?:test|invariant)[A-Za-z0-9_]*)\s*\(")


@dataclass(frozen=True)
class Suite:
    id: str
    name: str
    kind: str
    enabled: bool
    lean_replay: str
    path: str | None
    repo: str | None
    rev: str | None
    submodules: bool
    forge_args: tuple[str, ...]
    notes: str


@dataclass(frozen=True)
class Manifest:
    path: Path
    checkout_root: Path
    suites: tuple[Suite, ...]
    supported_cheatcodes: frozenset[str]


def load_manifest(path: Path) -> Manifest:
    with path.open("rb") as f:
        raw = tomllib.load(f)
    checkout_root = resolve_path(raw.get("checkout_root", ".foundry-suites"))
    runner = raw.get("lean_runner", {})
    supported = frozenset(runner.get("supported_cheatcodes", []))
    suites = tuple(parse_suite(entry) for entry in raw.get("suite", []))
    return Manifest(path, checkout_root, suites, supported)


def parse_suite(entry: dict[str, Any]) -> Suite:
    return Suite(
        id=require_str(entry, "id"),
        name=require_str(entry, "name"),
        kind=require_str(entry, "kind"),
        enabled=bool(entry.get("enabled", False)),
        lean_replay=str(entry.get("lean_replay", "planned")),
        path=entry.get("path"),
        repo=entry.get("repo"),
        rev=entry.get("rev"),
        submodules=bool(entry.get("submodules", False)),
        forge_args=tuple(str(arg) for arg in entry.get("forge_args", [])),
        notes=str(entry.get("notes", "")),
    )


def require_str(entry: dict[str, Any], key: str) -> str:
    value = entry.get(key)
    if not isinstance(value, str) or not value:
        raise SystemExit(f"manifest entry is missing string field {key!r}")
    return value


def resolve_path(path: str | Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return ROOT / candidate


def suite_dir(manifest: Manifest, suite: Suite) -> Path:
    if suite.kind == "local":
        if suite.path is None:
            raise SystemExit(f"suite {suite.id}: local suite missing path")
        return resolve_path(suite.path)
    if suite.kind == "git":
        return manifest.checkout_root / suite.id
    raise SystemExit(f"suite {suite.id}: unknown kind {suite.kind!r}")


def selected_suites(manifest: Manifest, ids: list[str], *, enabled_only: bool) -> list[Suite]:
    suites = list(manifest.suites)
    if ids:
        wanted = set(ids)
        suites = [suite for suite in suites if suite.id in wanted]
        missing = wanted - {suite.id for suite in suites}
        if missing:
            raise SystemExit(f"unknown suite id(s): {', '.join(sorted(missing))}")
    if enabled_only:
        suites = [suite for suite in suites if suite.enabled]
    return suites


def run(cmd: list[str], cwd: Path, *, check: bool = True) -> subprocess.CompletedProcess[str]:
    print("$", " ".join(cmd), f"(cwd={cwd})")
    proc = subprocess.run(cmd, cwd=cwd, text=True)
    if check and proc.returncode != 0:
        raise SystemExit(proc.returncode)
    return proc


def list_suites(manifest: Manifest, suites: list[Suite]) -> None:
    print(f"manifest {manifest.path}")
    print(f"checkout_root {manifest.checkout_root}")
    print()
    print(f"{'id':28} {'kind':6} {'enabled':7} {'lean':15} location")
    for suite in suites:
        location = suite.path if suite.kind == "local" else suite.repo
        print(
            f"{suite.id:28} {suite.kind:6} {str(suite.enabled):7} "
            f"{suite.lean_replay:15} {location}"
        )


def fetch_suites(manifest: Manifest, suites: list[Suite]) -> None:
    manifest.checkout_root.mkdir(parents=True, exist_ok=True)
    for suite in suites:
        if suite.kind != "git":
            print(f"{suite.id}: local suite, nothing to fetch")
            continue
        if not suite.repo or not suite.rev:
            raise SystemExit(f"{suite.id}: git suite requires repo and rev")
        path = suite_dir(manifest, suite)
        if path.exists():
            run(["git", "fetch", "--tags", "origin"], path)
        else:
            run(["git", "clone", suite.repo, str(path)], ROOT)
        run(["git", "checkout", "--detach", suite.rev], path)
        if suite.submodules:
            run(["git", "submodule", "update", "--init", "--recursive"], path)


def iter_solidity_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*.sol"):
        rel_parts = path.relative_to(root).parts
        if any(part in SKIP_DIRS for part in rel_parts):
            continue
        files.append(path)
    return files


def scan_cheatcodes(root: Path) -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in iter_solidity_files(root):
        try:
            text = path.read_text(errors="ignore")
        except OSError:
            continue
        counts.update(CHEATCODE_RE.findall(text))
    return counts


def scan_test_functions(root: Path) -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in iter_solidity_files(root):
        try:
            text = path.read_text(errors="ignore")
        except OSError:
            continue
        counts.update(TEST_FUNCTION_RE.findall(text))
    return counts


def scan_suites(manifest: Manifest, suites: list[Suite]) -> None:
    for suite in suites:
        root = suite_dir(manifest, suite)
        if not root.exists():
            print(f"{suite.id}: missing checkout at {root}")
            continue
        counts = scan_cheatcodes(root)
        tests = scan_test_functions(root)
        unsupported = sorted(set(counts) - manifest.supported_cheatcodes)
        print(
            f"{suite.id}: {sum(tests.values())} test/invariant functions, "
            f"{sum(counts.values())} vm.* calls, {len(counts)} unique cheatcodes"
        )
        if counts:
            top = ", ".join(f"{name}={count}" for name, count in counts.most_common(20))
            print(f"  top: {top}")
        if unsupported:
            print(f"  unsupported_by_lean_runner: {', '.join(unsupported)}")


def forge_suites(manifest: Manifest, suites: list[Suite], extra_args: list[str]) -> None:
    for suite in suites:
        root = suite_dir(manifest, suite)
        if not root.exists():
            print(f"{suite.id}: missing checkout at {root}")
            continue
        cmd = ["forge", "test", *suite.forge_args, *extra_args]
        run(cmd, root)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    sub = parser.add_subparsers(dest="command", required=True)

    for name in ["list", "fetch", "scan", "forge"]:
        cmd = sub.add_parser(name)
        cmd.add_argument("--suite", action="append", default=[])
        cmd.add_argument(
            "--enabled-only",
            action="store_true",
            help="only use suites marked enabled=true",
        )
        if name == "forge":
            cmd.add_argument("forge_args", nargs=argparse.REMAINDER)
    return parser


def main() -> None:
    args = build_parser().parse_args()
    manifest = load_manifest(args.manifest)
    suites = selected_suites(manifest, args.suite, enabled_only=args.enabled_only)
    if args.command == "list":
        list_suites(manifest, suites)
    elif args.command == "fetch":
        fetch_suites(manifest, suites)
    elif args.command == "scan":
        scan_suites(manifest, suites)
    elif args.command == "forge":
        extra = args.forge_args
        if extra and extra[0] == "--":
            extra = extra[1:]
        forge_suites(manifest, suites, extra)
    else:
        raise SystemExit(f"unknown command {args.command}")


if __name__ == "__main__":
    main()
