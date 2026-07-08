#!/usr/bin/env python3
"""Thin bridge over scripts/run_forge_interpreter_harness.py (design §5.2).

Reuses the harness's PROVEN Forge/solc/import/lean invocations rather than
reinventing them:

  * ``run_forge``        - compile with pinned solc + run the Foundry test.
  * ``run_solc_rejects`` - assert solc REJECTS a source (OVER_ACCEPT claims).
  * ``run_solc_import``  - invoke solc_ast_to_lean_source.py to render Lean.

For the Solidus observable we reuse ``run_solc_import`` to obtain the generated
Lean source, then build our own tiny ``lake env lean`` invocation (mirroring the
harness's ``run_lean`` file assembly) so we can CAPTURE the #eval output line
rather than only match it against a fixed expectation. Nothing in the
solc/forge/import plumbing is changed.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional

import re

from . import env as cenv
from . import observable as obs


_REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOLC = "/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35"
DEFAULT_FORGE = "/Users/dan/.foundry/bin/forge"
DEFAULT_LAKE = shutil.which("lake") or "lake"


def _load_harness():
    script = _REPO_ROOT / "scripts" / "run_forge_interpreter_harness.py"
    spec = importlib.util.spec_from_file_location("run_forge_interpreter_harness", script)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


_HARNESS = _load_harness()


@dataclass
class ToolPaths:
    repo: Path = _REPO_ROOT
    solc: str = DEFAULT_SOLC
    forge: str = DEFAULT_FORGE
    lake: str = DEFAULT_LAKE


def _variables(tools: ToolPaths, case_tmp: Path, name: str) -> dict[str, str]:
    return {
        "repo": str(tools.repo),
        "outdir": str(case_tmp),
        "case_tmp": str(case_tmp),
        "forge": tools.forge,
        "solc": tools.solc,
        "lake": tools.lake,
        "case": name,
    }


# ---------------------------------------------------------------------------
# Forge (real-behavior check, design §4 step 1)
# ---------------------------------------------------------------------------

def run_forge_test(forge_root: Path, case_tmp: Path,
                   match_contract: Optional[str] = None,
                   match_test: Optional[str] = None,
                   tools: Optional[ToolPaths] = None,
                   timeout: int = 300) -> tuple[bool, str]:
    """Run the submission's Forge test. ``forge_root`` is a Foundry project
    dir (foundry.toml + src + test) relative to the repo or absolute."""
    tools = tools or ToolPaths()
    case_tmp.mkdir(parents=True, exist_ok=True)
    try:
        rel = forge_root.resolve().relative_to(tools.repo.resolve())
        root_arg = str(rel)
    except ValueError:
        root_arg = str(forge_root.resolve())
    forge_case: dict[str, Any] = {"forge": {"root": root_arg, "quiet": True}}
    if match_contract:
        forge_case["forge"]["match_contract"] = match_contract
    if match_test:
        forge_case["forge"]["match_test"] = match_test
    variables = _variables(tools, case_tmp, "forge")
    return _HARNESS.run_forge(forge_case, tools.repo, variables, timeout)


# solc diagnostics are `<Type>Error: ...` or `Error (NNNN): ...` with an exit
# code; warnings (`Warning: ...`) leave exit code 0. Review L-1 / P1: decide the
# OVER_ACCEPT reject by EXIT CODE + a real error diagnostic (optionally a
# specific error CODE), NOT a substring that a warning could satisfy.
_SOLC_ERROR_RE = re.compile(r"(?m)^(?:\S*Error|Error \(\d+\)):|Error \((\d+)\)")
_SOLC_ERRCODE_RE = re.compile(r"Error \((\d+)\)")


def run_solc_rejects_source(source: Path, case_tmp: Path,
                            error_code: Optional[str] = None,
                            tools: Optional[ToolPaths] = None,
                            timeout: int = 120) -> tuple[bool, str]:
    """Assert pinned solc REJECTS ``source`` (OVER_ACCEPT claims, §4 step 1a).

    Decision (review L-1 / P1): the compile must FAIL (non-zero exit) AND emit a
    real error-level diagnostic. Warnings never count (they leave exit 0). If
    ``error_code`` is given (e.g. "5887"), that specific solc error code must be
    present, so the reject is pinned to a semantic cause, not free text."""
    tools = tools or ToolPaths()
    case_tmp.mkdir(parents=True, exist_ok=True)
    stdout_log = case_tmp / "solc-reject.stdout.log"
    stderr_log = case_tmp / "solc-reject.stderr.log"
    # --error-codes makes solc print `Error (NNNN):` so a specific error code can
    # be matched (review L-1 / P1); without it the CLI omits the numeric code.
    command = [tools.solc, "--error-codes", "--bin", str(source.resolve())]
    try:
        status = _HARNESS.run_capture(command, tools.repo, timeout,
                                      stdout_log, stderr_log)
    except subprocess.TimeoutExpired:
        return False, f"timeout_after_{timeout}s"
    output = _read_log(stdout_log) + _read_log(stderr_log)
    if status == 0:
        return False, "unexpected_accept_exit0"
    if not _SOLC_ERROR_RE.search(output):
        # non-zero exit but no error-level diagnostic (e.g. internal/CLI issue)
        return False, f"exit_{status}_no_error_diagnostic"
    if error_code:
        codes = set(_SOLC_ERRCODE_RE.findall(output))
        if error_code not in codes:
            return False, f"error_code_{error_code}_not_found_in_{sorted(codes)}"
    return True, f"reject_exit_{status}"


# ---------------------------------------------------------------------------
# Solidus (import + typecheck + elaborate + execute; observable extraction)
# ---------------------------------------------------------------------------

@dataclass
class SolidusResult:
    """The outcome of running Solidus on the entry call."""

    ok: bool                     # True if the entry call ran to completion
    stage: str                   # "import" | "lean" | "run"
    fail_closed: bool            # True if Solidus rejected (coverage-gap candidate)
    observable: Optional[obs.Observable]
    message: str                 # evidence / error text
    generated_source_path: Optional[Path] = None


def _read_log(path: Path) -> str:
    try:
        return path.read_text(errors="replace")
    except OSError:
        return ""


def run_solidus_observable(source: Path, contract: str, fname: str, args: list,
                           case_tmp: Path, namespace: str,
                           fuel: int = 64,
                           tools: Optional[ToolPaths] = None,
                           timeout: int = 300,
                           env: Optional["cenv.EnvOverrides"] = None) -> SolidusResult:
    """Import ``source``, then #eval the §3.4 observable of ``contract.fname``.

    Distinguishes:
      * importer fail()            -> fail_closed, stage=import (coverage-gap)
      * lean exit != 0             -> fail_closed, stage=lean   (elab/exec reject)
      * observable "solidus-reject" -> fail_closed, stage=run   (typecheck reject)
      * observable success/revert  -> ok, stage=run
    """
    tools = tools or ToolPaths()
    env = env or cenv.EnvOverrides()
    case_tmp.mkdir(parents=True, exist_ok=True)

    # 1. Reuse the importer via the harness's run_solc_import.
    import_case = {"solc_import": {
        "source": str(source.resolve()),
        "contract": contract,
        "namespace": namespace,
    }}
    variables = _variables(tools, case_tmp, "solidus")
    import_ok, import_status, generated = _HARNESS.run_solc_import(
        import_case, tools.repo, variables, timeout)
    gen_path = case_tmp / "solc-ast.stdout.lean"
    if not import_ok:
        stderr = _read_log(case_tmp / "solc-ast.stderr.log")
        return SolidusResult(
            ok=False, stage="import", fail_closed=True, observable=None,
            message=f"importer {import_status}: {stderr.strip()[:2000]}",
            generated_source_path=gen_path)

    # 2. Build the Lean file: imports + heartbeats + generated + our helper + eval
    args_lean = obs.render_lean_args(args)
    lean_lines = [
        "import SolidCore.Solidity.Checked",
        "import SolidCore.Witness.Checked",
        "set_option maxHeartbeats 8000000",
        "",
        generated,
        "",
        obs.LEAN_OBSERVABLE_HELPER,
        "",
        obs.lean_eval_line(namespace, contract, fuel, fname, args_lean, env),
    ]
    lean_file = case_tmp / "contest_observable.lean"
    lean_file.write_text("\n".join(lean_lines) + "\n", encoding="utf-8")

    stdout_log = case_tmp / "lean.stdout.log"
    stderr_log = case_tmp / "lean.stderr.log"
    command = [tools.lake, "env", "lean", str(lean_file)]
    try:
        status = _HARNESS.run_capture(command, tools.repo, timeout,
                                      stdout_log, stderr_log)
    except subprocess.TimeoutExpired:
        return SolidusResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message=f"lean timeout after {timeout}s",
            generated_source_path=gen_path)

    stdout = _read_log(stdout_log)
    marker = obs.OBSERVABLE_MARKER.strip()
    marker_lines = [ln for ln in stdout.splitlines() if marker in ln]

    if status != 0 and not marker_lines:
        # Elaboration / execution error before the #eval printed => fail-closed.
        stderr = _read_log(stderr_log)
        return SolidusResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message=f"lean exit {status}: {stderr.strip()[:2000]}",
            generated_source_path=gen_path)

    if not marker_lines:
        return SolidusResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message="no observable produced by #eval",
            generated_source_path=gen_path)

    # #eval prints the string quoted, e.g.  "CONTEST_OBS success|w:0"
    # Take everything after the marker, then drop a trailing quote.
    raw = marker_lines[-1]
    payload = raw.split(marker, 1)[1].strip()
    if payload.endswith('"'):
        payload = payload[:-1]
    payload = payload.strip()
    observed = obs.parse_observable(payload)

    if observed.is_solidus_reject:
        return SolidusResult(
            ok=False, stage="run", fail_closed=True, observable=observed,
            message=f"solidus fail-closed: {observed.reject_message}",
            generated_source_path=gen_path)

    return SolidusResult(
        ok=True, stage="run", fail_closed=False, observable=observed,
        message="ran to completion", generated_source_path=gen_path)
