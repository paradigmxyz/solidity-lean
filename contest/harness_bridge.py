#!/usr/bin/env python3
"""Thin bridge over scripts/run_forge_interpreter_harness.py (design §5.2).

Reuses the harness's PROVEN Forge/solc/import/lean invocations rather than
reinventing them:

  * ``run_forge``        - compile with pinned solc + run the Foundry test.
  * ``run_solc_rejects`` - assert solc REJECTS a source (OVER_ACCEPT claims).
  * ``run_solc_import``  - invoke solc_ast_to_lean_source.py to render Lean.

For the solidity-lean observable we reuse ``run_solc_import`` to obtain the generated
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


# The repo root used for the Lean/lake build, the importer, and the harness
# scripts. Normally the checkout this package lives in. When the contest code is
# run from a git WORKTREE (whose sibling `../evm-interaction` and `.lake` build
# are absent), set CONTEST_REPO_ROOT to a fully-built checkout so lean/forge
# resolve there while the Python package still loads from the worktree.
_REPO_ROOT = Path(
    os.environ.get("CONTEST_REPO_ROOT") or Path(__file__).resolve().parents[1])
def _resolve_tool(env_var: str, pinned: str, exe: str) -> str:
    """Resolve a required external tool so the harness runs on any machine.

    Order: explicit ``$env_var`` (an absolute path you pass in) → the pinned
    local path if it exists (the maintainer's box) → whatever is on ``PATH`` →
    the pinned literal as a last resort. External users: install pinned solc
    0.8.35 (``solc-select use 0.8.35``) + Foundry so they land on ``PATH``, or
    set ``SOLC``/``FORGE`` (or pass ``--solc``/``--forge``). See SUBMITTING.md.
    NOTE: the contest requires solc **0.8.35** specifically — a different solc
    on PATH will silently produce wrong verdicts, so prefer ``solc-select`` or
    the explicit env var / flag."""
    v = os.environ.get(env_var)
    if v:
        return v
    if os.path.exists(pinned):
        return pinned
    return shutil.which(exe) or pinned


DEFAULT_SOLC = _resolve_tool(
    "SOLC", "/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35", "solc")
DEFAULT_FORGE = _resolve_tool("FORGE", "/Users/dan/.foundry/bin/forge", "forge")
DEFAULT_LAKE = os.environ.get("LAKE") or shutil.which("lake") or "lake"


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

# A pinned, sandboxed Foundry profile for running UNTRUSTED submitter tests
# (adversarial-review finding 1): `ffi` disabled and `fs_permissions` empty, so
# a submitter's `foundry.toml` can NOT re-enable arbitrary host-process
# execution or filesystem access. We never run the submitter's own toml.
_SANDBOX_FOUNDRY_TOML = (
    "[profile.default]\n"
    "src = \"src\"\n"
    "test = \"test\"\n"
    "evm_version = \"cancun\"\n"
    "ffi = false\n"
    "fs_permissions = []\n"
)


def run_forge_test(forge_root: Path, case_tmp: Path,
                   match_contract: Optional[str] = None,
                   match_test: Optional[str] = None,
                   tools: Optional[ToolPaths] = None,
                   timeout: int = 300) -> tuple[bool, str]:
    """Run the submission's Forge test in a SANDBOXED copy of the project.

    ``forge_root`` is the submission's Foundry project dir. We copy only its
    ``src/`` and ``test/`` into a fresh project with a harness-generated
    ``foundry.toml`` (``ffi`` off, ``fs_permissions`` empty) so the submitter's
    own config cannot enable ffi/FS access on the adjudication host."""
    tools = tools or ToolPaths()
    case_tmp.mkdir(parents=True, exist_ok=True)
    proj = case_tmp / "sandbox_proj"
    if proj.exists():
        shutil.rmtree(proj)
    proj.mkdir(parents=True)
    for sub in ("src", "test"):
        srcdir = forge_root / sub
        if srcdir.is_dir():
            shutil.copytree(srcdir, proj / sub)
    (proj / "foundry.toml").write_text(_SANDBOX_FOUNDRY_TOML)

    command = [
        tools.forge, "test",
        "--root", str(proj.resolve()),
        "--use", tools.solc,
        "--no-auto-detect", "--offline", "--force",
        "--out", str((case_tmp / "forge-out").resolve()),
        "--cache-path", str((case_tmp / "forge-cache").resolve()),
        "-q",
    ]
    if match_contract:
        command += ["--match-contract", match_contract]
    if match_test:
        command += ["--match-test", match_test]
    stdout_log = case_tmp / "forge.stdout.log"
    stderr_log = case_tmp / "forge.stderr.log"
    try:
        status = _HARNESS.run_capture(command, tools.repo, timeout,
                                      stdout_log, stderr_log)
    except subprocess.TimeoutExpired:
        return False, f"timeout_after_{timeout}s"
    except Exception as exc:  # missing forge binary / OS error: INFRA, not the
        # submission failing — the caller routes infra statuses to NEEDS_REVIEW
        # instead of a terminal INVALID (release audit: fail-open to review,
        # never silently invalidate a valid submission on a broken toolchain).
        return False, f"infra_error: {exc}"
    if status == 0:
        return True, "pass"
    tail = (_read_log(stdout_log) + _read_log(stderr_log))[-800:]
    return False, f"forge_exit_{status}: {tail}"


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
# solidity-lean (import + typecheck + elaborate + execute; observable extraction)
# ---------------------------------------------------------------------------

@dataclass
class SolidityLeanResult:
    """The outcome of running solidity-lean on the entry call."""

    ok: bool                     # True if the entry call ran to completion
    stage: str                   # "import" | "lean" | "run"
    fail_closed: bool            # True if solidity-lean rejected (coverage-gap candidate)
    observable: Optional[obs.Observable]
    message: str                 # evidence / error text
    generated_source_path: Optional[Path] = None
    # True if the Lean run TIMED OUT or otherwise failed inconclusively (not a
    # clean importer/typecheck reject). Adjudicated as NEEDS_REVIEW, never as an
    # automatic coverage gap (adversarial-review finding 3): a resource-exhaustion
    # failure is not evidence of a missing feature.
    inconclusive: bool = False


def _read_log(path: Path) -> str:
    try:
        return path.read_text(errors="replace")
    except OSError:
        return ""


# Substrings in Lean's stderr that mark a NON-program failure: the run is
# inconclusive, not evidence of a missing solidity-lean feature. Two families:
#  * RESOURCE exhaustion — a slow-but-correct run, an attacker resource bomb, or
#    a poisoned `fuel`.
#  * BUILD / TOOLCHAIN / ENVIRONMENT — the generated file imports ONLY the fixed
#    SolidCore.* modules, so a package/import/toolchain resolution failure is an
#    environment problem (stale build, wrong cwd, missing sibling dependency),
#    never Lean rejecting the imported PROGRAM. Misclassifying either as a clean
#    fail-closed would mint a bogus qualifying COVERAGE_GAP from a flaky build
#    (found via a worktree run where `../evm-interaction` was absent).
_INCONCLUSIVE_LEAN_SIGNATURES: tuple[str, ...] = (
    # resource
    "deep recursion", "maximum recursion", "out of memory",
    "deterministic timeout", "(interrupted)", "stack overflow",
    "excessive memory",
    # build / toolchain / environment
    "package directory not found", "unknown package",
    "no such file or directory", "failed to load",
    "could not resolve import", "unknown module",
    "error: build failed", "lake:", "toolchain",
    "unknown constant 'solidcore", "unknown identifier 'solidcore",
    "unknown namespace 'solidcore",
)


def lean_failure_inconclusive(stderr: str) -> bool:
    """True iff a non-zero Lean exit should be treated as INCONCLUSIVE (routed to
    human review) rather than auto-qualified as a coverage gap.

    DEFAULT-INCONCLUSIVE (audit finding, CONTEST-BREAKING). The old design was an
    allow-list of "noise" signatures that returned inconclusive ONLY on a match,
    defaulting everything else to a qualifying COVERAGE_GAP — i.e. it FAILED OPEN:
    an OOM-killer SIGKILL (status 137, empty stderr), "no space left on device",
    a Lean PANIC / libc++abi abort, a segfault, or an `elan` toolchain error all
    produced NO listed signature and were minted as fake gaps.

    A non-zero Lean exit here happens ONLY AFTER a SUCCESSFUL import (an importer
    reject returns earlier with stage="import"), and the observable helper catches
    program-level `Except.error`s and PRINTS them as a `solidity-lean-reject`
    (exit 0 WITH the marker, handled separately). So a non-zero exit with no marker is a
    failure of the Lean toolchain / our generated harness / a resource limit —
    NOT Lean cleanly rejecting the submitted program. We therefore default to
    inconclusive. The signature list is retained only as documentation of the
    common noise shapes; the classification no longer depends on matching it."""
    return True


def _unescape_lean_repr(s: str) -> str:
    """Reverse Lean's `Repr String` / `String.quote` escaping of the #eval output.

    Handles the escapes Lean emits: ``\\\\`` ``\\"`` ``\\'`` ``\\n`` ``\\t`` ``\\r``
    and ``\\u{HHHH}``. A backslash is processed once (so ``\\\\n`` -> a literal
    backslash then ``n``, never a newline). An unrecognized escape keeps the
    following character verbatim (drops the backslash)."""
    if "\\" not in s:
        return s
    out: list[str] = []
    i, n = 0, len(s)
    simple = {"\\": "\\", '"': '"', "'": "'", "n": "\n", "t": "\t", "r": "\r"}
    while i < n:
        c = s[i]
        if c != "\\" or i + 1 >= n:
            out.append(c)
            i += 1
            continue
        nxt = s[i + 1]
        if nxt == "u" and i + 2 < n and s[i + 2] == "{":
            close = s.find("}", i + 3)
            if close != -1:
                try:
                    out.append(chr(int(s[i + 3:close], 16)))
                    i = close + 1
                    continue
                except ValueError:
                    pass
            out.append(nxt)
            i += 2
        elif nxt in simple:
            out.append(simple[nxt])
            i += 2
        else:
            out.append(nxt)
            i += 2
    return "".join(out)


def run_solidity_lean_observable(source: Path, contract: str, fname: str, args: list,
                           case_tmp: Path, namespace: str,
                           fuel: int = 64,
                           tools: Optional[ToolPaths] = None,
                           timeout: int = 300,
                           env: Optional["cenv.EnvOverrides"] = None,
                           slots: Optional[list[int]] = None,
                           constructor_args: Optional[list] = None,
                           inject_storage: Optional[list[tuple[int, int]]] = None,
                           calldata_hex: Optional[str] = None,
                           param_types: Optional[list[str]] = None,
                           ctor_param_types: Optional[list[str]] = None,
                           structs: Optional[dict[str, list[str]]] = None,
                           ) -> SolidityLeanResult:
    """Import ``source``, then #eval the §3.4 observable of ``contract.fname``.

    Distinguishes:
      * importer fail()            -> fail_closed, stage=import (coverage-gap)
      * lean exit != 0             -> fail_closed, stage=lean   (elab/exec reject)
      * observable "solidity-lean-reject" -> fail_closed, stage=run   (typecheck reject)
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
    variables = _variables(tools, case_tmp, "solidity_lean")
    import_ok, import_status, generated = _HARNESS.run_solc_import(
        import_case, tools.repo, variables, timeout)
    gen_path = case_tmp / "solc-ast.stdout.lean"
    if not import_ok:
        stderr = _read_log(case_tmp / "solc-ast.stderr.log")
        return SolidityLeanResult(
            ok=False, stage="import", fail_closed=True, observable=None,
            message=f"importer {import_status}: {stderr.strip()[:2000]}",
            generated_source_path=gen_path)

    # 2. Build the Lean file: imports + heartbeats + generated + our helper + eval
    # TYPE-DIRECTED arg rendering (register >= 1.4.0): with the entry/ctor
    # parameter typeStrings, JSON-list args render as Value.dynamicArray/
    # fixedArray/tuple — the same CoreValues solidity-lean's own ABI decode
    # produces — so array/struct params reach the model as the SAME logical
    # call the EVM decodes from the calldata bytes (X-ARGVAL retired).
    args_lean = obs.render_lean_args(args, types=param_types, structs=structs)
    ctor_args_lean = obs.render_lean_args(constructor_args or [],
                                          types=ctor_param_types,
                                          structs=structs)
    lean_lines = [
        "import SolidCore.Solidity.Checked",
        "import SolidCore.Witness.Checked",
        "set_option maxHeartbeats 8000000",
        "",
        generated,
        "",
        obs.LEAN_OBSERVABLE_HELPER,
        "",
        obs.lean_eval_line(namespace, contract, fuel, fname, args_lean, env,
                           slots=slots, ctor_args_lean=ctor_args_lean,
                           inject_storage=inject_storage,
                           calldata_hex=calldata_hex),
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
        # A timeout is INCONCLUSIVE, not a coverage gap (review finding 3): it
        # may be a genuinely slow-but-correct run, an attacker resource bomb, or
        # a poisoned `fuel`. Never auto-classify it as a missing feature.
        return SolidityLeanResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message=f"lean timeout after {timeout}s", inconclusive=True,
            generated_source_path=gen_path)

    stdout = _read_log(stdout_log)
    marker = obs.OBSERVABLE_MARKER.strip()
    marker_lines = [ln for ln in stdout.splitlines() if marker in ln]

    if status != 0 and not marker_lines:
        # Lean exited non-zero before the #eval printed. This can be a genuine
        # elaboration/typecheck reject of the IMPORTED PROGRAM (a coverage gap),
        # or a failure of our generated harness / a resource issue (inconclusive).
        # We only treat it as fail-closed here; the adjudicator decides coverage
        # vs. needs-review from the reason class + stderr signals below.
        stderr = _read_log(stderr_log)
        return SolidityLeanResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message=f"lean exit {status}: {stderr.strip()[:2000]}",
            inconclusive=lean_failure_inconclusive(stderr),
            generated_source_path=gen_path)

    if not marker_lines:
        # Exit 0 but the #eval printed no observable marker: the helper never ran
        # to a rendered result (truncated output / OOM before print / a harness
        # bug), NOT a clean program reject (those print `solidity-lean-reject`).
        # Treat as INCONCLUSIVE, never a coverage gap (audit finding: this fell
        # through to fail_closed with inconclusive=False and was minted as a fake gap).
        return SolidityLeanResult(
            ok=False, stage="lean", fail_closed=True, observable=None,
            message="no observable produced by #eval", inconclusive=True,
            generated_source_path=gen_path)

    # #eval prints the string quoted, e.g.  "CONTEST_OBS success|w:0"
    # Take everything after the marker, then drop a trailing quote.
    raw = marker_lines[-1]
    payload = raw.split(marker, 1)[1].strip()
    if payload.endswith('"'):
        payload = payload[:-1]
    # Reverse Lean's `Repr String` escaping (audit finding): the only
    # submitter-controlled free text in the observable is a revert `Error(string)`
    # / custom-error string, and Lean prints it escaped (`a"b` -> `a\"b`, newlines
    # -> `\n`). The EVM side decodes the SAME message byte-accurately, so without
    # un-escaping a revert string containing `"`, `\`, or a control char produced a
    # spurious `wrong-revert` SOUNDNESS_GAP. The rest of the observable is
    # numeric/hex/structural and contains no backslashes, so this is a no-op there.
    payload = _unescape_lean_repr(payload)
    payload = payload.strip()
    observed = obs.parse_observable(payload)

    if observed.is_solidity_lean_reject:
        return SolidityLeanResult(
            ok=False, stage="run", fail_closed=True, observable=observed,
            message=f"solidity_lean fail-closed: {observed.reject_message}",
            generated_source_path=gen_path)

    return SolidityLeanResult(
        ok=True, stage="run", fail_closed=False, observable=observed,
        message="ran to completion", generated_source_path=gen_path)
