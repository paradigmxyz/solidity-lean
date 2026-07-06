#!/usr/bin/env python3
"""Compare Forge/solc tests with paired Solidity-interpreter witnesses.

This is deliberately shaped like the Forge comparison harness in
`/Users/dan/Projects/evm-compiler`: it pins real solc for the Forge side,
uses a temporary Foundry output/cache directory, keeps logs on failure or when
`KEEP_TMP=1`, and prints machine-readable status lines.

The current Solidity model has a Lean source AST/typechecker/interpreter, not a
native `.sol` parser.  A case may therefore include `solc_import`, which asks
solc for the source AST and renders the supported subset into Lean syntax
before running Lean `#eval` witnesses.  Cases can still use hand-written Lean
witnesses while importer coverage grows.
"""

from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import io
import re
import shutil
import signal
import subprocess
import sys
import threading
import tempfile
from typing import Any

ANSI = re.compile("\\x1b\\[[0-9;]*m")
TEST_LINE = re.compile("^\\[(PASS|FAIL|SKIP)\\]\\s+(.+)$")
SUMMARY = re.compile(
    "^Ran\\s+\\d+\\s+test suites?.*:\\s+(\\d+)\\s+tests?\\s+passed,\\s+(\\d+)\\s+failed,\\s+(\\d+)\\s+skipped"
)
LIST_TEST_LINE = re.compile("^\\s{4}\\S")


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def resolve_executable(name: str, override: str | None) -> str:
    candidate = override or os.environ.get(name.upper()) or name
    if "/" in candidate:
        return candidate
    resolved = shutil.which(candidate)
    return resolved or candidate


def load_manifest(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        manifest = json.load(handle)
    if not isinstance(manifest, dict):
        raise ValueError("manifest root must be a JSON object")
    if not isinstance(manifest.get("cases"), list):
        raise ValueError("manifest must contain a `cases` array")
    return manifest


def expand(text: str, variables: dict[str, str]) -> str:
    for name, value in variables.items():
        text = text.replace("{" + name + "}", value)
    return text


def expand_args(values: list[Any], variables: dict[str, str]) -> list[str]:
    return [expand(str(value), variables) for value in values]


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def run_capture(
    command: list[str],
    cwd: Path,
    timeout: int,
    stdout_log: Path,
    stderr_log: Path,
    env: dict[str, str] | None = None,
) -> int:
    stdout_log.parent.mkdir(parents=True, exist_ok=True)
    stderr_log.parent.mkdir(parents=True, exist_ok=True)
    with stdout_log.open("w", encoding="utf-8") as stdout_handle:
        with stderr_log.open("w", encoding="utf-8") as stderr_handle:
            process = subprocess.Popen(
                command,
                cwd=str(cwd),
                env=env,
                text=True,
                stdout=stdout_handle,
                stderr=stderr_handle,
                start_new_session=True,
            )
            try:
                return process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                raise


def normalized_forge_results(stdout_log: Path, stderr_log: Path) -> list[str]:
    lines = []
    for path in (stdout_log, stderr_log):
        if not path.exists():
            continue
        for raw in path.read_text(errors="replace").splitlines():
            line = ANSI.sub("", raw).strip()
            match = TEST_LINE.match(line)
            if match:
                test_name = re.sub("\\s+\\(gas:\\s*\\d+\\)$", "", match.group(2))
                lines.append(f"{match.group(1)} {test_name}")
                continue
            match = SUMMARY.match(line)
            if not match:
                continue
            lines.append(
                "SUMMARY passed="
                + match.group(1)
                + " failed="
                + match.group(2)
                + " skipped="
                + match.group(3)
            )
    return lines or ["NO_FORGE_TEST_RESULTS_FOUND"]


def forge_list_args(args: list[str]) -> list[str] | None:
    if not args or args[0] != "test":
        return None
    filtered = [arg for arg in args if arg not in ("-q", "--quiet")]
    if "--list" not in filtered and "-l" not in filtered:
        filtered.append("--list")
    return filtered


def count_forge_listed_tests(stdout_log: Path, stderr_log: Path) -> int:
    count = 0
    for path in (stdout_log, stderr_log):
        if not path.exists():
            continue
        for raw in path.read_text(errors="replace").splitlines():
            line = ANSI.sub("", raw).rstrip()
            if LIST_TEST_LINE.match(line):
                count += 1
    return count


def default_forge_args(case: dict[str, Any], variables: dict[str, str]) -> list[str]:
    forge = case.get("forge", {})
    if not isinstance(forge, dict):
        raise ValueError("forge case must be an object")
    root = forge.get("root")
    if not isinstance(root, str):
        raise ValueError("forge.root is required when forge.args is omitted")
    args = [
        "test",
        "--root",
        "{repo}/" + root,
        "--use",
        "{solc}",
        "--no-auto-detect",
        "--offline",
        "--force",
        "--out",
        "{case_tmp}/forge-out",
        "--cache-path",
        "{case_tmp}/forge-cache",
    ]
    match_contract = forge.get("match_contract")
    if isinstance(match_contract, str):
        args.extend(["--match-contract", match_contract])
    match_test = forge.get("match_test")
    if isinstance(match_test, str):
        args.extend(["--match-test", match_test])
    if forge.get("quiet", True):
        args.append("-q")
    return expand_args(args, variables)


def run_forge(
    case: dict[str, Any],
    repo: Path,
    variables: dict[str, str],
    timeout: int,
) -> tuple[bool, str]:
    forge = case.get("forge")
    if forge is None:
        return True, "skipped"
    if not isinstance(forge, dict):
        return False, "invalid forge case"

    args_raw = forge.get("args")
    if args_raw is None:
        args = default_forge_args(case, variables)
    elif isinstance(args_raw, list):
        args = expand_args(args_raw, variables)
    else:
        return False, "invalid forge.args"

    cwd_raw = forge.get("cwd", ".")
    if not isinstance(cwd_raw, str):
        return False, "invalid forge.cwd"
    cwd = Path(expand(cwd_raw, variables))
    if not cwd.is_absolute():
        cwd = repo / cwd

    env = os.environ.copy()
    extra_env = forge.get("env", {})
    if isinstance(extra_env, dict):
        for key, value in extra_env.items():
            env[str(key)] = expand(str(value), variables)

    list_args = forge_list_args(args)
    listed_tests: int | None = None
    if list_args is not None:
        list_command = [variables["forge"], *list_args]
        list_stdout_log = Path(variables["case_tmp"]) / "forge.list.stdout.log"
        list_stderr_log = Path(variables["case_tmp"]) / "forge.list.stderr.log"
        print("  forge_list_cmd=" + " ".join(list_command))
        try:
            list_status = run_capture(
                list_command, cwd, timeout, list_stdout_log, list_stderr_log, env
            )
        except subprocess.TimeoutExpired:
            return False, f"list_timeout_after_{timeout}s"
        if list_status != 0:
            return False, f"list_exit_{list_status}"
        listed_tests = count_forge_listed_tests(list_stdout_log, list_stderr_log)
        write_text(
            Path(variables["case_tmp"]) / "forge.list.results",
            f"DISCOVERED tests={listed_tests}\n",
        )
        if listed_tests == 0:
            return False, "no_tests_discovered"

    command = [variables["forge"], *args]
    stdout_log = Path(variables["case_tmp"]) / "forge.stdout.log"
    stderr_log = Path(variables["case_tmp"]) / "forge.stderr.log"
    print("  forge_cmd=" + " ".join(command))
    try:
        status = run_capture(command, cwd, timeout, stdout_log, stderr_log, env)
    except subprocess.TimeoutExpired:
        return False, f"timeout_after_{timeout}s"

    results = normalized_forge_results(stdout_log, stderr_log)
    if listed_tests is not None:
        results.insert(0, f"DISCOVERED tests={listed_tests}")
        if results == [f"DISCOVERED tests={listed_tests}", "NO_FORGE_TEST_RESULTS_FOUND"]:
            results[1] = "QUIET_FORGE_RESULTS_SUPPRESSED"
    write_text(Path(variables["case_tmp"]) / "forge.results", "\n".join(results) + "\n")
    if status != 0:
        return False, f"exit_{status}"
    return True, "ok"


def run_solc_rejects(
    case: dict[str, Any],
    repo: Path,
    variables: dict[str, str],
    timeout: int,
) -> tuple[bool, str]:
    rejects = case.get("solc_rejects")
    if rejects is None:
        return True, "skipped"
    if not isinstance(rejects, list):
        return False, "invalid"

    case_tmp = Path(variables["case_tmp"])
    results = []
    for index, item in enumerate(rejects):
        if isinstance(item, str):
            source = item
            expected = "Error:"
        elif isinstance(item, dict):
            source = item.get("source")
            expected = item.get("contains", "Error:")
        else:
            return False, f"invalid_entry_{index}"
        if not isinstance(source, str) or not isinstance(expected, str):
            return False, f"invalid_entry_{index}"

        source_path = Path(expand(source, variables))
        if not source_path.is_absolute():
            source_path = repo / source_path
        stdout_log = case_tmp / f"solc-reject-{index}.stdout.log"
        stderr_log = case_tmp / f"solc-reject-{index}.stderr.log"
        command = [variables["solc"], "--bin", str(source_path)]
        print("  solc_reject_cmd=" + " ".join(command))
        try:
            status = run_capture(command, repo, timeout, stdout_log, stderr_log)
        except subprocess.TimeoutExpired:
            return False, f"timeout_{index}_after_{timeout}s"

        output = stdout_log.read_text(errors="replace") + stderr_log.read_text(
            errors="replace"
        )
        if status == 0:
            return False, f"unexpected_accept_{index}"
        if expected not in output:
            return False, f"missing_diagnostic_{index}_{expected}"
        results.append(f"REJECT {source_path.relative_to(repo)}")

    write_text(case_tmp / "solc-reject.results", "\n".join(results) + "\n")
    return True, "ok"


def run_solc_import(
    case: dict[str, Any],
    repo: Path,
    variables: dict[str, str],
    timeout: int,
) -> tuple[bool, str, str]:
    solc_import = case.get("solc_import")
    if solc_import is None:
        return True, "skipped", ""
    if not isinstance(solc_import, dict):
        return False, "invalid", ""

    source = solc_import.get("source")
    contract = solc_import.get("contract")
    namespace = solc_import.get(
        "namespace",
        "SolidCore.Solidity.SolcAstImport.Generated",
    )

    if not isinstance(source, str) or not isinstance(contract, str):
        return False, "missing_source_or_contract", ""
    if not isinstance(namespace, str):
        return False, "invalid_namespace", ""

    source_path = Path(expand(source, variables))
    if not source_path.is_absolute():
        source_path = repo / source_path

    case_tmp = Path(variables["case_tmp"])
    stdout_log = case_tmp / "solc-ast.stdout.lean"
    stderr_log = case_tmp / "solc-ast.stderr.log"

    command = [
        sys.executable,
        str(repo / "scripts" / "solc_ast_to_lean_source.py"),
        str(source_path),
        "--contract",
        contract,
        "--solc",
        variables["solc"],
        "--namespace",
        namespace,
        "--body-only",
    ]

    print("  solc_ast_cmd=" + " ".join(command))
    try:
        status = run_capture(command, repo, timeout, stdout_log, stderr_log)
    except subprocess.TimeoutExpired:
        return False, f"timeout_after_{timeout}s", ""
    if status != 0:
        return False, f"exit_{status}", ""
    return True, "ok", stdout_log.read_text(encoding="utf-8")


def run_lean(
    case: dict[str, Any],
    repo: Path,
    variables: dict[str, str],
    timeout: int,
) -> tuple[bool, str]:
    lean = case.get("lean")
    if lean is None:
        return True, "skipped"
    if not isinstance(lean, dict):
        return False, "invalid lean case"

    imports = lean.get("imports", [])
    if isinstance(lean.get("import"), str):
        imports = [lean["import"]]
    if not isinstance(imports, list):
        return False, "invalid lean.imports"

    evals = lean.get("evals", [])
    if not isinstance(evals, list):
        return False, "invalid lean.evals"

    import_ok, import_status, generated_source = run_solc_import(
        case,
        repo,
        variables,
        timeout,
    )
    if not import_ok:
        return False, f"solc_ast_{import_status}"

    lean_lines = [f"import {item}" for item in imports]
    if generated_source:
        lean_lines.append("")
        lean_lines.append(generated_source)

    expected = []
    labels = []
    for item in evals:
        if not isinstance(item, dict):
            return False, "invalid lean eval"
        expr = item.get("expr")
        expect = item.get("expect")
        if not isinstance(expr, str) or not isinstance(expect, str):
            return False, "lean eval needs expr and expect strings"
        lean_lines.append(f"#eval {expr}")
        expected.append(expect)
        labels.append(str(item.get("label", expr)))

    case_tmp = Path(variables["case_tmp"])
    lean_file = case_tmp / "interpreter.lean"
    write_text(lean_file, "\n".join(lean_lines) + "\n")
    stdout_log = case_tmp / "lean.stdout.log"
    stderr_log = case_tmp / "lean.stderr.log"
    command = [variables["lake"], "env", "lean", str(lean_file)]
    print("  lean_cmd=" + " ".join(command))
    try:
        status = run_capture(command, repo, timeout, stdout_log, stderr_log)
    except subprocess.TimeoutExpired:
        return False, f"timeout_after_{timeout}s"

    if status != 0:
        return False, f"exit_{status}"

    actual = [line.strip() for line in stdout_log.read_text().splitlines() if line.strip()]
    actual_tail = actual[-len(expected) :] if expected else []
    write_text(
        case_tmp / "lean.results",
        "\n".join(
            f"{label}: {value}"
            for label, value in zip(labels, actual_tail)
        )
        + ("\n" if expected else ""),
    )

    if actual_tail != expected:
        return False, f"expected_{expected}_got_{actual_tail}"
    return True, "ok"


def print_failure_logs(case_tmp: Path) -> None:
    for name in (
        "forge.list.results",
        "forge.results",
        "forge.list.stdout.log",
        "forge.list.stderr.log",
        "lean.results",
        "forge.stdout.log",
        "forge.stderr.log",
        "solc-ast.stdout.lean",
        "solc-ast.stderr.log",
        "lean.stdout.log",
        "lean.stderr.log",
    ):
        path = case_tmp / name
        if not path.exists() or not path.stat().st_size:
            continue
        print(f"--- {path} ---")
        print(path.read_text(errors="replace").rstrip())
    for path in sorted(case_tmp.glob("solc-reject-*.stderr.log")):
        if not path.stat().st_size:
            continue
        print(f"--- {path} ---")
        print(path.read_text(errors="replace").rstrip())


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        default="tests/forge-harness/manifest.json",
        help="JSON manifest, relative to the repository root by default",
    )
    parser.add_argument("--only", action="append", default=[], help="case name")
    parser.add_argument("--skip-forge", action="store_true")
    parser.add_argument("--skip-lean", action="store_true")
    parser.add_argument("--forge", help="forge executable")
    parser.add_argument("--solc", help="solc executable for Forge")
    parser.add_argument("--lake", help="lake executable")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--jobs", type=int, default=1,
                        help="run cases concurrently (default 1 = sequential)")
    parser.add_argument("--keep-tmp", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    repo = repo_root()
    parser = build_parser()
    args = parser.parse_args(argv)
    manifest_path = Path(args.manifest)
    if not manifest_path.is_absolute():
        manifest_path = repo / manifest_path

    try:
        manifest = load_manifest(manifest_path)
        forge = resolve_executable("forge", args.forge)
        solc = resolve_executable("solc", args.solc)
        lake = resolve_executable("lake", args.lake)
    except Exception as exc:
        print("forge_interpreter_compare=fail")
        print(f"error={exc}")
        return 2

    keep_tmp = args.keep_tmp or os.environ.get("KEEP_TMP") == "1"
    outdir = Path(
        tempfile.mkdtemp(
            prefix="solid-core-forge-interpreter.",
            dir=os.environ.get("TMPDIR") or None,
        )
    )

    selected = set(args.only)
    failures = []
    ran = 0

    # Thread-safe stdout routing: each worker thread stashes a per-case buffer in
    # thread-local state; the router sends writes to that buffer (or the real
    # stdout when none is set). This avoids `redirect_stdout`, which swaps the
    # process-global stdout and corrupts capture across concurrent threads.
    class _ThreadRoutingStdout:
        def __init__(self, real):
            self._real = real
            self._local = threading.local()

        def set_buffer(self, buf):
            self._local.buf = buf

        def clear_buffer(self):
            self._local.buf = None

        def write(self, s):
            buf = getattr(self._local, "buf", None)
            (buf if buf is not None else self._real).write(s)

        def flush(self):
            buf = getattr(self._local, "buf", None)
            (buf if buf is not None else self._real).flush()

    router = _ThreadRoutingStdout(sys.stdout)

    def run_case(case):
        """Run one case, capturing its stdout (via the thread-routing stdout) so
        parallel workers don't interleave. Returns
        (name, ran_delta, output, failure_tuple_or_None)."""
        if not isinstance(case, dict) or not isinstance(case.get("name"), str):
            return (
                "<invalid>",
                0,
                "",
                ("<invalid>", outdir / "invalid_case",
                 "invalid_case", "invalid_case", "invalid_case"),
            )

        name = case["name"]
        if selected and name not in selected:
            return (name, 0, "", None)

        buf = io.StringIO()
        router.set_buffer(buf)
        try:
            case_tmp = outdir / re.sub("[^A-Za-z0-9_.-]+", "_", name)
            case_tmp.mkdir(parents=True, exist_ok=True)
            case_timeout = case.get("timeout", args.timeout)
            if not isinstance(case_timeout, int) or case_timeout <= 0:
                return (
                    name, 1, buf.getvalue(),
                    (name, case_tmp, "invalid_timeout",
                     "invalid_timeout", "invalid_timeout"),
                )

            variables = {
                "repo": str(repo),
                "outdir": str(outdir),
                "case_tmp": str(case_tmp),
                "forge": forge,
                "solc": solc,
                "lake": lake,
                "case": name,
            }

            print(f"case={name}")
            solc_ok, solc_status = run_solc_rejects(
                case, repo, variables, case_timeout
            )
            forge_ok, forge_status = (
                (True, "skipped")
                if args.skip_forge
                else run_forge(case, repo, variables, case_timeout)
            )
            lean_ok, lean_status = (
                (True, "skipped")
                if args.skip_lean
                else run_lean(case, repo, variables, case_timeout)
            )
            print(
                f"case_result={name} solc_rejects={solc_status} forge="
                f"{forge_status} lean={lean_status}"
            )
        finally:
            router.clear_buffer()

        failure = (
            None if (solc_ok and forge_ok and lean_ok)
            else (name, case_tmp, solc_status, forge_status, lean_status)
        )
        return (name, 1, buf.getvalue(), failure)

    saved_stdout = sys.stdout
    sys.stdout = router
    try:
        cases = manifest["cases"]
        jobs = max(1, args.jobs)
        if jobs == 1:
            results = [run_case(case) for case in cases]
        else:
            # Preserve manifest order in the output while running concurrently.
            from concurrent.futures import ThreadPoolExecutor
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                results = list(pool.map(run_case, cases))

        sys.stdout = saved_stdout
        for _name, ran_delta, output, failure in results:
            ran += ran_delta
            if output:
                sys.stdout.write(output)
            if failure is not None:
                failures.append(failure)

        if failures:
            print("forge_interpreter_compare=fail")
            print("status=1")
            print(f"cases={ran}")
            print(f"tmp={outdir}")
            for name, case_tmp, solc_status, forge_status, lean_status in failures:
                print(
                    f"failure={name} solc_rejects={solc_status} forge="
                    f"{forge_status} lean={lean_status}"
                )
                print_failure_logs(case_tmp)
            return 1

        print("forge_interpreter_compare=pass")
        print("status=0")
        print(f"cases={ran}")
        print("paired_cases_passed=yes")
        if keep_tmp:
            print(f"tmp={outdir}")
        else:
            print("logs_kept=no")
        return 0
    finally:
        sys.stdout = saved_stdout
        if failures or keep_tmp:
            if failures and not keep_tmp:
                print(f"kept_tmp={outdir}", file=sys.stderr)
        else:
            shutil.rmtree(outdir, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
