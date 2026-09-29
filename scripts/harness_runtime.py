"""Select only a native runner attested for the current source tree.

The build script writes the attestation after Lake succeeds. Missing/stale
attestations fall back to ordinary Lean; an old binary can never adjudicate a
new semantics tree just because it is still present in .lake/build/bin.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess
import time
from functools import lru_cache


@lru_cache(maxsize=128)
def _local_imports(path: str, metadata: tuple) -> tuple[str, ...]:
    imports = []
    for line in re.findall(r"^(?:(?:public|private|meta) )*import +([^\n]+)",
                           Path(path).read_text(), re.M):
        imports.extend(name for name in line.split()
                       if re.fullmatch(r"SolidCore(?:\.\w+)+", name))
    return tuple(imports)


def source_files(repo: Path) -> list[Path]:
    pending = ["SpecHuntRunner"]
    seen = set()
    files = []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        file = repo / (module.replace(".", "/") + ".lean")
        files.append(file)
        st = file.stat()
        pending.extend(_local_imports(str(file), (st.st_size, st.st_mtime_ns,
                                                  st.st_ctime_ns, st.st_ino)))
    return sorted(files + [repo / x for x in ("lakefile.lean", "lake-manifest.json", "lean-toolchain")])


@lru_cache(maxsize=8)
def _hash_files(entries: tuple) -> str:
    h = hashlib.sha256()
    for path, relative, *_ in entries:
        h.update(relative.encode() + b"\0")
        h.update(Path(path).read_bytes())
        h.update(b"\0")
    return h.hexdigest()


def source_hash(repo: Path) -> str:
    entries = []
    for file in source_files(repo):
        st = file.stat()
        entries.append((str(file), file.relative_to(repo).as_posix(), st.st_size,
                        st.st_mtime_ns, st.st_ctime_ns, st.st_ino))
    return _hash_files(tuple(entries))


@lru_cache(maxsize=8)
def _binary_hash(path: str, metadata: tuple) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def binary_hash(path: Path) -> str:
    st = path.stat()
    return _binary_hash(str(path), (st.st_size, st.st_mtime_ns, st.st_ctime_ns, st.st_ino))


def helper_ready(repo: Path) -> bool:
    """A source edit or stale compiled helper always selects the inline helper."""
    try:
        stamp = json.loads((repo / ".lake/build/bin/specHuntRunner.json").read_text())
        artifact = repo / ".lake/build/lib/lean/SolidCore/Contest/Observable.olean"
        return (stamp["sourceSha256"] == source_hash(repo)
                and stamp["helperSha256"] == binary_hash(artifact))
    except (OSError, ValueError, KeyError, TypeError):
        return False


def lean_command(repo: Path, lake: str, file: Path) -> list[str]:
    fallback = [lake, "env", "lean", str(file)]
    if os.environ.get("CONTEST_NATIVE") == "0":
        return fallback
    binary = repo / ".lake/build/bin/specHuntRunner"
    try:
        stamp = json.loads((binary.parent / "specHuntRunner.json").read_text())
        if (stamp["sourceSha256"] == source_hash(repo)
                and stamp["binarySha256"] == binary_hash(binary)):
            return [lake, "env", str(binary), str(file)]
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return fallback


def run_lean_capture(repo: Path, lake: str, file: Path, timeout: int,
                     stdout: Path, stderr: Path, capture) -> int:
    """Retry native failures in Lean, within the original wall-clock budget.

    Native C can exhaust its stack on a deeply nested input that the IR
    interpreter accepts. Such failures must not invent a new coverage verdict.
    Keep both executions' logs, and never retry an exhausted timeout.
    """
    fallback = [lake, "env", "lean", str(file)]
    command = lean_command(repo, lake, file)
    started = time.monotonic()
    status = capture(command, repo, timeout, stdout, stderr)
    remaining = timeout - (time.monotonic() - started)
    if command == fallback or status == 0 or remaining < 1:
        return status
    for log in (stdout, stderr):
        if log.exists():
            log.replace(log.with_suffix(".native.log"))
    stdout.with_name("native-fallback.json").write_text(json.dumps({
        "nativeExitStatus": status, "remainingSeconds": int(remaining),
        "retry": "ordinary Lean", "source": str(file),
    }, indent=2) + "\n")
    return capture(fallback, repo, int(remaining), stdout, stderr)


if __name__ == "__main__":
    repo = Path(__file__).resolve().parents[1]
    binary = repo / ".lake/build/bin/specHuntRunner"
    if len(sys.argv) != 2 or sys.argv[1] != "build":
        raise SystemExit("usage: harness_runtime.py build")
    before = source_hash(repo)
    subprocess.run([os.environ.get("LAKE", "lake"), "build", "specHuntRunner"],
                   cwd=repo, check=True)
    if source_hash(repo) != before:
        raise SystemExit("sources changed during native build; rebuild before publishing an attestation")
    stamp = {"sourceSha256": source_hash(repo), "binarySha256": binary_hash(binary),
             "helperSha256": binary_hash(repo / ".lake/build/lib/lean/SolidCore/Contest/Observable.olean")}
    (binary.parent / "specHuntRunner.json").write_text(json.dumps(stamp, indent=2) + "\n")
    print(json.dumps(stamp))
