#!/usr/bin/env python3
"""The generic negative suite, run through the generic certification driver.

negatives.py --certify CMD [--replay CMD] [--work DIR] [--table OUT.md]

CMD is the driver's command line (split by the shell), run as
    CMD <source.sol> --out <dir>
from the repository root. The driver's verdict is the first word of the last line of its output
that starts with CERTIFIED, BLOCKED or REJECTED (any case), with the reason after it; no such line,
or a nonzero exit with CERTIFIED, counts as ERROR. A case passes when the verdict is the expected
one, and every case expected not to certify passes only when the driver does not print CERTIFIED.

--replay CMD runs the cold replay of a finished run's directory, as
    CMD <dir>
The replay cases certify tests/heldout/Clamp.sol once, then copy its directory per case, change one
pinned input in the copy and replay it: stale bytes (the runtime bytes of another contract's fresh
compile), a flipped byte, changed solar options in the recorded pins, a stale spec (the source's
spec edited after the run), stale source (its code edited), a stale import (a generated module of
the run edited after it), an omitted selector (one dropped from the recorded entrypoints), a false
environment pin, and a lowered gas bound (out of gas passed off as a revert).
Every case runs the same driver command on the same tree: the table records the commit and the
driver's hash before and after, and the suite fails if they differ.
Each must be refused. Without --replay those cases are reported as not run.

Exits 0 iff every case that ran passed.
"""
import argparse, json, pathlib, re, shlex, shutil, subprocess, sys, time

H = "tests/heldout"
FRESH = [
    # name, source, expected, what it tests
    ("heldout-clamp", f"{H}/Clamp.sol", "CERTIFIED", "positive control: held-out, no hand-written proofs"),
    ("heldout-stepsum", f"{H}/StepSum.sol", "CERTIFIED", "positive control: loop with supplied invariant"),
    ("heldout-registry", f"{H}/Registry.sol", "CERTIFIED", "positive control: mapping, owner check, event"),
    ("renamed-new-constants", f"{H}/Band.sol", "CERTIFIED", "Clamp renamed, constants in place of stored bounds"),
    ("empty-revert", f"{H}/EmptyRevert.sol", "CERTIFIED", "empty revert next to a bounded loop (revert, not OOG)"),
    ("wrong-spec", f"{H}/negative/ClampWrongSpec.sol", "REJECTED", "postcondition false of the code"),
    ("false-env", f"{H}/negative/FalseEnv.sol", "REJECTED", "contradictory environment premise (vacuous)"),
    ("invalid-initial-invariant", f"{H}/negative/InitBroken.sol", "REJECTED", "constructor does not establish the invariant"),
    ("entrypoint-breaks-invariant", f"{H}/negative/InvBroken.sol", "REJECTED", "a second entrypoint breaks the invariant"),
    ("sibling-goal-isolation", f"{H}/negative/SiblingFns.sol", "REJECTED",
     "a sibling function's premise or proof state must not reach another's goal"),
    ("sibling-isolation", f"{H}/negative/SiblingLeak.sol", "REJECTED",
     "postcondition provable only if a sibling branch's assumption leaks"),
    ("sibling-isolation-control", f"{H}/negative/SiblingOk.sol", "CERTIFIED", "control of sibling-isolation"),
    ("unsupported-external-call", f"{H}/blocked/ExternalCall.sol", "BLOCKED", "external call"),
    ("unsupported-reentrancy", f"{H}/blocked/Reentrancy.sol", "BLOCKED", "value call, state written after it"),
    ("unsupported-delegatecall", f"{H}/blocked/Delegatecall.sol", "BLOCKED", "delegatecall"),
    ("unsupported-assembly", f"{H}/blocked/Assembly.sol", "BLOCKED", "inline assembly"),
]
REPLAY = ["stale-bytes", "flipped-byte", "changed-solar-options", "stale-spec-hash", "stale-source", "stale-import",
          "omitted-selector", "false-env-pin", "oog-as-revert"]
VERDICT = re.compile(r"^\s*(CERTIFIED|BLOCKED|REJECTED)\b[:\s]*(.*)$", re.I)


def run(cmd, log):
    t = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    out = r.stdout + r.stderr
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(shlex.join(cmd) + "\n" + out)
    verdict, reason = "ERROR", ""
    for line in out.splitlines():
        m = VERDICT.match(line)
        if m:
            verdict, reason = m.group(1).upper(), m.group(2).strip()
    if verdict == "CERTIFIED" and r.returncode != 0:
        verdict, reason = "ERROR", f"CERTIFIED with exit {r.returncode}"
    if verdict == "ERROR" and not reason:
        tail = [l for l in out.strip().splitlines() if l.strip()]
        reason = f"exit {r.returncode}: " + (tail[-1][:140] if tail else "no output")
    return verdict, reason, r.returncode, round(time.time() - t)


def files(d, pat):
    return sorted(p for p in pathlib.Path(d).rglob(pat) if p.is_file())


def flip_hex(s, i=None):
    i = len(s) // 2 // 2 * 2 if i is None else i
    return s[:i] + f"{int(s[i:i + 2], 16) ^ 1:02x}" + s[i + 2:]


def mutate_replay(case, d, other_bin):
    """Change one pinned input of a finished run's directory d; return what changed."""
    mans = [p for p in files(d, "*.json") if '"bytecode"' in p.read_text()]
    if case in ("stale-bytes", "flipped-byte"):
        if not mans:
            return None
        changed = []
        for p in mans:
            j = json.loads(p.read_text())
            old = j["bytecode"]
            j["bytecode"] = other_bin if case == "stale-bytes" else flip_hex(old)
            p.write_text(json.dumps(j, indent=2))
            changed.append(str(p.relative_to(d)))
        for p in files(d, "Bytecode.lean"):
            t = p.read_text()
            lb, rb = t.index("[", t.index("def bytecode")), t.index("]", t.index("def bytecode"))
            hexs = "".join(f"{int(x, 16):02x}" for x in re.findall(r"0x([0-9a-fA-F]{1,2})", t[lb:rb]))
            new = other_bin if case == "stale-bytes" else flip_hex(hexs)
            bs = [new[i:i + 2] for i in range(0, len(new), 2)]
            p.write_text(t[:lb] + "[" + ", ".join("0x" + b for b in bs) + "]" + t[rb + 1:])
            changed.append(str(p.relative_to(d)))
        return ("bytes of another contract's fresh compile" if case == "stale-bytes" else "middle byte XOR 1") \
            + " in " + ", ".join(changed)
    if case == "changed-solar-options":
        for p in files(d, "*.json"):
            j = json.loads(p.read_text())
            for k in ("solar_options", "options", "optimization"):
                if k in j:
                    j[k] = (j[k] + ["-O0"]) if isinstance(j[k], list) else \
                        (not j[k] if isinstance(j[k], bool) else str(j[k]) + " -O0")
                    p.write_text(json.dumps(j, indent=2))
                    return f"{p.relative_to(d)}: {k} changed"
        return None
    if case == "stale-spec-hash":
        for p in files(d, "*.sol"):
            t = p.read_text()
            if "@custom:ensures" in t:
                p.write_text(t.replace("@custom:ensures result >= a", "@custom:ensures result >= a + 0", 1))
                return f"{p.relative_to(d)}: one ensures clause edited"
        return None
    if case == "stale-source":
        for p in files(d, "*.sol"):
            t = p.read_text()
            if "if (x > b) return b;" in t:
                p.write_text(t.replace("if (x > b) return b;", "if (x >= b) return b;", 1))
                return f"{p.relative_to(d)}: one comparison of the code edited (same behaviour, other bytes)"
        return None
    if case in ("omitted-selector", "false-env-pin", "oog-as-revert"):
        keys = {"omitted-selector": ("selectors", "functions", "entrypoints"),
                "false-env-pin": ("env", "environment", "evm_version", "chain_id"),
                "oog-as-revert": ("gas", "gas_bound", "gasBound")}[case]
        for p in files(d, "*.json"):
            try:
                j = json.loads(p.read_text())
            except ValueError:
                continue
            for k in keys:
                if k not in j:
                    continue
                v = j[k]
                if case == "omitted-selector" and isinstance(v, (list, dict)) and len(v) > 1:
                    if isinstance(v, list):
                        j[k] = v[1:]
                    else:
                        j[k] = dict(list(v.items())[1:])
                elif case == "false-env-pin":
                    j[k] = ({**v, "chain_id": 0, "caller": 0} if isinstance(v, dict) else
                            ("london" if v != "london" else "cancun") if isinstance(v, str) else (v or 0) + 1)
                elif case == "oog-as-revert" and isinstance(v, int) and v > 0:
                    j[k] = v // 2
                else:
                    continue
                p.write_text(json.dumps(j, indent=2))
                return f"{p.relative_to(d)}: {k} changed"
        return None
    if case == "stale-import":
        for p in files(d, "*.lean"):
            t = p.read_text()
            if "def bytecode" not in t and re.search(r"^import ", t, re.M):
                p.write_text(t + "\n-- edited after the run\n")
                return f"{p.relative_to(d)}: comment appended"
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--certify", required=True)
    ap.add_argument("--replay", default=None)
    ap.add_argument("--work", default=".lake/negatives")
    ap.add_argument("--table", default=None)
    ap.add_argument("--only", default=None)
    ap.add_argument("--solar", default=None, help="solar for the stale-bytes compile (default: the driver's)")
    a = ap.parse_args()
    work = pathlib.Path(a.work).resolve()
    certify = shlex.split(a.certify)
    drv = pathlib.Path(certify[0])
    drv_hash = lambda: subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip() + ":" + \
        (__import__("hashlib").sha256(drv.read_bytes()).hexdigest() if drv.is_file() else "")
    drv_before = drv_hash()
    rows = []
    want = set(a.only.split(",")) if a.only else None
    clamp_dir = None
    for name, src, exp, what in FRESH:
        if want and name not in want and not (name == "heldout-clamp" and a.replay):
            continue
        out = work / name
        if out.exists():
            shutil.rmtree(out)
        v, reason, rc, wall = run(certify + [src, "--out", str(out)], work / "log" / f"{name}.txt")
        ok = v == exp
        rows.append((name, what, exp, v, reason, ok, wall))
        if name == "heldout-clamp" and v == "CERTIFIED":
            clamp_dir = out
        print(f"{name}: expected {exp}, got {v} ({reason}) in {wall} s", flush=True)
    for case in REPLAY:
        if want and case not in want:
            continue
        if not a.replay or clamp_dir is None:
            rows.append((case, "replay of the certified Clamp run with one input changed", "REJECTED", "NOT RUN",
                         "no replay command" if not a.replay else "Clamp did not certify", None, 0))
            continue
        d = work / ("replay-" + case)
        if d.exists():
            shutil.rmtree(d)
        shutil.copytree(clamp_dir, d, symlinks=True)
        other = ""
        if case == "stale-bytes":
            solar = a.solar or "solar"
            r = subprocess.run([solar, "--emit=bin-runtime", f"{H}/StepSum.sol"], capture_output=True, text=True)
            m = re.search(r'"bin-runtime"\s*:\s*"([0-9a-f]+)"', r.stdout)
            other = m.group(1) if m else ""
        what = mutate_replay(case, d, other)
        if what is None:
            rows.append((case, "no such input found in the run's directory", "REJECTED", "NOT RUN",
                         "the driver's directory has no file this case changes", None, 0))
            continue
        v, reason, rc, wall = run(shlex.split(a.replay) + [str(d)], work / "log" / f"replay-{case}.txt")
        rows.append((case, what, "REJECTED", v, reason, v in ("REJECTED", "BLOCKED") or (v == "ERROR" and rc != 0), wall))
        print(f"{case}: got {v} ({reason})", flush=True)
    drv_after = drv_hash()
    lines = ["| case | what | expected | actual | rejecting check (driver's reason) | pass |", "|---|---|---|---|---|---|"]
    for name, what, exp, v, reason, ok, wall in rows:
        r = reason.replace("|", "\\|")
        lines.append(f"| {name} | {what} | {exp} | {v} | {r} | {'yes' if ok else ('not run' if ok is None else '**NO**')} |")
    lines.append("")
    lines.append(f"driver and tree unchanged across the cases: {drv_before == drv_after} ({drv_before})")
    table = "\n".join(lines)
    print("\n" + table)
    if a.table:
        pathlib.Path(a.table).write_text(table + "\n")
    ran = [r for r in rows if r[5] is not None]
    ok = all(r[5] for r in ran) and bool(ran) and drv_before == drv_after
    print("\nNEGATIVE-SUITE " + ("PASS" if ok else "FAIL") + f" ({sum(1 for r in ran if r[5])}/{len(ran)} ran and passed, "
          f"{len(rows) - len(ran)} not run)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
