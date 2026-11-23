#!/usr/bin/env python3
"""The generic negative suite, run through the generic certification driver.

negatives.py --certify CMD [--replay CMD] [--work DIR] [--table OUT.md]

CMD is the driver's command line (split by the shell), with the placeholders {src}, {out} and
{work} filled per case, as for solar's tools/certify/certify:
    --certify 'tools/certify/certify {src} natspec --solidity-lean SL --base SHA --work {work} --record-dir {out}'
    --replay 'tools/certify/certify --replay {dir} --solidity-lean SL --work {work}'
(without placeholders it runs CMD <source.sol> --out <dir>), from the directory the driver needs;
give the sources' directory with --heldout when that is not this checkout. The driver's verdict is the first word of the last line of its output
that starts with CERTIFIED, BLOCKED or REJECTED (any case), with the reason after it; no such line,
or a nonzero exit with CERTIFIED, counts as ERROR. A case passes when the verdict is the expected
one, and every case expected not to certify passes only when the driver does not print CERTIFIED.

--replay CMD runs the cold replay of a finished run's directory, as
    CMD <dir>
The replay cases certify tests/heldout/Meter.sol once, then copy its directory per case, change one
pinned input in the copy and replay it: stale bytes (the runtime bytes of another contract's fresh
compile), a flipped byte, changed solar options in the recorded pins, a stale spec (the source's
spec edited after the run), stale source (its code edited), a stale import (a generated module of
the run edited after it), an omitted selector (one dropped from the recorded entrypoints), a false
environment pin, and a lowered gas bound (out of gas passed off as a revert).
Every case runs the same driver command on the same tree: the table records the commit and the
driver's hash before and after, and the suite fails if they differ.
Each must be refused. Without --replay those cases are reported as not run.

--replay-from DIR runs only the replay cases, each from a copy of DIR (a finished run's directory,
such as a published record's replay/), in two layers: file (one run file edited, the manifest
left alone: refused before any build) and pin (one pin of record.json changed, the run files
untouched: refused only by the fresh cold run's pin comparison). --no-fresh-run stops a case
when the driver starts its fresh run, for the file layer while no heavy build may run; --slot
prefixes each replay command (a host-wide build slot). Receipts go to WORK/receipts.json.

Exits 0 iff every case that ran passed.
"""
import argparse, json, pathlib, re, shlex, shutil, subprocess, sys, time

H = "tests/heldout"  # replaced by --heldout
FRESH = [
    # name, source, expected, what it tests
    ("heldout-flag", f"{H}/Flag.sol", "CERTIFIED", "positive: inside the envelope, succeeds-if on every function"),
    ("invariant-control", f"{H}/negative/InvOkFlat.sol", "CERTIFIED", "control of entrypoint-breaks-invariant-in-envelope"),
    ("heldout-meter", f"{H}/Meter.sol", "CERTIFIED|REJECTED", "positive control: inside the generic source stage at bc6da61b"),
    ("heldout-gate", f"{H}/Gate.sol", "CERTIFIED", "positive control: empty-reason require (empty revert, not OOG)"),
    # CERTIFIED|BLOCKED: outside the generic source stage at bc6da61b (constructor parameters,
    # early returns, mappings, reason strings, internal calls, loops); BLOCKED until it covers them.
    ("heldout-clamp", f"{H}/Clamp.sol", "CERTIFIED|BLOCKED", "held-out, constructor parameters, early returns"),
    ("heldout-stepsum", f"{H}/StepSum.sol", "CERTIFIED|BLOCKED", "positive control: loop with supplied invariant"),
    ("heldout-registry", f"{H}/Registry.sol", "CERTIFIED|BLOCKED", "positive control: mapping, owner check, event"),
    ("renamed-new-constants", f"{H}/Band.sol", "CERTIFIED|BLOCKED", "Clamp renamed, constants in place of stored bounds"),
    ("empty-revert", f"{H}/EmptyRevert.sol", "CERTIFIED|BLOCKED", "empty revert next to a bounded loop (revert, not OOG)"),
    ("wrong-spec", f"{H}/negative/ClampWrongSpec.sol", "REJECTED|BLOCKED", "postcondition false of the code"),
    # Inside the envelope at bc6da61b (the driver's probe passes): these must be REJECTED.
    ("wrong-spec-in-envelope", f"{H}/negative/MeterWrongSpec.sol", "REJECTED", "Meter with one false postcondition"),
    ("false-env-in-envelope", f"{H}/negative/FalseEnvFlat.sol", "REJECTED|BLOCKED", "contradictory environment premise"),
    ("invalid-initial-invariant-in-envelope", f"{H}/negative/InitBrokenFlat.sol", "REJECTED", "invariant false initially"),
    ("entrypoint-breaks-invariant-in-envelope", f"{H}/negative/InvBrokenFlat.sol", "REJECTED", "reset() breaks the invariant"),
    ("false-env-fixed-block", f"{H}/negative/FalseEnvFixed.sol", "REJECTED|BLOCKED",
     "premise satisfiable in general, false in the statement's fixed environment"),
    ("vacuous-second-function-in-envelope", f"{H}/negative/VacuousSecondFlat.sol", "REJECTED",
     "contradictory premise on a second function storing a constant"),
    ("vacuous-second-function", f"{H}/negative/VacuousSecond.sol", "REJECTED|BLOCKED",
     "contradictory premise on a function other than the non-vacuity witness"),
    ("sibling-goal-isolation-in-envelope", f"{H}/negative/SiblingFnsFlat.sol", "REJECTED", "a sibling function's premise must not leak"),
    ("false-env", f"{H}/negative/FalseEnv.sol", "REJECTED|BLOCKED", "contradictory environment premise (vacuous)"),
    ("invalid-initial-invariant", f"{H}/negative/InitBroken.sol", "REJECTED|BLOCKED", "constructor does not establish the invariant"),
    ("entrypoint-breaks-invariant", f"{H}/negative/InvBroken.sol", "REJECTED|BLOCKED", "a second entrypoint breaks the invariant"),
    ("sibling-goal-isolation", f"{H}/negative/SiblingFns.sol", "REJECTED|BLOCKED",
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
# The driver's verdict lines (solar tools/certify/certify): CERTIFIED|FUNCTIONAL|COMPILED: exit 0
# (the requested tier holds); REJECTED: <check>: exit 1, or exit 2 when the run proved less than the
# requested tier; BLOCKED: <feature> (...) exit 3. Older TIER <T> / CHECKED / ERROR lines are read too.
VERDICT = re.compile(r"^\s*(TIER\s+\w+|CHECKED\b[^:]*|CERTIFIED|FUNCTIONAL|COMPILED|BLOCKED|REJECTED|ERROR)\b[:\s]*(.*)$")


def norm(word):
    w = word.upper()
    if w in ("CERTIFIED", "TIER CERTIFIED"):
        return "CERTIFIED"
    if w in ("FUNCTIONAL", "COMPILED") or w.startswith("TIER"):
        return "LOWER-TIER"  # a lower tier than certified was requested and met
    if w.startswith("CHECKED") or w in ("ERROR", "REJECTED"):
        return "REJECTED"
    return w


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
            verdict, reason = norm(m.group(1)), (m.group(1) + ": " + m.group(2)).strip()
            if verdict == "REJECTED" and m.group(2).startswith("resources:"):
                # A build that ran out of memory, time or heartbeats: never a refutation, so
                # never a pass for a case expected REJECTED.
                verdict = "RESOURCES"
    if verdict == "CERTIFIED" and r.returncode != 0:
        verdict, reason = "ERROR", f"CERTIFIED with exit {r.returncode}"
    if verdict == "ERROR" and r.returncode in (1, 2) and "resources:" not in out:
        verdict = "REJECTED"
    if verdict == "ERROR" and not reason:
        tail = [l for l in out.strip().splitlines() if l.strip()]
        reason = f"exit {r.returncode}: " + (tail[-1][:140] if tail else "no output")
    return verdict, reason, r.returncode, round(time.time() - t)


def fill(cmd, **kw):
    """Fill {src}, {out}, {dir}, {work} in a command template; without placeholders, append
    <src> --out <out> (fresh) or <dir> (replay)."""
    if any("{" in x for x in cmd):
        return [x.format(**{k: str(v) for k, v in kw.items()}) for x in cmd]
    return cmd + ([kw["src"], "--out", str(kw["out"])] if "src" in kw else [str(kw["dir"])])


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
                p.write_text(t.replace("@custom:ensures", "@custom:ensures true &&", 1))
                return f"{p.relative_to(d)}: one ensures clause edited"
        return None
    if case == "stale-source":
        for p in files(d, "*.sol"):
            t = p.read_text()
            if "total = total + v;" in t:
                p.write_text(t.replace("total = total + v;", "total = v + total;", 1))
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


# --replay-from DIR: the replay cases start from an existing finished run's directory (such as a
# published record's replay/), not from a fresh certified run of Meter. Each case runs in two
# layers. file: one run file of the copy is edited and the record's manifest is left alone, so
# the driver must refuse it before any build. pin: the run files stay untouched and one pin of
# record.json (which the manifest does not hash) is changed, so the manifest passes and only the
# fresh cold run's pin comparison can refuse it.
LAYERS = ("file", "pin")


def _sub1(p, old, new):
    t = p.read_text()
    if old not in t:
        return False
    p.write_text(t.replace(old, new, 1))
    return True


def mutate_from(case, layer, d, other_bin):
    """Change one input of the copy d of a finished run's directory; return what changed."""
    rec_p = d / "record.json"
    rec = json.loads(rec_p.read_text())
    srcs = [r for r in rec.get("run_files", {}) if r.endswith(".sol") and "/" not in r]
    top = d / srcs[0] if srcs else None
    inputs = sorted((d / "inputs").rglob("*")) if (d / "inputs").is_dir() else []
    pick = lambda name: next((p for p in inputs if p.name == name), None)
    if layer == "pin":
        def setk(path, val):
            o = rec
            for k in path[:-1]:
                o = o[k]
            old = o.get(path[-1])
            o[path[-1]] = val(old)
            rec_p.write_text(json.dumps(rec, indent=2) + "\n")
            return f"record.json {'.'.join(path)}: {str(old)[:40]} -> {str(o[path[-1]])[:40]}"
        import hashlib
        if case == "stale-bytes":
            return setk(("bytecode_sha256",), lambda _: hashlib.sha256(bytes.fromhex(other_bin)).hexdigest())
        if case == "flipped-byte":
            cr = json.loads((d / "certify-record.json").read_text())
            return setk(("bytecode_sha256",), lambda _: hashlib.sha256(bytes.fromhex(flip_hex(cr["bytecode"]))).hexdigest())
        if case == "changed-solar-options":
            return setk(("options",), lambda o: ["-Osize" if x == "-Ogas" else x for x in o])
        if case == "stale-spec-hash":
            return setk(("spec", "sha256"), lambda s: flip_hex(s, 0))
        if case == "stale-source":
            return setk(("source", "sha256"), lambda s: flip_hex(s, 0))
        if case == "stale-import":
            return setk(("solidity_lean", "inputs_sha256"), lambda s: flip_hex(s, 0) if isinstance(s, str) else "0" * 64)
        if case == "omitted-selector":
            return setk(("functions",), lambda f: f[1:])
        if case == "false-env-pin":
            return setk(("environment",), lambda e: e.replace("caller 0x2000", "caller 0x0"))
        if case == "oog-as-revert":
            return setk(("gas_bound",), lambda g: g // 2)
        return None
    if case in ("stale-bytes", "flipped-byte"):
        p = d / "certify-record.json"
        j = json.loads(p.read_text())
        j["bytecode"] = other_bin if case == "stale-bytes" else flip_hex(j["bytecode"])
        p.write_text(json.dumps(j, indent=2) + "\n")
        return "certify-record.json bytecode: " + ("another contract's fresh compile" if case == "stale-bytes" else "middle byte XOR 1")
    if case == "changed-solar-options":
        p = pick("options")
        return p and _sub1(p, "-Ogas", "-Osize") and f"{p.relative_to(d)}: -Ogas -> -Osize"
    if case == "stale-spec-hash":
        return top and _sub1(top, "@custom:ensures ", "@custom:ensures true && ") and f"{srcs[0]}: one ensures clause edited"
    if case == "stale-source":
        t = top.read_text() if top else ""
        m = re.search(r"(\b\w+ = )([^;]+);", t)
        if not m:
            return None
        top.write_text(t[:m.start()] + m.group(1) + "(" + m.group(2) + ");" + t[m.end():])
        return f"{srcs[0]}: '{m.group(0)}' parenthesised (same behaviour, other source bytes)"
    if case == "stale-import":
        p = pick("Source.lean")
        if not p:
            return None
        p.write_text(p.read_text() + "\n-- edited after the run\n")
        return f"{p.relative_to(d)}: comment appended"
    if case == "omitted-selector":
        p = pick("shape.json")
        j = json.loads(p.read_text())
        j["entries"] = j["entries"][1:]
        p.write_text(json.dumps(j, indent=2) + "\n")
        return f"{p.relative_to(d)}: first entry dropped"
    if case == "false-env-pin":
        p = pick("shape.json")
        j = json.loads(p.read_text())
        j["env"] = "[fun s => s.caller = 0]"
        p.write_text(json.dumps(j, indent=2) + "\n")
        return f"{p.relative_to(d)}: env [] -> a caller premise"
    if case == "oog-as-revert":
        p = pick("shape.json")
        j = json.loads(p.read_text())
        g = int(re.search(r"\d+", j["gas"]).group())
        j["gas"] = j["gas"].replace(str(g), str(g // 2))
        p.write_text(json.dumps(j, indent=2) + "\n")
        return f"{p.relative_to(d)}: gas bound {g} -> {g // 2}"
    return None


def run_watch(cmd, log, stop_at=None):
    """run(), but kill the driver's process group when a line matches stop_at (the fresh cold run
    starting), and keep a receipt: start, end, exit, peak RSS of the tree is left to the slot."""
    import os, signal, datetime
    t = time.time()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    log.parent.mkdir(parents=True, exist_ok=True)
    stopped = False
    with open(log, "w") as f:
        f.write(shlex.join(cmd) + "\n")
        f.flush()
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
        out = []
        for line in p.stdout:
            out.append(line)
            f.write(line)
            f.flush()
            if stop_at and stop_at in line:
                os.killpg(p.pid, signal.SIGTERM)
                stopped = True
                break
        rc = p.wait()
    out = "".join(out)
    end = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    if stopped:
        return "FRESH-RUN", "the manifest passed and the fresh cold run started (stopped: --no-fresh-run)", rc, round(time.time() - t), start, end
    verdict, reason = "ERROR", ""
    for line in out.splitlines():
        m = VERDICT.match(line)
        if m:
            verdict, reason = norm(m.group(1)), (m.group(1) + ": " + m.group(2)).strip()
            if verdict == "REJECTED" and m.group(2).startswith("resources:"):
                verdict = "RESOURCES"
    if verdict == "CERTIFIED" and rc != 0:
        verdict, reason = "ERROR", f"CERTIFIED with exit {rc}"
    if verdict == "ERROR" and not reason:
        tail = [l for l in out.strip().splitlines() if l.strip()]
        reason = f"exit {rc}: " + (tail[-1][:140] if tail else "no output")
    return verdict, reason, rc, round(time.time() - t), start, end


def replay_from(a, work, other):
    """The nine replay cases against a.replay_from, by layer; returns table rows."""
    import hashlib
    src = pathlib.Path(a.replay_from).resolve()
    rows, receipts = [], []
    layers = LAYERS if a.layer == "both" else (a.layer,)
    want = set(a.only.split(",")) if a.only else None
    for layer in layers:
        for case in REPLAY:
            name = f"{case}@{layer}"
            if want and case not in want and name not in want:
                continue
            d = work / ("from-" + case + "-" + layer) / src.name
            if d.parent.exists():
                shutil.rmtree(d.parent)
            shutil.copytree(src, d, symlinks=True)
            what = mutate_from(case, layer, d, other)
            if not what:
                rows.append((name, "no such input in the directory", "REJECTED", "NOT RUN", "nothing to change", None, 0))
                continue
            cmd = fill(shlex.split(a.replay), dir=d, work=work / "w" / name)
            if a.slot:
                cmd = shlex.split(a.slot) + cmd
            v, reason, rc, wall, t0, t1 = run_watch(cmd, work / "log" / f"{name}.txt",
                                                    "== replay:" if a.no_fresh_run else None)
            # FRESH-RUN: the manifest passed and the case awaits its fresh cold run (not run yet).
            ok = None if v == "FRESH-RUN" else (v in ("REJECTED", "BLOCKED") and rc != 0)
            rows.append((name, what, "REJECTED", v, f"{reason} (exit {rc})", ok, wall))
            receipts.append({"case": name, "changed": what, "command": cmd, "exit": rc, "verdict": v, "line": reason,
                             "start": t0, "end": t1, "wall_s": wall,
                             "log_sha256": hashlib.sha256((work / "log" / f"{name}.txt").read_bytes()).hexdigest()})
            print(f"{name}: got {v} ({reason}) exit {rc} in {wall} s", flush=True)
    (work / "receipts.json").write_text(json.dumps(receipts, indent=2) + "\n")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--certify", default=None)
    ap.add_argument("--replay", default=None)
    ap.add_argument("--work", default=".lake/negatives")
    ap.add_argument("--table", default=None)
    ap.add_argument("--only", default=None)
    ap.add_argument("--heldout", default=None, help="tests/heldout of this checkout (absolute) when the driver runs elsewhere")
    ap.add_argument("--solar", default=None, help="solar for the stale-bytes compile (default: the driver's)")
    ap.add_argument("--replay-from", default=None, metavar="DIR",
                    help="run only the replay cases, each from a copy of this finished run's directory")
    ap.add_argument("--layer", choices=["file", "pin", "both"], default="both")
    ap.add_argument("--no-fresh-run", action="store_true",
                    help="stop a case when the driver starts its fresh cold run (light cases only)")
    ap.add_argument("--slot", default=None, help="prefix every replay command with this (a host-wide build slot)")
    ap.add_argument("--other-bin", default=None, help="hex runtime bytes of another contract, for stale-bytes")
    a = ap.parse_args()
    if not (a.certify or a.replay_from):
        ap.error("--certify or --replay-from is required")
    if a.replay_from and not a.replay:
        ap.error("--replay-from needs --replay")
    global H
    if a.heldout:
        H = str(pathlib.Path(a.heldout).resolve())
    work = pathlib.Path(a.work).resolve()
    certify = shlex.split(a.certify or a.replay)
    drv = pathlib.Path(certify[0])
    drv_hash = lambda: subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip() + ":" + \
        (__import__("hashlib").sha256(drv.read_bytes()).hexdigest() if drv.is_file() else "")
    drv_before = drv_hash()
    rows = []
    want = set(a.only.split(",")) if a.only else None
    clamp_dir = None
    if a.replay_from:
        other = a.other_bin or ""
        if not other:
            r = subprocess.run([a.solar or "solar", "--emit=bin-runtime", f"{H}/StepSum.sol"], capture_output=True, text=True)
            m = re.search(r'"bin-runtime"\s*:\s*"([0-9a-f]+)"', r.stdout)
            other = m.group(1) if m else ""
        work.mkdir(parents=True, exist_ok=True)
        rows = replay_from(a, work, other)
    for name, src, exp, what in ([] if a.replay_from else FRESH):
        if want and name not in want and not (name == "heldout-meter" and a.replay):
            continue
        out = work / name
        if out.exists():
            shutil.rmtree(out)
        v, reason, rc, wall = run(fill(certify, src=src, out=out, work=work / "w" / name), work / "log" / f"{name}.txt")
        # CERTIFIED|BLOCKED: a loop, BLOCKED until the driver consumes supplied invariants, never
        # anything else.
        ok = v in exp.split("|")
        rows.append((name, what, exp, v, reason, ok, wall))
        if name in ("sibling-isolation-control", "heldout-meter", "heldout-clamp") and v == "CERTIFIED" and clamp_dir is None:
            clamp_dir = out
        print(f"{name}: expected {exp}, got {v} ({reason}) in {wall} s", flush=True)
    for case in ([] if a.replay_from else REPLAY):
        if want and case not in want:
            continue
        if not a.replay or clamp_dir is None:
            rows.append((case, "replay of the certified Meter run with one input changed", "REJECTED", "NOT RUN",
                         "no replay command" if not a.replay else "Meter did not certify", None, 0))
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
        v, reason, rc, wall = run(fill(shlex.split(a.replay), dir=d, work=work / "w" / ("replay-" + case)),
                                  work / "log" / f"replay-{case}.txt")
        rows.append((case, what, "REJECTED", v, reason, v in ("REJECTED", "BLOCKED") or (v == "ERROR" and rc != 0 and "resources:" not in reason), wall))
        print(f"{case}: got {v} ({reason})", flush=True)
    drv_after = drv_hash()
    lines = ["| case | what | expected | actual | rejecting check (driver's reason) | pass |", "|---|---|---|---|---|---|"]
    for name, what, exp, v, reason, ok, wall in rows:
        r = reason.replace("|", "\\|")
        lines.append(f"| {name} | {what} | {exp.replace('|', ' or ')} | {v} | {r} | {'yes' if ok else ('not run' if ok is None else '**NO**')} |")
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
