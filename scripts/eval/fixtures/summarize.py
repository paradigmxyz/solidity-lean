#!/usr/bin/env python3
"""Summarize evaluation receipts into schema rows (Verify/Eval/A/schema.json) and a markdown table
with doubling ratios metric(2n)/metric(n).

    scripts/eval/fixtures/summarize.py [--receipts ~/eval-receipts.jsonl] [--rows lane_rows.jsonl ...]
                                       [--lane A] [--jsonl out.jsonl] [--md out.md]

Inputs:
* check.sh receipts (one line per run: lane, file, exit, wall, peak_rss_kb, profile, log). For each
  one, the log is read for the cumulative profile, "proof_stats <thm>: ..." and
  "kernel_recheck <thm>: ok in <ms> ms" lines (Verify.Eval.Common.Measure), giving one row per
  measured theorem. ~/eval-logs/replay-<lane>-<fixture>.jsonl (Verify/Eval/A/Replay.lean) adds the
  kernel-only replay time, axioms and statement hash. Rows with a "status" field (timeouts written
  by run_baseline.sh) are kept as such.
* --rows: lane-provided rows already in the schema's shape, used as they are.
The latest receipt per (lane, fixture, statement) wins. A theorem named *.baseline is variant
"baseline"; any other theorem is "new" unless the row says otherwise.
"""
import argparse
import json
import os
import pathlib
import re
import socket
import subprocess

REPO = pathlib.Path(__file__).resolve().parents[3]
HOME = pathlib.Path.home()

NON_ELAB = ("import", "initialization", "interpretation", "type checking", "blocked (unaccounted)",
            ".olean serialization", "linting", "module linting", "declTypeLinter", "tacticAnalysis")
TACTIC = ("simp", "dsimp", "tactic execution", "omega", "grind", "decide", "bv_decide", "norm_num",
          "aesop", "ring", "linarith")


def to_ms(v):
    m = re.match(r"([0-9.]+)(ms|s)$", v.strip())
    if not m:
        return None
    x = float(m.group(1))
    return x if m.group(2) == "ms" else x * 1000.0


def parse_profile(text):
    prof = {}
    if "cumulative profiling times:" not in text:
        return prof
    for line in text.split("cumulative profiling times:")[-1].splitlines():
        m = re.match(r"^\s+(.+?) ([0-9.]+(?:ms|s))$", line)
        if m:
            prof[m.group(1)] = to_ms(m.group(2))
    return prof


def wall_to_s(w):
    if w is None:
        return None
    if isinstance(w, (int, float)):
        return float(w)
    parts = [float(p) for p in str(w).split(":")]
    s = 0.0
    for p in parts:
        s = s * 60 + p
    return s


def env_info():
    tc = (REPO / "lean-toolchain").read_text().strip() if (REPO / "lean-toolchain").exists() else "?"
    try:
        commit = subprocess.check_output(["git", "-C", str(REPO), "rev-parse", "--short=12", "HEAD"], text=True).strip()
        dirty = subprocess.call(["git", "-C", str(REPO), "diff", "--quiet", "HEAD"]) != 0
        commit += "+dirty" if dirty else ""
    except Exception:
        commit = "?"
    try:
        mem = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") // 2**30
    except Exception:
        mem = "?"
    machine = f"{socket.gethostname()}/{os.cpu_count()}cpu/{mem}GiB LEAN_NUM_THREADS=1 -M{os.environ.get('EVAL_MEM', '5000')}"
    return tc, machine, commit


def split_fixture(stem):
    m = re.match(r"^([A-Za-z]+?)(\d+)$", stem)
    return (m.group(1), int(m.group(2))) if m else (None, None)


def load_replay(lane, fixture):
    p = HOME / "eval-logs" / f"replay-{lane}-{fixture}.jsonl"
    out = {}
    if not p.exists():
        return out
    for line in p.read_text().splitlines():
        try:
            d = json.loads(line)
        except Exception:
            continue
        if "replay" in d:
            out[d["replay"]] = d
    return out


def olean_size(file):
    mod = pathlib.Path(file).with_suffix(".olean")
    p = REPO / ".lake" / "build" / "lib" / "lean" / mod
    return p.stat().st_size if p.exists() else None


def rows_from_receipt(r, tc, machine, commit):
    lane = r.get("lane", "?")
    file = r.get("file", "")
    fixture = pathlib.Path(file).stem
    family, n = split_fixture(fixture)
    base = dict(lane=lane, fixture=fixture, family=family, n=n, toolchain=tc, machine=machine,
                commit=commit, log=r.get("log") or "", peak_rss_kb=r.get("peak_rss_kb"),
                wall_s=r.get("wall_s", wall_to_s(r.get("wall"))))
    if "status" in r:  # run_baseline.sh's timeout / oom / error rows
        st = r["status"]
        if st == "error" and r.get("log") and os.path.exists(r["log"]):
            t = open(r["log"], errors="replace").read()
            if re.search(r"excessive memory|out of memory", t):
                st = "oom"
            elif "maximum number of steps exceeded" in t:
                st = "error:simp-maxSteps"
        r = dict(r, status=st)
        base.update(variant="baseline", statement=f"{fixture}.baseline", status=r["status"],
                    limit_s=r.get("limit_s"))
        return [base]
    text = ""
    if base["log"] and os.path.exists(base["log"]):
        text = open(base["log"], errors="replace").read()
    prof = parse_profile(text)
    elab = sum(v for k, v in prof.items() if k not in NON_ELAB and not k.startswith("compilation")) if prof else None
    tac = sum(v for k, v in prof.items() if k in TACTIC) if prof else None
    status = "ok" if r.get("exit") == 0 and ": error:" not in text else "error"
    if re.search(r"out of memory|memory (limit|threshold)|maximum memory|excessive memory", text, re.I):
        status = "oom"
    stats = {m.group(1): m for m in re.finditer(
        r"proof_stats (\S+): tree=(\d+) dag=(\d+) aux_decls=(\d+) aux_dag=(\d+)", text)}
    rech = {m.group(1): float(m.group(2)) for m in re.finditer(r"kernel_recheck (\S+): ok in ([0-9.]+) ms", text)}
    replay = load_replay(lane, fixture)
    names = list(stats) or list(rech) or [None]
    out = []
    for name in names:
        row = dict(base)
        row.update(status=status, elab_ms=elab, tactic_ms=tac, interp_ms=prof.get("interpretation"),
                   kernel_ms=prof.get("type checking"), olean_bytes=olean_size(file))
        row["statement"] = name or f"{fixture}.?"
        if name is None:  # nothing measured (the file failed early): a fixture's own file is its baseline
            row["variant"] = "baseline" if ("/Eval/A/Fixtures/" in file or lane == "A") else "new"
        else:
            row["variant"] = "baseline" if name.endswith(".baseline") else "new"
        if name in stats:
            m = stats[name]
            row.update(tree_nodes=int(m.group(2)), dag_nodes=int(m.group(3)) + int(m.group(5)),
                       aux_decls=int(m.group(4)))
        row["kernel_recheck_ms"] = rech.get(name)
        if name and replay:
            mine = [d for k, d in replay.items() if k == name or k.startswith(name + ".") or
                    k.startswith(name + "._") or ("_proof_" in k and k.startswith(name))]
            if mine:
                row["kernel_replay_ms"] = round(sum(d["kernel_replay_ms"] for d in mine), 3)
                row["axioms_ok"] = all(d["axioms_ok"] for d in mine)
                row["axioms"] = sorted({a for d in mine for a in d["axioms"]})
            if name in replay:
                row["statement_hash"] = replay[name]["statement_hash"]
        row.setdefault("heartbeats", None)
        out.append(row)
    return out


def fmt(v, kind="num"):
    if v is None:
        return "–"
    if kind == "int":
        return f"{int(v):,}"
    if kind == "ratio":
        return f"×{v:.2f}"
    if isinstance(v, float):
        return f"{v:,.0f}" if v >= 100 else f"{v:.1f}"
    return str(v)


RATIO_METRICS = [("wall_s", "wall"), ("tactic_ms", "tactic"), ("kernel_ms", "kernel"),
                 ("kernel_replay_ms", "replay"), ("dag_nodes", "dag")]


def ratio(rows, row, key):
    if row.get("n") is None or row.get(key) in (None, 0):
        return None
    prev = rows.get((row["lane"], row["family"], row["variant"], row["n"] // 2))
    if not prev or prev.get("status") != "ok" or not prev.get(key):
        return None
    return row[key] / prev[key]


def markdown(rows):
    idx = {(r["lane"], r.get("family"), r["variant"], r.get("n")): r for r in rows if r.get("n")}
    head = ["fixture", "variant", "status", "wall s", "elab ms", "tactic ms", "kernel ms", "recheck ms",
            "replay ms", "dag", "tree", "olean B", "RSS MB", "axioms ok"] + [f"{lbl} 2n/n" for _, lbl in RATIO_METRICS]
    lines = ["| " + " | ".join(head) + " |", "|" + "---|" * len(head)]
    order = sorted(rows, key=lambda r: (r["lane"], r.get("family") or "", r["variant"], r.get("n") or 0))
    for r in order:
        status = r["status"] + (f" (>{int(r['limit_s'])} s)" if r["status"] == "timeout" and r.get("limit_s") else "")
        cells = [r["fixture"], r["variant"], status, fmt(r.get("wall_s")), fmt(r.get("elab_ms")),
                 fmt(r.get("tactic_ms")), fmt(r.get("kernel_ms")), fmt(r.get("kernel_recheck_ms")),
                 fmt(r.get("kernel_replay_ms")), fmt(r.get("dag_nodes"), "int"), fmt(r.get("tree_nodes"), "int"),
                 fmt(r.get("olean_bytes"), "int"),
                 fmt(r["peak_rss_kb"] / 1024 if r.get("peak_rss_kb") else None), fmt(r.get("axioms_ok"))]
        cells += [fmt(ratio(idx, r, k), "ratio") if r["status"] == "ok" else "–" for k, _ in RATIO_METRICS]
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipts", default=str(HOME / "eval-receipts.jsonl"))
    ap.add_argument("--rows", nargs="*", default=[])
    ap.add_argument("--lane", default=None, help="only this lane's receipts")
    ap.add_argument("--fixtures-only", action="store_true", help="only <Family><n> fixtures")
    ap.add_argument("--files", nargs="*", default=None, help="only these file stems (e.g. Bump BumpTotal)")
    ap.add_argument("--jsonl", default=None)
    ap.add_argument("--md", default=None)
    a = ap.parse_args()
    tc, machine, commit = env_info()
    latest = {}
    if os.path.exists(a.receipts):
        for line in open(a.receipts):
            try:
                r = json.loads(line)
            except Exception:
                continue
            if a.lane and r.get("lane") != a.lane:
                continue
            if r.get("exit") == 127:  # check.sh not found: not a measurement
                continue
            for row in rows_from_receipt(r, tc, machine, commit):
                latest[(row["lane"], row["fixture"], row["variant"])] = row
    for path in a.rows:
        for line in open(path):
            line = line.strip()
            if line:
                row = json.loads(line)
                if a.lane and row.get("lane") != a.lane:
                    continue
                latest[(row["lane"], row["fixture"], row.get("variant", "new"))] = row
    rows = list(latest.values())
    if a.fixtures_only:
        rows = [r for r in rows if r.get("n") and r["n"] >= 16]
    if a.files:
        rows = [r for r in rows if r["fixture"] in a.files]
    if a.jsonl:
        with open(a.jsonl, "w") as f:
            for r in sorted(rows, key=lambda r: (r["lane"], r.get("family") or "", r.get("n") or 0, r["variant"])):
                f.write(json.dumps(r, sort_keys=True) + "\n")
    md = markdown(rows)
    if a.md:
        pathlib.Path(a.md).write_text(md + "\n")
    print(md)


if __name__ == "__main__":
    main()
