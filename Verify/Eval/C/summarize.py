#!/usr/bin/env python3
"""Summarize lane C fixture runs (~/eval-c-runs.tsv and the check.sh logs) as a markdown table
and JSON: wall, peak RSS, tactic/elaboration and kernel (type checking) profiler times,
#kernel_recheck ms, proof DAG/tree, olean bytes, stepper counters, doubling ratios."""
import json, re, sys, pathlib, os

rows = []
tsv = pathlib.Path(os.path.expanduser("~/eval-c-runs.tsv"))
for line in tsv.read_text().splitlines():
    k, n, v, var, sz, rest = line.split("\t", 5)
    m = re.search(r"exit=(\d+) wall=(\S+) peak_rss_kb=(\d+) log=(\S+)", rest)
    if not m: continue
    code, wall, rss, log = m.groups()
    text = pathlib.Path(log).read_text(errors="replace") if pathlib.Path(log).exists() else ""
    def prof(name):
        mm = re.search(r"^\s+" + re.escape(name) + r" ([0-9.]+)(ms|s)$", text, re.M)
        if not mm: return 0.0
        x = float(mm.group(1)); return x * 1000 if mm.group(2) == "s" else x
    ps = re.findall(r"proof_stats \S+: tree=(\d+) dag=(\d+) aux_decls=(\d+) aux_dag=(\d+)", text)
    kr = re.findall(r"kernel_recheck \S+: ok in ([0-9.]+) ms", text)
    st = re.search(r"evm_sym stats: (.*)", text)
    mm, ss = wall.split(":")[-2:]
    rows.append(dict(kind=k, n=int(n), variant=v, mode=var, exit=int(code),
        wall_s=round(int(mm) * 60 + float(ss), 2), rss_mb=int(rss) // 1024,
        tactic_ms=prof("tactic execution"), elab_ms=prof("elaboration"),
        kernel_ms=prof("type checking"), recheck_ms=float(kr[0]) if kr else None,
        tree=int(ps[0][0]) if ps else None, dag=int(ps[0][1]) if ps else None,
        aux_dag=int(ps[0][3]) if ps else None, olean=int(sz),
        stats=st.group(1) if st else "", log=log))
last = {}
for r in rows: last[(r["kind"], r["n"], r["variant"], r["mode"])] = r
rows = sorted(last.values(), key=lambda r: (r["kind"], r["variant"], r["mode"], r["n"]))
prev = {}
print("| fixture | variant | exit | wall s | tactic ms | kernel ms | recheck ms | dag | olean | x2 wall | stepper |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for r in rows:
    key = (r["kind"], r["variant"], r["mode"])
    ratio = ""
    if key in prev and prev[key]["wall_s"] > 0 and r["exit"] == 0 and prev[key]["exit"] == 0:
        ratio = f'{r["wall_s"] / prev[key]["wall_s"]:.2f}'
    prev[key] = r
    print(f'| {r["kind"]}{r["n"]} | {r["variant"]}/{r["mode"]} | {r["exit"]} | {r["wall_s"]} | {r["tactic_ms"]:.0f} | {r["kernel_ms"]:.0f} | {r["recheck_ms"]} | {r["dag"]} | {r["olean"]} | {ratio} | {r["stats"][:200]} |')
pathlib.Path(os.path.expanduser("~/eval-c-summary.json")).write_text(json.dumps(rows, indent=1))
