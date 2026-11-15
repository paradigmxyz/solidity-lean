#!/usr/bin/env python3
"""Lane G: the tables of docs/eval/g.md from the run outputs (~/g-gen)."""
import csv, glob, os, re, statistics, sys
H = os.path.expanduser("~/g-gen")

def gcompare():
    rows = ["", "| contract (check.sh run) | candidates | proved (all three agree) | base: sym_mem_disch each | shared grind state | ground first, then shared | kernel of found proofs (base / shared / ground) |", "|---|---|---|---|---|---|---|"]
    for c in ["AbiHash", "Masks", "Events"]:
        f = f"{H}/check-Real_{c}.out"
        if not os.path.exists(f) or os.path.getsize(f) == 0:
            rows.append(f"| {c} | not run | | | | | |"); continue
        s = open(f).read()
        m = re.findall(r"g_compare: (\d+) candidates; base proved (\d+) in ([0-9.]+) ms \(kernel ([0-9.]+) ms\); shared proved (\d+) in ([0-9.]+) ms \(kernel ([0-9.]+) ms\); ground\+shared proved (\d+) in ([0-9.]+) ms \(kernel ([0-9.]+) ms\)", s)
        dis = len(re.findall(r"warning: g_compare: base", s))
        err = len(re.findall(r"error", s))
        n = sum(int(x[0]) for x in m); pb = sum(int(x[1]) for x in m); ps = sum(int(x[4]) for x in m); pg = sum(int(x[7]) for x in m)
        tb = sum(float(x[2]) for x in m); ts = sum(float(x[5]) for x in m); tg = sum(float(x[8]) for x in m)
        kb = sum(float(x[3]) for x in m); ks = sum(float(x[6]) for x in m); kg = sum(float(x[9]) for x in m)
        wall = re.search(r"\[check\] exit=(\d+) wall=(\S+)", s)
        rows.append(f"| {c} (exit {wall.group(1) if wall else '?'}, {len(m)} contexts, {dis} disagreements, {err} errors) | {n} | {pb} / {ps} / {pg} | {tb:.0f} ms | {ts:.0f} ms | {tg:.0f} ms | {kb:.1f} / {ks:.1f} / {kg:.1f} ms |")
    return "\n".join(rows)

def vcgrind():
    out = []
    for C, dirs in [("Vault", ["discharge/Vault"]), ("ArrayMax", ["discharge/ArrayMax", "discharge/ArrayMax-b"])]:
        rows = []
        for d in dirs:
            f = f"{H}/{d}/results.tsv"
            if os.path.exists(f): rows += list(csv.DictReader(open(f), delimiter="\t"))
        ids = sorted(set(r["id"] for r in rows))
        out.append(f"\n{C}: {len(ids)} required rows measured.\n")
        out.append("| backend | proved | median elab+kernel (ms) | median kernel (ms) | median proof DAG | max RSS (MB) | axioms of proved rows |")
        out.append("|---|---|---|---|---|---|---|")
        for b in ["vc_valid", "vc_grind", "vc_grind_nl", "cert", "vacuity(vc_grind)"]:
            br = [r for r in rows if r["backend"] == b]
            if not br: continue
            pr = [r for r in br if r["status"] in ("proved", "yes")]
            med = lambda k: (statistics.median(float(r[k]) for r in pr) if pr and all(r[k] not in ("-", "") for r in pr) else float("nan"))
            ax = sorted(set(r["axioms"] for r in pr))
            rss = max((int(r["peak_kb"]) for r in pr if r["peak_kb"].isdigit()), default=0) // 1024
            label = "yes (vacuous)" if b.startswith("vacuity") else "proved"
            out.append(f"| {b} | {len(pr)}/{len(br)} {label} | {med('elab_with_kernel_ms'):.0f} | {med('kernel_all_ms'):.0f} | {med('proof_dag'):.0f} | {rss} | {'; '.join(ax)} |")
        fails = [r for r in rows if r["backend"] in ("vc_valid", "vc_grind") and r["status"] not in ("proved",)]
        for r in fails:
            out.append(f"- {r['id']} {r['backend']}: {r['status'][:150]}")
        vac = [r["id"] for r in rows if r["backend"].startswith("vacuity") and r["status"] == "yes"]
        out.append(f"- vacuous by grind: {', '.join(vac) or 'none'}")
    for C in ["Vault", "ArrayMax"]:
        f = f"{H}/discharge-neg/{C}/results.tsv"
        if os.path.exists(f):
            rs = list(csv.DictReader(open(f), delimiter="\t"))
            out.append(f"- negative ({C}, goal negated as test/smt-negatives.sh N4): " + "; ".join(f"{r['backend']} {r['status'][:70]}" for r in rs))
    return "\n".join(out)

def cbv():
    rows = ["", "| statement | variant | elab+kernel (ms) | kernel (ms) | proof DAG (+aux) | axioms |", "|---|---|---|---|---|---|"]
    for f in [f"{H}/check-Cbv_Sat.out", f"{H}/check-Cbv_Mulx.out"]:
        if not os.path.exists(f) or os.path.getsize(f) == 0:
            rows.append(f"| {os.path.basename(f)} | not run | | | | |"); continue
        s = open(f).read()
        for m in re.finditer(r"g_time (\S+) (\S+): ([0-9.]+) ms\nkernel_recheck_all \S+: ok in ([0-9.]+) ms over \d+ declarations\nproof_stats \S+: tree=\d+ dag=(\d+) aux_decls=\d+ aux_dag=(\d+) type_dag=\d+\n'\S+' depends on axioms: \[(.*?)\]", s):
            rows.append(f"| {m.group(1)} | {m.group(2)} | {float(m.group(3)):.1f} | {float(m.group(4)):.2f} | {m.group(5)} (+{m.group(6)}) | {m.group(7)} |")
        e = re.search(r"\[check\] exit=(\d+) wall=(\S+) peak_rss_kb=(\d+)", s)
        if e: rows.append(f"| ({os.path.basename(f)}) | check.sh | exit {e.group(1)}, wall {e.group(2)}, peak {int(e.group(3))//1024} MB | | | |")
    return "\n".join(rows)

if __name__ == "__main__":
    doc = open(sys.argv[1]).read()
    doc = doc.replace("GCOMPARE_TABLE", gcompare()).replace("VCGRIND_TABLE", vcgrind()).replace("CBV_TABLE", cbv())
    open(sys.argv[2], "w").write(doc)
