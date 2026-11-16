#!/usr/bin/env python3
"""Loop acceptance gate over solar-verify's emitted obligations.

Usage: loopgate.py SOLAR_VERIFY Z3 SOURCE.sol CONTRACT.FN OUTDIR [--assume SMT]... [--show NAME]...

Runs `SOLAR_VERIFY --no-infer --only CONTRACT.FN --emit-lean OUTDIR/emit SOURCE.sol` (z3 as
SOLAR_VERIFY_Z3), then reads the manifest and decides each outcome apart:

  initiation, consecution, termination, exit  every obligation of that kind unsat (none emitted
                                              is reported, and fails for the first three: a loop
                                              without invariant or measure is not accepted)
  nonvacuity  REQUIRED: the advisory probe (some path returns under the precondition) is sat AND
              witness.py finds a model of it with every --assume (such as one that runs the loop)

Writes OUTDIR/gate.json and exits 0 ACCEPT, 1 an obligation failed, 2 solar-verify error or no
manifest, 3 an obligation kind missing, 4 VACUOUS (probe unsat or no witness). solar-verify itself
exits 0 on a vacuous function (it only warns), so the gate does not read its exit as acceptance.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KIND = {
    "loop invariant not satisfied on entry": "initiation",
    "loop invariant not preserved by the loop body": "consecution",
    "loop does not terminate: decreases clause not decreased": "termination",
    "postcondition not satisfied": "exit",
    "contract invariant not preserved": "contract_invariant",
}
REQUIRED = ("initiation", "consecution", "termination")

args = sys.argv[1:]
assume, show = [], []
for flag, acc in (("--assume", assume), ("--show", show)):
    while flag in args:
        i = args.index(flag)
        acc.append(args[i + 1])
        del args[i : i + 2]
verify, z3, src, only, outdir = args
outdir = os.path.abspath(outdir)
os.makedirs(outdir, exist_ok=True)
emit = os.path.join(outdir, "emit")
env = dict(os.environ, SOLAR_VERIFY_Z3=z3)
# --emit-lean takes sources under the run's directory: run beside the source.
p = subprocess.run([verify, "--no-infer", "--only", only, "--emit-lean", emit, os.path.basename(src)],
                   env=env, capture_output=True, text=True, cwd=os.path.dirname(os.path.abspath(src)))
open(os.path.join(outdir, "solar-verify.out"), "w").write(p.stdout + p.stderr)
gate = {"source": src, "function": only, "solar_verify_exit": p.returncode, "outcomes": {}}
man = os.path.join(emit, "manifest.json")


def finish(code, verdict):
    gate["exit"], gate["verdict"] = code, verdict
    json.dump(gate, open(os.path.join(outdir, "gate.json"), "w"), indent=1)
    print(f"{only}: {verdict} (exit {code})")
    for k, o in gate["outcomes"].items():
        print(f"  {k}: exit {o['exit']}")
    sys.exit(code)


if not os.path.exists(man):
    finish(2, "ERROR: solar-verify wrote no manifest")
(u,) = json.load(open(man))["units"]
rows = {k: [] for k in KIND.values()}
probes = []
for q in u["obligations"]:
    if q["role"] == "advisory":
        probes.append(q)
    else:
        rows[KIND[q["kind"]]].append(q)
for k, qs in rows.items():
    gate["outcomes"][k] = {
        "ids": [(q["id"], q["answer"]) for q in qs],
        "exit": 3 if not qs else 0 if all(q["answer"] == "unsat" for q in qs) else 1,
    }
nv = {"probes": [(q["id"], q["answer"]) for q in probes]}
if len(probes) != 1 or probes[0]["answer"] != "sat":
    nv["exit"] = 4
else:
    cmd = [sys.executable, os.path.join(HERE, "witness.py"), man, probes[0]["id"], z3]
    for a in assume:
        cmd += ["--assume", a]
    w = subprocess.run(cmd + show, capture_output=True, text=True)
    nv["witness"] = (w.stdout + w.stderr).strip()
    nv["assume"] = assume
    nv["exit"] = 0 if w.returncode == 0 else 4
gate["outcomes"]["nonvacuity"] = nv
ex = {k: o["exit"] for k, o in gate["outcomes"].items()}
if any(e == 1 for e in ex.values()):
    finish(1, "REJECT: obligation failed")
if any(ex[k] == 3 for k in REQUIRED):
    finish(3, "REJECT: loop obligation kind missing")
if ex["nonvacuity"] != 0:
    finish(4, "REJECT: vacuous (no satisfiable precondition witness)")
if p.returncode != 0:
    finish(2, "ERROR: solar-verify exit nonzero with every obligation discharged")
finish(0, "ACCEPT")
