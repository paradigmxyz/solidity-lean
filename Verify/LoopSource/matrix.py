#!/usr/bin/env python3
"""Per-loop obligation matrix from solar-verify manifests: matrix.py NAME=MANIFEST ...

For each function, one row per obligation kind (initiation, consecution, termination, exit) with
every manifest id of that kind, the solver's answer and an exit code (0 every one unsat, 1 any
other answer, 3 none emitted), so each outcome is reported apart. Prints JSON.
"""
import json
import sys

KIND = {
    "loop invariant not satisfied on entry": "initiation",
    "loop invariant not preserved by the loop body": "consecution",
    "loop does not terminate: decreases clause not decreased": "termination",
    "postcondition not satisfied": "exit",
    "contract invariant not preserved": "contract_invariant",
}
out = {}
for arg in sys.argv[1:]:
    name, path = arg.split("=", 1)
    m = json.load(open(path))
    (u,) = m["units"]
    rows = {k: [] for k in KIND.values()}
    rows["probe"] = []
    for q in u["obligations"]:
        if q["role"] == "advisory":
            rows["probe"].append({"id": q["id"], "answer": q["answer"], "smt_sha256": q["smt_sha256"]})
            continue
        rows[KIND[q["kind"]]].append({"id": q["id"], "answer": q["answer"], "line": q.get("site", {}).get("line"),
                                       "smt_sha256": q["smt_sha256"]})
    res = {}
    for k, qs in rows.items():
        if k == "probe":
            res["reachability_probe"] = {"queries": qs, "exit": 0 if qs and all(q["answer"] == "sat" for q in qs) else 1}
            continue
        res[k] = {"queries": qs, "exit": 3 if not qs else 0 if all(q["answer"] == "unsat" for q in qs) else 1}
    out[name] = {"unit": u["name"], "status": u["status"], "outcomes": res}
print(json.dumps(out, indent=1))
