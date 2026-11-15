#!/usr/bin/env python3
"""Loop certificates from solar-verify's loop-cut export (--emit-loopvc, format 1).

    loopcert.py annotate SOURCE INVARIANTS OUT
        Writes OUT: SOURCE with the supplied invariants and ranking functions of INVARIANTS (the
        driver's --invariants file, below) inserted as @custom:invariant / @custom:decreases lines
        right above each named loop. Nothing else changes: deleting the inserted lines gives SOURCE
        byte for byte, which is checked, so the compiled code is the same and only the candidate
        solar-verify cuts at is new.
    loopcert.py plan EXPORT [--only C.f]...
        Reads EXPORT/manifest.json and, per unit, its loop cut, and prints the plan as JSON: each
        unit with a loop is "required" (with its templates by edge) or "blocked" (with the reason);
        units without a loop are "no-loop". Exit 0 when no unit is blocked, 3 otherwise.
    loopcert.py gen EXPORT PLAN OUTDIR
        Writes OUTDIR/LoopCert/<C>/<f>.lean per required unit: a proof of every instance obligation
        (by vc_smt, lean-smt's reconstruction of cvc5's proof), each template's validity at the
        run's candidate through the exporter's exactness theorems, and the theorem certified: the
        conjunction of every template on every edge (entry invariant, back invariant, back rank,
        exit path obligations).
    loopcert.py receipt PLAN AXIOMS_DIR [DISCHARGE_SUMMARY] > receipt.json
        Statuses per unit with a loop: "proved" only when its certificate built and certified's
        axioms are within propext, Classical.choice and Quot.sound and (with the summary of
        Verify/Discharge/discharge.sh on EXPORT) every instance is proved there and none holds
        vacuously; "blocked" with the plan's reason; otherwise "failed" (inconclusive). Exit 0 all
        proved, 3 some blocked and none failed, 1 any failed.

A unit is required rather than blocked (format 1 of the interface) when it has one loop; an
invariant (annotated or supplied); a ranking function (else termination has no proof); no call in
the loop; an entry edge with an invariant template, a back edge with an invariant and a rank
template, an exit edge to a normal return, an empty call edge and revert paths without templates;
every required obligation of the unit an instance of exactly one template; and the interface
library and Horn view the hashes name.

INVARIANTS (format certify-invariants, version 1):

    {"format": "certify-invariants", "version": 1,
     "loops": [{"function": "C.f", "line": L, "invariants": ["i <= n", ...], "decreases": "n - i"}]}

L is the line of the loop statement in SOURCE; expressions are solar-verify's spec language over the
loop's variables, the function's parameters, state variables and old(...).
"""
import hashlib
import json
import os
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def fail(msg, code=1):
    print(f"loopcert: error: {msg}", file=sys.stderr)
    sys.exit(code)


def load(path, what):
    try:
        with open(path, "rb") as f:
            return json.loads(f.read().decode("utf-8"))
    except (OSError, ValueError, UnicodeDecodeError) as e:
        fail(f"cannot read {what} {path}: {e}")


def sha(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def annotate(source, invariants, out):
    spec = load(invariants, "the invariants file")
    if spec.get("format") != "certify-invariants" or spec.get("version") != 1:
        fail(f"{invariants} is not certify-invariants version 1")
    lines = open(source, encoding="utf-8").read().split("\n")
    inserts = {}
    for lp in spec.get("loops") or []:
        line = lp.get("line")
        if not isinstance(line, int) or not 1 <= line <= len(lines):
            fail(f"{invariants}: loop of {lp.get('function')} has no line {line} in {source}")
        text = lines[line - 1]
        if not re.match(r"\s*(for|while|do)\b", text):
            fail(f"{invariants}: line {line} of {source} is not a loop statement: {text.strip()!r}")
        indent = re.match(r"\s*", text).group(0)
        add = []
        for inv in lp.get("invariants") or []:
            if not isinstance(inv, str) or not inv.strip() or "\n" in inv:
                fail(f"{invariants}: invariant {inv!r} is not one line of spec text")
            add.append(f"{indent}/// @custom:invariant {inv.strip()}")
        dec = lp.get("decreases")
        if dec is not None:
            if not isinstance(dec, str) or not dec.strip() or "\n" in dec:
                fail(f"{invariants}: decreases {dec!r} is not one line of spec text")
            add.append(f"{indent}/// @custom:decreases {dec.strip()}")
        if not add:
            fail(f"{invariants}: the loop at line {line} supplies nothing")
        if line in inserts:
            fail(f"{invariants}: line {line} named twice")
        inserts[line] = add
    outl, mark = [], []
    for i, l in enumerate(lines, 1):
        for a in inserts.get(i, []):
            outl.append(a)
            mark.append(True)
        outl.append(l)
        mark.append(False)
    if "\n".join(l for l, m in zip(outl, mark) if not m) != "\n".join(lines):
        fail("the annotated source does not reduce to the original by deleting the inserted lines")
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(outl))
    print(json.dumps({"source_sha256": sha(source), "annotated_sha256": sha(out),
                      "inserted": {str(k): v for k, v in inserts.items()}}))


def plan(export, only):
    manifest = load(os.path.join(export, "manifest.json"), "the export's manifest")
    if manifest.get("format") != "solar-verify-lean" or manifest.get("version") != 2:
        fail("not a solar-verify-lean version 2 export")
    lib = os.path.join(export, "LoopVc.lean")
    out = {"export": export, "manifest_sha256": sha(os.path.join(export, "manifest.json")), "units": []}
    # A unit's own loop-cut error is also on its loopvc entry; any other error of the run (a source
    # outside the run's directory, say) leaves the export incomplete and blocks every unit.
    names = [u.get("name") for u in manifest.get("units", [])]
    errors = [e for e in manifest.get("errors") or []
              if not any(e.startswith(f"{n}: --emit-loopvc:") for n in names)]
    for u in manifest.get("units", []):
        name = u.get("name")
        if only and name not in only:
            continue
        lv = u.get("loopvc")
        if lv is None:
            out["units"].append({"unit": name, "status": "no-loop"})
            continue
        if errors:
            out["units"].append({"unit": name, "status": "blocked", "reason": f"the export reports errors: {'; '.join(errors)}"})
            continue
        if "error" in lv:
            out["units"].append({"unit": name, "status": "blocked", "reason": f"loop cut not exported: {lv['error']}"})
            continue
        why = check_unit(export, u, lv, lib)
        if isinstance(why, str):
            out["units"].append({"unit": name, "status": "blocked", "reason": why})
        else:
            out["units"].append(dict(unit=name, status="required", **why))
    for name in only or []:
        if not any(x["unit"] == name for x in out["units"]):
            fail(f"the export has no unit {name}")
    return out


def check_unit(export, u, lv, lib):
    j = load(os.path.join(export, lv["file"]), "the loop cut")
    if j.get("format") != "solar-verify-loopvc" or j.get("version") != 1:
        return "the loop cut is not solar-verify-loopvc format 1"
    if j.get("unit") != u["name"]:
        return f"the loop cut names unit {j.get('unit')}"
    if not os.path.isfile(lib) or j["lean"].get("library_sha256") != sha(lib):
        return "LoopVc.lean is not the library the cut was written for"
    if sha(os.path.join(export, j["horn"]["file"])) != j["horn"]["sha256"]:
        return "the Horn view is not the one the cut names"
    edges = {e["id"]: e for e in j["edges"]}
    temps = {t["id"]: t for t in j["templates"]}
    for e in ("entry", "back", "exit", "call", "revert"):
        if e not in edges:
            return f"no {e} edge"
    if edges["call"].get("templates"):
        return "a call inside the loop (call edge): no call summaries in format 1"
    if edges["exit"].get("to") != "return" or edges["exit"].get("outcome") != "normal":
        return "the exit edge does not reach a normal return"
    if edges["revert"].get("templates"):
        return "the revert edge carries obligations"
    by = {}
    for e in ("entry", "back", "exit"):
        for t in edges[e]["templates"]:
            if t not in temps or temps[t]["edge"] != e:
                return f"template {t} is not on edge {e}"
            by.setdefault(e, []).append(temps[t]["role"])
    if not j["candidate"].get("conjuncts"):
        return "no invariant: nothing to cut at (supply one)"
    if "invariant" not in by.get("entry", []):
        return "no invariant template on the entry edge (initiation)"
    if "invariant" not in by.get("back", []):
        return "no invariant template on the back edge (preservation)"
    if "rank" not in by.get("back", []):
        return "no ranking function: termination has no proof (supply decreases)"
    if any(t["edge"] not in ("entry", "back", "exit") for t in j["templates"]):
        return "a template off the entry, back and exit edges"
    listed = [t for e in ("entry", "back", "exit") for t in edges[e]["templates"]]
    if sorted(listed) != sorted(temps):
        return "the edges do not list every template exactly once"
    inst = [i["id"] for t in j["templates"] for i in t["instances"]]
    req = [o["id"] for o in u["obligations"] if o.get("role") == "obligation" and o.get("required")]
    if sorted(inst) != sorted(req) or len(set(inst)) != len(inst):
        return (f"the templates' instances are not the unit's obligations (missing "
                f"{sorted(set(req) - set(inst))}, extra {sorted(set(inst) - set(req))})")
    side = [o["id"] for o in u["obligations"] if o.get("role") != "obligation" and o.get("required")]
    if side:
        return f"required queries outside the cut's templates: {side}"
    return {
        "cut": lv["file"], "cut_sha256": sha(os.path.join(export, lv["file"])),
        "module": j["obligations"]["module"], "loop_module": j["lean"]["module"],
        "namespace": j["lean"]["namespace"],
        "module_sha256": sha(os.path.join(export, j["obligations"]["module"])),
        "loop_module_sha256": sha(os.path.join(export, j["lean"]["module"])),
        "formulas_sha256": j["sha256"]["formulas"], "candidate_sha256": j["sha256"]["candidate"],
        "candidate": {"invariants": [c["text"] for c in j["candidate"]["conjuncts"]],
                      "rank": (j["candidate"].get("rank") or {}).get("text"),
                      "origins": sorted({c["origin"] for c in j["candidate"]["conjuncts"]})},
        "templates": [{"id": t["id"], "edge": t["edge"], "role": t["role"],
                       "instances": [{"id": i["id"], "lean": i["lean"]} for i in t["instances"]]}
                      for t in j["templates"]],
        "reverts": [r["id"] for r in j.get("reverts", [])],
    }


def gen(export, planfile, outdir):
    p = load(planfile, "the plan")
    for u in p["units"]:
        if u["status"] != "required":
            continue
        mod = "LoopCert." + u["unit"]
        path = os.path.join(outdir, *mod.split(".")) + ".lean"
        os.makedirs(os.path.dirname(path), exist_ok=True)
        lm = u["loop_module"].removesuffix(".lean").replace("/", ".")
        ns = u["namespace"]
        L = ["-- Generated by Verify/Infer/loopvc/loopcert.py; do not edit.",
             "import Verify.Discharge.Reconstruct.Tactic", f"import {lm}", "",
             "set_option maxRecDepth 100000", "", f"namespace {mod}",
             "open SolarVerify.Vc SolarVerify.LoopVc", ""]
        for t in u["templates"]:
            for k, i in enumerate(t["instances"]):
                L.append(f"/-- {i['id']}: an instance of template {t['id']} ({t['edge']} edge, {t['role']}). -/")
                L.append(f"theorem {t['id']}_{k} : {i['lean']}.Valid := by vc_smt")
                L.append("")
            body = "List.forall_mem_nil _"
            for k in reversed(range(len(t["instances"]))):
                body = f"List.forall_mem_cons.2 ⟨{t['id']}_{k}, {body}⟩"
            L.append(f"theorem {t['id']}_holds : {ns}.{t['id']}.Valid {ns}.cut {ns}.cand :=")
            L.append(f"  {ns}.{t['id']}_valid.2 ({body})")
            L.append("")
        conj = " ∧ ".join(f"{ns}.{t['id']}.Valid {ns}.cut {ns}.cand" for t in u["templates"])
        edges = ", ".join(f"{t['id']} {t['edge']} {t['role']}" for t in u["templates"])
        L.append(f"/-- Every template on every edge of {u['unit']}'s loop cut holds at the run's candidate ({edges}). -/")
        L.append(f"theorem certified : {conj} :=")
        L.append("  ⟨" + ", ".join(f"{t['id']}_holds" for t in u["templates"]) + "⟩")
        # The same as one list of obligations: the form Verify/Infer/loopvc/Bridge.lean's ForBinds
        # and WhileBinds take (AllValid), which bind the cut to SolidCore's loop rule.
        allv = [(f"{t['id']}_{k}", i["lean"]) for t in u["templates"] for k, i in enumerate(t["instances"])]
        body = "List.forall_mem_nil _"
        for name, _ in reversed(allv):
            body = f"List.forall_mem_cons.2 ⟨{name}, {body}⟩"
        L.append("")
        L.append(f"/-- Every required obligation of {u['unit']}, each an instance of one template, is valid. -/")
        L.append(f"theorem obligations_valid : ∀ o ∈ [{', '.join(l for _, l in allv)}], Obligation.Valid o :=")
        L.append(f"  {body}")
        L += ["", "open Lean Elab Command in", "#eval show CommandElabM Unit from do",
              f"  let axs ← Lean.collectAxioms (String.toName \"{mod}.certified\")",
              "  IO.println s!\"AXIOMS: {String.intercalate \" \" (axs.toList.map toString)}\"", "",
              f"end {mod}", ""]
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(L))
        print(path)


def receipt(planfile, axdir, summary):
    p = load(planfile, "the plan")
    rows = {}
    if summary:
        with open(summary) as f:
            head = f.readline().rstrip("\n").split("\t")
            for line in f:
                r = dict(zip(head, line.rstrip("\n").split("\t")))
                rows[r.get("id")] = r
    out = []
    for u in p["units"]:
        if u["status"] == "no-loop":
            continue
        if u["status"] == "blocked":
            out.append({"unit": u["unit"], "status": "blocked", "reason": u["reason"]})
            continue
        why = []
        axf = os.path.join(axdir, u["unit"] + ".out")
        text = open(axf).read() if os.path.isfile(axf) else ""
        m = re.search(r"^AXIOMS: (.*)$", text, re.M)
        code = re.search(r"^EXIT (\d+)$", text, re.M)
        axs = sorted(set(m.group(1).split())) if m else None
        if not code or code.group(1) != "0":
            why.append(f"the certificate does not check (exit {code.group(1) if code else 'missing'})")
        elif axs is None:
            why.append("no axiom report")
        elif not set(axs) <= ALLOWED:
            why.append(f"axioms {sorted(set(axs) - ALLOWED)}")
        vac = {}
        if summary:
            for t in u["templates"]:
                for i in t["instances"]:
                    r = rows.get(i["id"])
                    vac[i["id"]] = r and r.get("vacuous")
                    if r is None or r.get("status") != "proved":
                        why.append(f"{i['id']} not proved by Verify/Discharge ({r and r.get('status')})")
                    elif r.get("vacuous") == "yes":
                        why.append(f"{i['id']} holds vacuously")
        out.append({"unit": u["unit"], "status": "failed" if why else "proved", "reasons": why,
                    "theorem": f"LoopCert.{u['unit']}.certified", "axioms": axs,
                    "edges": {e: [f"{t['id']}:{t['role']}" for t in u["templates"] if t["edge"] == e]
                              for e in ("entry", "back", "exit")},
                    "candidate": u["candidate"], "formulas_sha256": u["formulas_sha256"],
                    "cut_sha256": u["cut_sha256"], "vacuity": vac or None})
    json.dump({"manifest_sha256": p["manifest_sha256"], "units": out}, sys.stdout, indent=2, ensure_ascii=False)
    sys.stdout.write("\n")
    if any(o["status"] == "failed" for o in out):
        sys.exit(1)
    sys.exit(3 if any(o["status"] == "blocked" for o in out) else 0)


def main():
    a = sys.argv[1:]
    if a[:1] == ["annotate"] and len(a) == 4:
        annotate(*a[1:])
    elif a[:1] == ["plan"] and len(a) >= 2:
        only = [a[i + 1] for i in range(2, len(a) - 1) if a[i] == "--only"]
        p = plan(a[1], only)
        json.dump(p, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
        sys.exit(3 if any(u["status"] == "blocked" for u in p["units"]) else 0)
    elif a[:1] == ["gen"] and len(a) == 4:
        gen(*a[1:])
    elif a[:1] == ["receipt"] and len(a) in (3, 4):
        receipt(a[1], a[2], a[3] if len(a) == 4 else None)
    else:
        fail("usage: loopcert.py annotate SOURCE INVARIANTS OUT | plan EXPORT [--only C.f]... | "
             "gen EXPORT PLAN OUTDIR | receipt PLAN AXIOMS_DIR [SUMMARY]")


main()
