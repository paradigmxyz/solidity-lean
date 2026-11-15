#!/usr/bin/env python3
"""The certification blueprint's checker (docs/blueprint/README.md).

Reads docs/blueprint/obligations.toml, checks the graph (ids, deps, edges, acyclic, the
human_review rule), then for every node with a `decl` elaborates its `module` in Lean
(`lake env lean`, one process per module) and reads the declaration's kind, whether it is a proof
or a statement, and its transitive axioms (`Lean.collectAxioms`, what `#print axioms` prints).
Each node gets a status:

  proved          a proof whose axioms are a subset of propext, Classical.choice, Quot.sound
  sorry           a proof that depends on sorryAx
  axioms          a proof that depends on any other axiom (ofReduceBool from native_decide, ...)
  statement-only  the decl is a statement (a Prop or a predicate), not a proof
  missing         no decl yet, or the decl is not in its module
  unbuilt         the decl's module is not built in this run, so nothing is known of it; an unbuilt
                  node is never ready (a build step for its module comes first)
  trusted         a stated trust boundary (E0, E1); never proved, never a proof obligation
  external        evidence outside Lean (the solar driver's byte binding); never proved here

and writes docs/blueprint/status.json, docs/blueprint/status.md and the ready list (nodes not
satisfied whose deps are all satisfied, ordered by how many unsatisfied nodes they unblock).

  python3 scripts/blueprint/check.py                      # check, print the summary
  python3 scripts/blueprint/check.py --write              # also write status.json / status.md
  python3 scripts/blueprint/check.py --baseline docs/blueprint/status.json
                                                          # fail if a node proved there is not now
  python3 scripts/blueprint/check.py --no-lean            # graph checks only (no Lean)

Build the modules first (the refinement workflow's builds); a module that is not built reports
its nodes as unbuilt, never as proved.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import tomllib
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GRAPH = ROOT / "docs/blueprint/obligations.toml"
OUT_JSON = ROOT / "docs/blueprint/status.json"
OUT_MD = ROOT / "docs/blueprint/status.md"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EDGES = {"E0", "E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8"}
KINDS = {"obligation", "lemma", "premise", "spec", "statement", "trusted", "external", "goal", "deliverable"}
# Kinds that are not Lean declarations: their receipt (in obligations.toml, once delivered) is the
# evidence, and they are never "proved".
RECEIPT_KINDS = {"deliverable", "goal", "external"}
# human_review is for what a person must read and agree with: statements, premises, specs.
REVIEWABLE = {"premise", "spec", "statement", "trusted"}
# A dep on one of these kinds is satisfied by its statement existing: it is a hypothesis or a
# definition the obligation speaks of, not something to prove.
STATEMENT_KINDS = {"premise", "spec", "statement"}
FIELDS = {"id", "kind", "contract", "function", "edge", "statement", "decl", "module", "deps",
          "lane", "owner", "branch", "acceptance", "receipt", "priority", "human_review", "note"}

MARK = "BLUEPRINT\t"

# The audit command, inlined so that it needs no build of its own. For each name: is it in the
# environment, which module declares it, its kind, whether its type is a Prop (it is a proof)
# or ends in Prop (it is a statement), and its transitive axioms (as #print axioms computes them).
AUDIT_PRELUDE = r"""
open Lean Elab Command Meta in
elab "#blueprint_audit " id:ident : command => do
  let n := id.getId
  let env ← getEnv
  match env.find? n with
  | none => IO.println s!"BLUEPRINT\t{n}\tnotfound"
  | some ci =>
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let (proof, pred) ← liftTermElabM do
      let proof ← isProp ci.type
      let pred ← forallTelescopeReducing ci.type fun _ b => return b.isProp
      return (proof, pred)
    let mod := match env.getModuleIdxFor? n with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "<this file>"
    let axs ← collectAxioms n
    let axs := (axs.map toString).qsort (· < ·)
    IO.println s!"BLUEPRINT\t{n}\tfound\t{kind}\t{proof}\t{pred}\t{mod}\t{String.intercalate "," axs.toList}"
"""


def load_graph(path: Path) -> dict:
    with open(path, "rb") as f:
        return tomllib.load(f)


def validate(data: dict) -> tuple[list[dict], list[str]]:
    errors: list[str] = []
    nodes = data.get("node", [])
    ids: dict[str, dict] = {}
    for n in nodes:
        nid = n.get("id")
        if not nid:
            errors.append(f"node without id: {n}")
            continue
        if nid in ids:
            errors.append(f"{nid}: duplicate id")
        ids[nid] = n
        extra = set(n) - FIELDS
        if extra:
            errors.append(f"{nid}: unknown fields {sorted(extra)}")
        kind = n.get("kind")
        if kind not in KINDS:
            errors.append(f"{nid}: kind {kind!r} not one of {sorted(KINDS)}")
        if not n.get("statement"):
            errors.append(f"{nid}: no statement")
        if "\n" in n.get("statement", ""):
            errors.append(f"{nid}: statement must be one line")
        if not n.get("lane"):
            errors.append(f"{nid}: no owner lane")
        if not n.get("owner"):
            errors.append(f"{nid}: no owner (the lane's thread id, or unassigned)")
        if "branch" not in n:
            errors.append(f"{nid}: no branch (empty until one is assigned)")
        if not n.get("acceptance"):
            errors.append(f"{nid}: no acceptance criterion")
        if n.get("priority", "P2") not in {"P0", "P1", "P2", "P3"}:
            errors.append(f"{nid}: priority is one of P0..P3")
        rc = n.get("receipt")
        if rc is not None:
            if kind not in RECEIPT_KINDS:
                errors.append(f"{nid}: a {kind} gets its receipt from the checker, not from obligations.toml")
            elif not (isinstance(rc, dict) and rc.get("sha") and rc.get("check")):
                errors.append(f"{nid}: a receipt is {{sha = ..., check = <run url or local log>}}")
        if not isinstance(n.get("human_review"), bool):
            errors.append(f"{nid}: human_review must be true or false")
        elif n["human_review"] and kind not in REVIEWABLE:
            errors.append(f"{nid}: human_review is for statements, premises and specs, not a {kind}")
        edge = n.get("edge")
        if edge is not None and edge not in EDGES:
            errors.append(f"{nid}: edge {edge!r} not one of E0..E8")
        if kind == "obligation" and (edge not in EDGES - {"E0", "E1"} or not n.get("contract")
                                     or not n.get("function")):
            errors.append(f"{nid}: an obligation names a contract, a function and an edge E2..E8")
        if kind in {"trusted", "external"} and n.get("decl"):
            errors.append(f"{nid}: a {kind} node has no decl")
        if n.get("decl") and not n.get("module"):
            errors.append(f"{nid}: decl {n['decl']} without the module that declares it")
    for n in nodes:
        for d in n.get("deps", []):
            if d not in ids:
                errors.append(f"{n.get('id')}: unknown dep {d}")
            if d == n.get("id"):
                errors.append(f"{d}: depends on itself")
    # Acyclic (iterative depth-first search).
    color: dict[str, int] = {}
    for start in ids:
        if color.get(start):
            continue
        stack = [(start, iter(ids[start].get("deps", [])))]
        color[start] = 1
        while stack:
            nid, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[nid] = 2
                stack.pop()
            elif nxt in ids:
                c = color.get(nxt, 0)
                if c == 1:
                    cyc = [s for s, _ in stack] + [nxt]
                    errors.append("cycle: " + " -> ".join(cyc[cyc.index(nxt):]))
                elif c == 0:
                    color[nxt] = 1
                    stack.append((nxt, iter(ids[nxt].get("deps", []))))
    return nodes, errors


def run_lean(modules: list[str], decls: list[str], memory: int, timeout: int) -> tuple[dict, str]:
    """Elaborate modules together and audit decls. Returns (results by decl, failure reason)."""
    src = "import Lean\n" + "".join(f"import {m}\n" for m in modules) + AUDIT_PRELUDE + "".join(
        f"\n#blueprint_audit {d}" for d in decls) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / ".lake", delete=False,
                                     prefix="blueprint_") as f:
        f.write(src)
        path = f.name
    try:
        p = subprocess.run(["lake", "env", "lean", "-M", str(memory), path], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout)
        out = (p.stdout + p.stderr).replace(path, "<audit>").replace(f"{ROOT}/", "")
    except subprocess.TimeoutExpired:
        return {}, f"lean timed out after {timeout}s"
    except FileNotFoundError:
        return {}, "lake not found"
    finally:
        os.unlink(path)
    res: dict[str, dict] = {}
    for line in out.splitlines():
        if not line.startswith(MARK):
            continue
        parts = line.split("\t")
        name = parts[1]
        if parts[2] == "notfound":
            res[name] = {"found": False}
        else:
            res[name] = {"found": True, "kind": parts[3], "proof": parts[4] == "true",
                         "predicate": parts[5] == "true", "declared_in": parts[6],
                         "axioms": [a for a in parts[7].split(",") if a] if len(parts) > 7 else []}
    if not res:
        first = next((l for l in out.splitlines() if "error" in l), out.strip()[:300])
        unbuilt = re.search(r"object file .* does not exist|unknown module prefix|unknown package|"
                            r"file not found|no such file", out, re.I)
        return {}, f"{'module not built' if unbuilt else 'lean failed'}: {first.strip()[:300]}"
    return res, ""


def classify(n: dict, info: dict | None, failure: str) -> tuple[str, str]:
    kind = n["kind"]
    if kind == "trusted":
        return "trusted", "a stated trust boundary"
    if kind in RECEIPT_KINDS and not n.get("decl"):
        if n.get("receipt"):
            return "delivered", f"receipt {n['receipt']['sha'][:12]} {n['receipt']['check']}"
        if kind == "external":
            return "external", "evidence outside Lean, not checked here"
        return "missing", "not delivered: no receipt yet"
    if not n.get("decl"):
        return "missing", "no decl yet"
    if failure:
        if failure.startswith(("module not built", "module not audited")):
            return "unbuilt", failure
        return "missing", failure
    if info is None or not info.get("found"):
        return "missing", f"{n['decl']} not found in {n['module']}"
    if info["kind"] == "axiom":
        return "axioms", f"{n['decl']} is itself an axiom"
    if info["proof"]:
        axs = set(info["axioms"])
        if "sorryAx" in axs:
            return "sorry", "depends on sorryAx"
        bad = sorted(axs - ALLOWED_AXIOMS)
        if bad:
            return "axioms", "depends on " + ", ".join(bad)
        return "proved", ""
    if info["predicate"]:
        return "statement-only", "a statement, not a proof"
    if kind in STATEMENT_KINDS and info["kind"] == "def":
        return "statement-only", "a definition the statement is made of (data, not a Prop)"
    return "missing", f"{n['decl']} is a {info['kind']} that is neither a proof nor a statement"


def satisfied(n: dict, status: str) -> bool:
    """Whether a node, as a dep, lets the nodes on it go ahead: proved, a stated premise, spec or
    statement, or a boundary the target states (trusted, external). Only proved is ever evidence."""
    return (status in {"proved", "delivered", "trusted", "external"}
            or (n["kind"] in STATEMENT_KINDS and status == "statement-only"))


def compute(nodes: list[dict], results: dict, failures: dict, receipt: dict | None = None) -> dict:
    by_id = {n["id"]: n for n in nodes}
    status: dict[str, dict] = {}
    for n in nodes:
        info = results.get(n["decl"]) if n.get("decl") else None
        fail = failures.get(n.get("module"), "") if n.get("decl") else ""
        st, why = classify(n, info, fail)
        entry: dict = {"status": st}
        if why:
            entry["reason"] = why
        for k in ("owner", "branch", "acceptance"):
            if n.get(k):
                entry[k] = n[k]
        if st == "proved" and receipt:
            entry["receipt"] = receipt
        elif n.get("receipt"):
            entry["receipt"] = n["receipt"]
        if info and info.get("found"):
            entry["axioms"] = info["axioms"]
            if info["declared_in"] != n["module"]:
                entry["declared_in"] = info["declared_in"]
        status[n["id"]] = entry
    ok = {i: satisfied(by_id[i], status[i]["status"]) for i in by_id}
    rdeps: dict[str, set[str]] = defaultdict(set)
    for n in nodes:
        for d in n.get("deps", []):
            rdeps[d].add(n["id"])

    def downstream(i: str) -> set[str]:
        seen: set[str] = set()
        todo = [i]
        while todo:
            for j in rdeps[todo.pop()]:
                if j not in seen:
                    seen.add(j)
                    todo.append(j)
        return seen

    ready = []
    for n in nodes:
        i = n["id"]
        if ok[i] or status[i]["status"] == "unbuilt":
            continue
        if all(ok[d] for d in n.get("deps", [])):
            unblocks = sum(1 for j in downstream(i) if not ok[j])
            ready.append({"id": i, "priority": n.get("priority", "P2"), "unblocks": unblocks,
                          "lane": n["lane"], "owner": n.get("owner", ""), "status": status[i]["status"]})
    # Priority first (P0 before P3), then how many unsatisfied nodes depend on it, directly or not.
    ready.sort(key=lambda r: (r["priority"], -r["unblocks"], r["id"]))
    for i in status:
        status[i]["deps_satisfied"] = all(ok[d] for d in by_id[i].get("deps", []))
    counts: dict[str, int] = defaultdict(int)
    for e in status.values():
        counts[e["status"]] += 1
    return {"allowed_axioms": sorted(ALLOWED_AXIOMS), "counts": dict(sorted(counts.items())),
            "nodes": dict(sorted(status.items())), "ready": ready}


def run_receipt(log: str | None) -> dict:
    """Where this run's verdicts come from: the commit, and the CI run or the local log."""
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
    if os.environ.get("GITHUB_RUN_ID"):
        check = (f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/"
                 f"{os.environ.get('GITHUB_REPOSITORY', '')}/actions/runs/{os.environ['GITHUB_RUN_ID']}")
    else:
        check = f"local:{log or 'check.py stdout'}"
    return {"sha": sha + ("+uncommitted" if dirty else ""), "check": check}


def regressions(base: dict, report: dict) -> list[str]:
    """Every node proved in the baseline that is not proved in the report."""
    out = []
    for i, e in sorted(base["nodes"].items()):
        if e["status"] != "proved":
            continue
        now = report["nodes"].get(i)
        if now is None:
            out.append(f"{i} was proved and is no longer in the graph")
        elif now["status"] != "proved":
            out.append(f"{i} regressed: proved -> {now['status']} ({now.get('reason', '')})")
    return out


def markdown(nodes: list[dict], report: dict) -> str:
    st = report["nodes"]
    lines = ["# Certification blueprint: status", "",
             "Generated by `python3 scripts/blueprint/check.py --write` from "
             "[obligations.toml](obligations.toml); do not edit. `proved` means a kernel-checked "
             "declaration whose axioms are only propext, Classical.choice and Quot.sound. It does not say "
             "that the declaration states the node's statement: that is what `human_review` on the "
             "node's spec, premise and statement deps asks a person to confirm.", "",
             "Counts: " + ", ".join(f"{k} {v}" for k, v in report["counts"].items()), "",
             f"Modules elaborated in this run: {len(report.get('modules', {}).get('audited', []))} of "
             f"{len(report.get('modules', {}).get('audited', [])) + len(report.get('modules', {}).get('not_audited', {}))}; "
             "a node whose module was not elaborated is missing, with the reason.", "",
             "## Ready", "",
             "Not satisfied, every dep satisfied, ordered by priority, then by how many unsatisfied nodes each "
             "unblocks.", "",
             "| # | Node | Priority | Status | Unblocks | Lane | Owner |", "|---|---|---|---|---|---|---|"]
    for k, r in enumerate(report["ready"], 1):
        lines.append(f"| {k} | `{r['id']}` | {r['priority']} | {r['status']} | {r['unblocks']} | {r['lane']} | {r['owner']} |")
    lines += ["", "## Nodes", "",
              "| Node | Edge | Status | Decl | Deps | Lane | Owner | Branch | Review | Statement | Acceptance |",
              "|---|---|---|---|---|---|---|---|---|---|---|"]
    for n in nodes:
        e = st[n["id"]]
        status = e["status"] + (f" ({e['reason']})" if e.get("reason") else "")
        decl = f"`{n['decl']}`" if n.get("decl") else ""
        deps = ", ".join(f"`{d}`" for d in n.get("deps", []))
        if e.get("receipt"):
            status += f" [{e['receipt']['sha'][:12]}, {e['receipt']['check']}]"
        cells = [f"`{n['id']}`", n.get("edge", ""), status, decl, deps, n["lane"], n.get("owner", ""),
                 n.get("branch", ""), "yes" if n["human_review"] else "", n["statement"], n.get("acceptance", "")]
        lines.append("| " + " | ".join(c.replace("|", "\\|") for c in cells) + " |")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--graph", type=Path, default=GRAPH)
    ap.add_argument("--write", action="store_true", help="write status.json and status.md")
    ap.add_argument("--out", type=Path, default=None, help="write status.json here (and status.md beside it)")
    ap.add_argument("--baseline", type=Path, help="fail if a node proved in this status.json is not proved now")
    ap.add_argument("--no-lean", action="store_true", help="check the graph only")
    ap.add_argument("--memory", type=int, default=int(os.environ.get("BLUEPRINT_MEMORY", "6000")))
    ap.add_argument("--timeout", type=int, default=1800, help="seconds per Lean process")
    ap.add_argument("--batch", type=int, default=8, help="modules per Lean process")
    ap.add_argument("--log", help="the local log this run writes, named in the receipts")
    ap.add_argument("--no-fresh-check", action="store_true",
                    help="audit oleans without asking lake whether they are up to date")
    ap.add_argument("--only-module", action="append", default=[], help="audit only these modules")
    args = ap.parse_args()

    nodes, errors = validate(load_graph(args.graph))
    base = json.loads(args.baseline.read_text()) if args.baseline else None
    if base:
        known = {n["id"] for n in nodes}
        for i, e in sorted(base["nodes"].items()):
            if e["status"] == "proved" and i not in known:
                errors.append(f"{i} is proved in the baseline and no longer in the graph")
    if errors:
        for e in errors:
            print(f"error: {e}", file=sys.stderr)
        return 2
    print(f"graph: {len(nodes)} nodes, acyclic, deps resolve")
    if args.no_lean:
        return 0

    (ROOT / ".lake").mkdir(exist_ok=True)
    by_mod: dict[str, list[str]] = defaultdict(list)
    for n in nodes:
        if n.get("decl") and n["decl"] not in by_mod[n["module"]]:
            by_mod[n["module"]].append(n["decl"])
    results: dict[str, dict] = {}
    failures: dict[str, str] = {}
    mods = []
    for mod in sorted(by_mod):
        if args.only_module and mod not in args.only_module:
            failures[mod] = "module not audited in this run"
        else:
            mods.append(mod)
    # Modules are imported a batch at a time (their closures share most oleans). A batch that does
    # not elaborate (a module not built, two modules declaring one name) is redone one module at a
    # time, so that each failure is the module's own.
    # A module whose olean is missing or older than its sources or imports is not audited: its old
    # olean would answer for code that is no longer there.
    if not args.no_fresh_check:
        fresh = []
        for mod in mods:
            p = subprocess.run(["lake", "build", "--no-build", mod], cwd=ROOT, capture_output=True, text=True)
            if p.returncode == 0:
                fresh.append(mod)
            else:
                failures[mod] = "module not built (or out of date) in this run"
                print(f"{mod}: not built or out of date", flush=True)
        mods = fresh
    for k in range(0, len(mods), max(args.batch, 1)):
        batch = mods[k:k + max(args.batch, 1)]
        decls = [d for m in batch for d in by_mod[m]]
        res, fail = run_lean(batch, decls, args.memory, args.timeout) if len(batch) > 1 else ({}, "single")
        if not fail:
            print(f"{', '.join(batch)}: {len(res)} decls audited", flush=True)
            results.update(res)
            continue
        for mod in batch:
            res, fail = run_lean([mod], by_mod[mod], args.memory, args.timeout)
            print(f"{mod}: {fail or f'{len(res)} decls audited'}", flush=True)
            results.update(res)
            if fail:
                failures[mod] = fail
    report = compute(nodes, results, failures, run_receipt(args.log))
    report["modules"] = {"audited": sorted(m for m in by_mod if m not in failures),
                         "not_audited": dict(sorted(failures.items()))}
    print("status: " + ", ".join(f"{k} {v}" for k, v in report["counts"].items()))
    print("ready (top 10): " + ", ".join(f"{r['id']} ({r['unblocks']})" for r in report["ready"][:10]))

    rc = 0
    if base:
        for msg in regressions(base, report):
            print(f"error: {msg}", file=sys.stderr)
            rc = 1
        newly = sorted(i for i, e in report["nodes"].items() if e["status"] == "proved"
                       and base["nodes"].get(i, {}).get("status") != "proved")
        if newly:
            print("newly proved, not in the baseline yet (commit the new status.json): " + ", ".join(newly))
    out_json = args.out or (OUT_JSON if args.write else None)
    if out_json:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(json.dumps(report, indent=1) + "\n")
        out_json.with_suffix(".md").write_text(markdown(nodes, report))
    return rc


if __name__ == "__main__":
    sys.exit(main())
