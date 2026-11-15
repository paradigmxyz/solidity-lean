#!/usr/bin/env bash
# Checks the CTI corpus: regenerates it and compares bytes, re-checks every record from its inputs,
# and requires the checker to refuse corrupted records.  Needs python3 with z3-solver 5.4.1
# (requirements.txt); PYTHON overrides the interpreter.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
py=${PYTHON:-python3}
cd "$here"
"$py" -c 'import z3, sys; v = z3.get_version_string(); sys.exit(0 if v == "5.4.1" else f"want z3 5.4.1, have {v}")'
# Python 3.14 gets other models from the same z3, so regeneration differs; 3.12 and 3.13 match.
"$py" -c 'import sys; sys.exit(0 if sys.version_info[:2] in ((3, 12), (3, 13)) else f"want Python 3.12 or 3.13, have {sys.version.split()[0]}")'
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "== regenerate"
"$py" cti.py gen problems.json "$work/corpus" > /dev/null
diff -r corpus "$work/corpus" || { echo "FAIL: the corpus differs from its regeneration" >&2; exit 1; }

echo "== check"
"$py" cti.py check problems.json corpus

echo "== refuse corrupted records"
"$py" - "$work" <<'PY'
import json, os, shutil, subprocess, sys
work = sys.argv[1]
py = sys.executable

def load(pid):
    return [json.loads(l) for l in open(f"corpus/{pid}.jsonl")]

def run(name, pid, edit, want):
    d = f"{work}/{name}"
    shutil.copytree("corpus", d)
    recs = load(pid)
    edit(recs)
    with open(f"{d}/{pid}.jsonl", "w") as f:
        for r in recs:
            f.write(json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n")
    p = subprocess.run([py, "cti.py", "check", "problems.json", d, "--only", pid], capture_output=True, text=True)
    if p.returncode == 0 or want not in p.stdout:
        print(f"FAIL {name}: checker did not refuse with '{want}'\n{p.stdout}{p.stderr}")
        sys.exit(1)
    print(f"ok   {name}: {want}")

def first(recs, **kw):
    return next(r for r in recs if all(r.get(k) == v for k, v in kw.items()))

# an implication pair's pre-state labelled negative (ICE: only a goal's state is negative)
def neg_pre(recs):
    r = first(recs, kind="cti", label="implication")
    r["label"] = "negative"
run("pre-state-negative", "infer-counter-u256", neg_pre, "negative label off a use (goal) obligation")

# an unreached implication pair promoted to a positive (failure to replay is no reachability)
def promote(recs):
    r = first(recs, kind="cti", label="implication")
    r["label"] = "positive"
run("promote-unreached", "infer-counter-u256", promote, "positive without a trace")

# a positive's trace forged: one value changed so a step is no back edge
def forge(recs):
    r = next(r for r in recs if r["kind"] == "cti" and r["label"] == "positive" and r["replay"]["depth"] >= 1)
    st = r["replay"]["trace"][0]
    k = sorted(st)[0]
    st[k] = str(int(st[k]) + 7)
run("forged-trace", "infer-okwhile-u256", forge, "trace")

# a not-inductive candidate claimed inductive
def claim(recs):
    first(recs, kind="candidate", status="not-inductive")["status"] = "inductive"
run("claim-inductive", "infer-counter-u256", claim, "does not follow from its records")

# a CTI that is not one: the post-state replaced by the pre-state, where the candidate holds
def fake(recs):
    r = first(recs, kind="cti", label="implication")
    r["s_prime"] = r["s"]
run("not-a-cti", "infer-counter-u256", fake, "is not a back edge")

# a solver unknown hidden: an inconclusive record under an inductive candidate
def hide(recs):
    c = first(recs, kind="candidate", status="inductive")
    recs.append({"kind": "cti", "id": c["id"] + "#u", "candidate": c["id"], "edge": "back",
                 "obligation": "preservation", "s": None, "s_prime": None, "label": "inconclusive",
                 "reason": "timeout"})
run("unknown-is-not-proved", "infer-drain-u256", hide, "does not follow from its records")

# the guarded-strengthening flag dropped
def unflag(recs):
    c = first(recs, kind="candidate", id="infer-counter-u256/guarded-dead")
    c["flags"] = [f for f in c["flags"] if f["flag"] != "passes-only-because-antecedent-false"]
run("guard-flag", "infer-counter-u256", unflag, "expected flag")

# a reached goal violation reported as a weak candidate
def weak(recs):
    first(recs, kind="candidate", status="goal-violated")["status"] = "too-weak"
run("bug-as-weak", "solar-bump-sdl22", weak, "does not follow from its records")
PY

echo "== unsupported problems are never proved"
"$py" - <<'PY'
import cti
spec = {"id": "nonlinear", "chc": "test/nonlinear.smt2", "origin": "test", "vars": ["x"], "candidates": []}
recs = cti.run_problem(spec, ".")
assert recs[0]["status"] == "unsupported" and "nonlinear" in recs[0]["reason"], recs
assert cti.status_of([{"label": "inconclusive", "obligation": "preservation"}]) == "inconclusive"
print("ok   nonlinear clause: unsupported; unknown: inconclusive")
PY
echo "OK"
