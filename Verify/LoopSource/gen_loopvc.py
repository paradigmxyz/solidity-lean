#!/usr/bin/env python3
"""Bind solar-verify's emitted loop obligations to Lean obligations, checked in the kernel.

Usage: gen_loopvc.py MANIFEST DUMP_MODULE NAMESPACE OUT.lean [--chunk K]

MANIFEST is the manifest.json of `solar-verify --emit-lean DIR` for one function and DUMP_MODULE
the module name of the same run's `--dump-lean FILE` (its `script`, the commands sent to the
solver). For every required obligation of the manifest, this writes the Lean obligation
`hs ⟹ φ` the script's `check-sat` gives with solar-verify's names kept (`checkObRaw`,
Verify/LoopSource/CheckRaw.lean): it inlines the definitions as `inline` does, flattens the
conjunctions, and keeps the facts `hypOk` cannot take by default. The module states, all by
kernel evaluation, with no solver:

* `check : checkLoop script obs = true`: each Lean obligation is the script's at its index;
* `ob_i : dischargeAt script i = true` for every `check-sat`, and `script_valid : Valid script`;
* `obs_valid : ObsValid (obs.map (·.2))`, from the two.

Each obligation is named after its kind in the manifest (`init`, `consec`, `decr`, `post`,
`inv`) and keeps the manifest id. A mismatch between this emulation of `inline` and Lean's is
not trusted: it makes `check` fail to evaluate to true.
"""
import json
import re
import sys

KINDS = {
    "loop invariant not satisfied on entry": "init",
    "loop invariant not preserved by the loop body": "consec",
    "loop does not terminate: decreases clause not decreased": "decr",
    "postcondition not satisfied": "post",
    "contract invariant not preserved": "inv",
}


def tokens(s):
    return re.findall(r'"(?:[^"\\]|\\.)*"|\.[A-Za-z0-9]+|\d+|[()\[\],]', s)


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i]

    def take(self, x=None):
        v = self.t[self.i]
        if x is not None and v != x:
            raise SyntaxError(f"expected {x}, got {v} at {self.i}")
        self.i += 1
        return v

    def tm(self):
        if self.peek() == "(":
            self.take("(")
            v = self.tm()
            self.take(")")
            return v
        k = self.take()
        if k in (".tt", ".ff"):
            return (k[1:],)
        if k == ".num":
            return ("num", int(self.take()))
        if k in (".ivar", ".bvar", ".avar", ".a2var"):
            return (k[1:], json.loads(self.take()))
        if k == ".app":
            f = json.loads(self.take())
            return ("app", f, self.lst())
        if k == ".all":
            x = json.loads(self.take())
            return ("all", x, self.tm())
        raise SyntaxError(k)

    def lst(self):
        self.take("[")
        out = []
        while self.peek() != "]":
            out.append(self.tm())
            if self.peek() == ",":
                self.take(",")
        self.take("]")
        return out


def parse_script(path):
    src = open(path).read()
    body = src[src.index("def script : List Cmd := [") + len("def script : List Cmd := ["):]
    body = body[: body.index("\n]\n")]
    cmds = []
    for line in body.split("\n"):
        line = line.strip().rstrip(",")
        if not line:
            continue
        if line.startswith(".assert "):
            p = P(tokens(line[len(".assert "):]))
            cmds.append(("assert", p.tm()))
        elif line in (".push", ".pop", ".checkSat"):
            cmds.append((line[1:],))
        else:
            cmds.append(("other",))
    return cmds


def obligations(cmds):
    stk, out = [[]], []
    for c in cmds:
        if c[0] == "assert":
            if stk:
                stk[0] = [c[1]] + stk[0]
            else:
                stk = [[c[1]]]
        elif c[0] == "push":
            stk = [[]] + stk
        elif c[0] == "pop":
            stk = stk[1:]
        elif c[0] == "checkSat":
            flat = [t for f in stk for t in f]
            out.append(list(reversed(flat)))
    return out


SORT_OF_VAR = {"ivar": "int", "bvar": "bool", "avar": "arr", "a2var": "arr2"}


def sort(t):
    k = t[0]
    if k == "num":
        return "int"
    if k in ("tt", "ff"):
        return "bool"
    if k in SORT_OF_VAR:
        return SORT_OF_VAR[k]
    if k == "all":
        return "bool" if sort(t[2]) == "bool" else None
    f, ss = t[1], [sort(a) for a in t[2]]
    if f in ("+", "*", "div", "mod") and ss == ["int", "int"]:
        return "int"
    if f == "-" and ss in (["int"], ["int", "int"]):
        return "int"
    if f in ("<=", "<", ">=", ">") and ss == ["int", "int"]:
        return "bool"
    if f == "=" and len(ss) == 2 and ss[0] is not None and ss[0] == ss[1]:
        return "bool"
    if f == "not" and ss == ["bool"]:
        return "bool"
    if f == "=>" and ss == ["bool", "bool"]:
        return "bool"
    if f in ("and", "or"):
        return "bool" if all(s == "bool" for s in ss) else None
    if f == "ite" and len(ss) == 3 and ss[0] == "bool" and ss[1] is not None and ss[1] == ss[2]:
        return ss[1]
    raise ValueError(f"sort of {f} not emulated; extend gen_loopvc.py")


def tvars(t):
    k = t[0]
    if k in SORT_OF_VAR:
        return [t[1]]
    if k == "app":
        return [v for a in t[2] for v in tvars(a)]
    if k == "all":
        return [t[1]] + tvars(t[2])
    return []


def binders(t):
    if t[0] == "app":
        return [v for a in t[2] for v in binders(a)]
    if t[0] == "all":
        return [t[1]] + binders(t[2])
    return []


def def_of(t):
    if t[0] == "app" and t[1] == "=" and len(t[2]) == 2 and t[2][0][0] in SORT_OF_VAR:
        x, u = t[2]
        if sort(u) == SORT_OF_VAR[x[0]] and x[1] not in tvars(u):
            return SORT_OF_VAR[x[0]], x[1], u
    return None


def subst(t, s, x, u):
    k = t[0]
    if k in SORT_OF_VAR:
        return u if (SORT_OF_VAR[k] == s and t[1] == x) else t
    if k == "app":
        return ("app", t[1], [subst(a, s, x, u) for a in t[2]])
    if k == "all":
        if s == "int" and t[1] == x:
            return t
        return ("all", t[1], subst(t[2], s, x, u))
    return t


def inline(fs):
    done, rest, n = [], list(fs), len(fs)
    while n > 0 and rest:
        f, rest = rest[0], rest[1:]
        n -= 1
        d = def_of(f)
        if d and all(y not in tvars(d[2]) for t in done + rest for y in binders(t)):
            s, x, u = d
            done = [subst(t, s, x, u) for t in done]
            rest = [subst(t, s, x, u) for t in rest]
        else:
            done = [f] + done
    return list(reversed(done)) + rest


def flatten(t):
    if t[0] == "tt":
        return []
    if t[0] == "app" and t[1] == "and":
        return [c for a in t[2] for c in flatten(a)]
    return [t]


def range_var(h):
    """The variable of a fact `0 <= x` or `x <= M` that `defaultOk` takes when x is not named."""
    if h[0] == "app" and h[1] == "<=" and len(h[2]) == 2:
        a, b = h[2]
        if a == ("num", 0) and b[0] == "ivar":
            return b[1]
        if a[0] == "ivar" and b[0] == "num":
            return a[1]
    return None


def lean_obligation(e):
    e1 = list(reversed(inline(e)))
    head = e1[0]
    assert head[0] == "app" and head[1] == "not" and len(head[2]) == 1, head
    phi = head[2][0]
    hyps = []
    for h in [c for t in e1[1:] for c in flatten(t)]:
        if h not in hyps:
            hyps.append(h)
    # Keep every fact but the ranges of names nothing else mentions (defaultOk takes those).
    core = [h for h in hyps if range_var(h) is None]
    named = set(tvars(phi)) | {v for h in core for v in tvars(h)}
    hs = [h for h in hyps if range_var(h) is None or range_var(h) in named]
    return hs, phi


def lean(t):
    k = t[0]
    if k == "num":
        return f"(.num {t[1]})"
    if k in ("tt", "ff"):
        return "." + k
    if k in SORT_OF_VAR:
        return f"(.{k} {json.dumps(t[1])})"
    if k == "app":
        return f"(.app {json.dumps(t[1])} [{', '.join(lean(a) for a in t[2])}])"
    return f"(.all {json.dumps(t[1])} {lean(t[2])})"


def main(argv):
    manifest, dump_mod, ns, out = argv[:4]
    chunk = 4
    if "--chunk" in argv:
        chunk = int(argv[argv.index("--chunk") + 1])
    m = json.load(open(manifest))
    (unit,) = m["units"]
    dump_path = dump_mod.replace(".", "/") + ".lean"
    obs = obligations(parse_script(dump_path))
    lines = [
        "-- Generated by Verify/LoopSource/gen_loopvc.py; do not edit.",
        "import Verify.LoopSource.CheckRaw",
        f"import {dump_mod}",
        "",
        "/-!",
        f"# {unit['name']}: solar-verify's obligations as Lean obligations, checked in the kernel",
        "",
        f"From `{manifest.split('/')[-1]}` (solar-verify {m.get('version', '?')}) and the script of the same run.",
        "Each Lean obligation keeps its manifest id; `check` shows the script gives it, `script_valid`",
        "is the script's verdict decided by the kernel (no solver), and `obs_valid` the two together.",
        "-/",
        "",
        f"namespace {ns}",
        "",
        "open SolidCore.Verify.VC",
        "",
        "set_option maxRecDepth 100000",
        "",
    ]
    names = []
    for q in unit["obligations"]:
        if q["role"] != "obligation":
            continue
        k = int(q["id"].split("#")[1])
        kind = KINDS[q["kind"]]
        e = obs[k]
        hs, phi = lean_obligation(e)
        nm = f"{kind}_{k}"
        names.append((nm, k))
        site = q.get("site", {})
        lines += [
            f"/-- {q['id']}: {q['kind']} ({site.get('file')}:{site.get('line')}); solver answer {q['answer']}. -/",
            f"def {nm} : Nat × List Tm × Tm := ({k}, [",
            ",\n".join("    " + lean(h) for h in hs) + "],",
            f"  {lean(phi)})",
            "",
        ]
    lines += [
        "/-- The required obligations, with their `check-sat` indices. -/",
        f"def obs : List (Nat × List Tm × Tm) := [{', '.join(n for n, _ in names)}]",
        "",
        "theorem check : checkLoop script obs = true := by decide +kernel",
        "",
    ]
    for j, (n, _) in enumerate(names):
        mem = "(List.Mem.head _)"
        for _ in range(j):
            mem = f"(List.Mem.tail _ {mem})"
        lines.append(f"theorem mem_{n} : {n} ∈ obs := {mem}")
    lines += [
        "",
        f"theorem obligation_count : (obligations script).length = {len(obs)} := by decide +kernel",
        "",
    ]
    for i in range(len(obs)):
        lines.append(f"theorem ob_{i} : dischargeAt script {i} = true := by decide +kernel")
    lines += [
        "",
        "/-- Every obligation of the script has no model: the verdict, decided by the kernel. -/",
        "theorem script_valid : Valid script :=",
        "  dischargeScript_of_each _ fun i hi =>",
        "    match i, obligation_count ▸ hi with",
    ]
    for i in range(len(obs)):
        lines.append(f"    | {i}, _ => ob_{i}")
    lines += [
        f"    | _ + {len(obs)}, h => absurd h (by omega)",
        "",
        "/-- The Lean obligations hold everywhere. -/",
        "theorem obs_valid : ObsValid (obs.map (·.2)) := checkLoop_sound check script_valid",
        "",
        f"/-- info: '{ns}.obs_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/",
        "#guard_msgs (whitespace := lax) in",
        "#print axioms obs_valid",
        "",
        f"end {ns}",
        "",
    ]
    open(out, "w").write("\n".join(lines))
    print(json.dumps({"out": out, "obligations": [n for n, _ in names], "check_sats": len(obs)}))


if __name__ == "__main__":
    main(sys.argv[1:])
