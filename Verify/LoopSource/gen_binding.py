#!/usr/bin/env python3
"""Writes the body binding of Counter.bump's loop (Contracts/VerifyCounter/LoopBinding.lean) from a
certify-invariants file, through the generic source loop bridge (SolidCore/Refinement/Generic/
LoopErased.lean: ForObl, forLoop_of_erased).

    gen_binding.py INVARIANTS OUT.lean          write the module
    gen_binding.py INVARIANTS OUT.lean --check  exit 1 unless OUT.lean is what INVARIANTS gives

INVARIANTS is format certify-invariants, version 1, with one entry for "Counter.bump":
{"function": "Counter.bump", "line": L, "invariants": [...], "decreases": "..."}. The supplied
expressions are solar-verify's spec language over the loop's header words, which this binding names
from bump's header (SourceLoop.headerS): n (argument 0), i (argument 1), count (slot 0, argument 2)
and old(count) (the call's slot 0). Invariants may use + and comparisons; the measure may use + and
- (natural subtraction). Nothing supplied is trusted: the module's proofs check the obligations
(initiation, exit, preservation and the measure's fall) in the kernel, and a candidate for which one
is false does not build.

Exit 0 written; 3 BLOCKED (no invariant, no decreases, an unknown name, an unsupported operator):
nothing written; 1 any other error.
"""
import json, os, re, sys

def die(msg, code=1):
    print(f"gen_binding: {'BLOCKED: ' if code == 3 else 'error: '}{msg}", file=sys.stderr)
    sys.exit(code)

TOK = re.compile(r"\s*(old\(count\)|[A-Za-z_][A-Za-z_0-9]*|\d+|==|<=|>=|&&|[-+()<>])")

def translate(expr, names, allow_minus):
    out, pos = [], 0
    expr = expr.strip()
    while pos < len(expr):
        m = TOK.match(expr, pos)
        if not m:
            die(f"cannot read {expr!r} at {expr[pos:]!r}", 3)
        t = m.group(1)
        pos = m.end()
        if t in names:
            if names[t] is None:
                die(f"{t} is not available in {expr!r}", 3)
            out.append(names[t])
        elif t.isdigit() or t in ("+", "(", ")", "<", ">"):
            out.append(t)
        elif t == "-":
            if not allow_minus:
                die(f"subtraction in an invariant ({expr!r}) is not supported: Solidity's checked - is not Nat's", 3)
            out.append("-")
        elif t in ("==", "<=", ">=", "&&"):
            out.append({"==": "=", "<=": "≤", ">=": "≥", "&&": "∧"}[t])
        else:
            die(f"unknown name {t!r} in {expr!r} (bump's header has n, i, count, old(count))", 3)
    return " ".join(out)

P_NAMES = {"n": "(nOf ρ)", "i": "i", "count": "cnt", "old(count)": "(ρ.store 0)"}
M_NAMES = {"n": "((WExpr.arg 0).eval σ)", "i": "((WExpr.arg 1).eval σ)",
           "count": "((WExpr.arg 2).eval σ)", "old(count)": None}

def main():
    a = sys.argv[1:]
    check = "--check" in a
    a = [x for x in a if x != "--check"]
    if len(a) != 2:
        die("usage: gen_binding.py INVARIANTS OUT.lean [--check]")
    spec = json.load(open(a[0]))
    if spec.get("format") != "certify-invariants" or spec.get("version") != 1:
        die(f"{a[0]} is not certify-invariants version 1")
    loops = [l for l in spec.get("loops", []) if l.get("function") == "Counter.bump"]
    if len(loops) != 1:
        die(f"{a[0]} has {len(loops)} entries for Counter.bump, not one")
    lp = loops[0]
    invs = lp.get("invariants") or []
    if not invs:
        die("no invariant for Counter.bump: nothing to cut the loop at", 3)
    dec = lp.get("decreases")
    if not dec:
        die("no decreases for Counter.bump: the loop has no measure, so it has no ForObl and no termination proof", 3)
    inv = " ∧ ".join(f"({translate(e, P_NAMES, False)})" for e in invs)
    meas = translate(dec, M_NAMES, True)
    spec_lines = "\n".join(f"  invariant `{e}`" for e in invs) + f"\n  decreases `{dec}`"
    here = os.path.dirname(os.path.abspath(__file__))
    template = open(os.path.join(here, "LoopBinding.lean.in")).read()
    text = (template.replace("@INV@", inv).replace("@MEAS@", meas).replace("@SPEC@", spec_lines)
            .replace("@SRC@", os.path.basename(a[0])))
    if check:
        if open(a[1]).read() != text:
            die(f"{a[1]} is not what {a[0]} gives")
        return
    open(a[1], "w").write(text)

if __name__ == "__main__":
    main()
