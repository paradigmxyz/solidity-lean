#!/usr/bin/env python3
"""Counterexamples to induction (CTIs) for loop-invariant candidates, classified as ICE samples.

    cti.py gen   PROBLEMS.json OUTDIR   find, classify and write the corpus
    cti.py check PROBLEMS.json OUTDIR   re-check every record of the corpus from its inputs alone

A problem is one loop as constrained Horn clauses over a single head predicate Inv (a chc file:
one entry clause, one back-edge clause, one or more exit clauses; anything else is refused as
unsupported). A candidate is a conjunction of formulas over the head variables, with an optional
decreasing measure. For every candidate this asks z3 for CTIs on each cutpoint edge:

  entry  (initiation)   entry(s')           and not I(s')                 s' is a POSITIVE
  back   (preservation) I(s), back(s, s')   and not I(s')                 (s, s') an IMPLICATION
  back   (decrease)     I(s), back(s, s')   and not (0 <= r(s), r(s') < r(s))   a RANK PAIR
  exit   (use)          I(s), exit(s)       and not goal(s)               s is a NEGATIVE

following ICE (Garg, Loeding, Madhusudan, Neider, CAV 2014): a positive is a state the loop
reaches, a negative a state from which the goal fails, and an implication pair says only that
s' must be in the invariant if s is. The pre-state of a back-edge CTI is never labelled negative.

Bounded replay unrolls the entry and back-edge clauses up to K steps from scratch:
  * a reached state that falsifies a conjunct is a positive and rejects the candidate;
  * an implication pair whose s is reached becomes a positive (its s' is reached one step later)
    and rejects the candidate;
  * a negative that is reached is a reachable violation of the goal (a bug in the source or the
    spec), not a fault of the candidate;
  * a state not reached within K is recorded as not-reached-within-k, which proves nothing.
A z3 unknown or timeout anywhere gives inconclusive, never inductive. inductive means only that
z3 found no CTI on any edge; the kernel discharge of the obligations is elsewhere.

A conjunct A => B (or (or (not A) B)) is checked for vacuity: whether A can hold at a head state
under the candidate, whether a state reached within K satisfies A, and whether the candidate
has a CTI with the conjunct replaced by B. One that passes only because A never holds is flagged.

No candidate is learned or strengthened here: the corpus is data for the existing Houdini, which
already drops candidates that fail initiation or preservation.
"""
import argparse
import hashlib
import json
import os
import sys

import z3

SCHEMA = "solidity-lean/cti/v1"
EDGES = ("entry", "back", "call", "exit")
OBLIGATIONS = {"entry": ("initiation", "use"), "back": ("preservation", "decrease", "use"), "exit": ("use",)}
LABELS = ("positive", "negative", "implication", "rank-pair", "inconclusive")
STATUSES = ("inductive", "not-inductive", "too-weak", "rejected", "goal-violated", "inconclusive")


class Unsupported(Exception):
    pass


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def solver(timeout_ms):
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.set("random_seed", 0)
    return s


def strip_commands(text):
    """Only declarations, definitions and assertions are read; z3's parser would run the rest."""
    skip = ("(set-logic", "(check-sat", "(get-model", "(exit", "(set-option", "(set-info")
    return "\n".join(l for l in text.splitlines() if not l.strip().startswith(skip))


def conjuncts(e):
    if z3.is_and(e):
        return [x for c in e.children() for x in conjuncts(c)]
    if z3.is_true(e):
        return []
    return [e]


def is_inv(e):
    return z3.is_app(e) and e.decl().name() == "Inv"


def has_inv(e):
    return is_inv(e) or (z3.is_app(e) and any(has_inv(c) for c in e.children()))


class Clause:
    """body ==> head, its universally bound variables made constants with a tag."""

    def __init__(self, f, tag, shared):
        self.consts = []
        body = f
        if z3.is_quantifier(f):
            if not f.is_forall():
                raise Unsupported("existential clause")
            n = f.num_vars()
            name = (lambda i: f.var_name(i)) if shared else (lambda i: f"{tag}!{f.var_name(i)}")
            self.consts = [z3.Const(name(i), f.var_sort(i)) for i in range(n)]
            body = z3.substitute_vars(f.body(), *reversed(self.consts))
        if z3.is_implies(body):
            ante, head = body.arg(0), body.arg(1)
        elif is_inv(body):
            ante, head = z3.BoolVal(True), body
        else:
            raise Unsupported(f"clause is not an implication: {body}")
        self.pre, self.rest = None, []
        for c in conjuncts(ante):
            if is_inv(c):
                if self.pre is not None:
                    raise Unsupported("nonlinear clause (two Inv in a body)")
                self.pre = list(c.children())
            elif has_inv(c):
                raise Unsupported(f"Inv under a connective: {c}")
            else:
                self.rest.append(c)
        if is_inv(head):
            self.post, self.goal = list(head.children()), None
        elif has_inv(head):
            raise Unsupported("Inv in a goal")
        else:
            self.post, self.goal = None, head
        if self.pre is None and self.post is None:
            raise Unsupported("clause without Inv")
        self.kind = "entry" if self.pre is None else ("back" if self.post is not None else "exit")

    def fresh(self, tag, keep=frozenset()):
        """A copy with fresh constants but those named in keep (for unrolling)."""
        sub = [(c, z3.Const(f"{tag}|{c}", c.sort())) for c in self.consts if str(c) not in keep]
        g = (lambda e: z3.substitute(e, *sub)) if sub else (lambda e: e)
        c = object.__new__(Clause)
        c.consts = [b for _, b in sub] + [x for x in self.consts if str(x) in keep]
        c.pre = [g(e) for e in self.pre] if self.pre is not None else None
        c.post = [g(e) for e in self.post] if self.post is not None else None
        c.goal = g(self.goal) if self.goal is not None else None
        c.rest = [g(e) for e in self.rest]
        c.kind = self.kind
        return c


class Problem:
    def __init__(self, spec, root):
        self.spec = spec
        self.id = spec["id"]
        self.path = os.path.join(root, spec["chc"])
        self.k = spec.get("k", 6)
        self.timeout = spec.get("timeout_ms", 10000)
        # shared: the clauses' variables are the constants of one solver transcript (solar-verify's
        # SSA names), so a name means the same value in every clause, and the constants the entry
        # clause binds (the state before the loop) are fixed for a whole run.
        self.shared = spec.get("shared", False)
        text = strip_commands(open(self.path).read())
        fs = list(z3.parse_smt2_string(text))
        self.clauses = [Clause(f, f"c{i}", self.shared) for i, f in enumerate(fs)]
        kinds = [c.kind for c in self.clauses]
        if kinds.count("entry") != 1 or kinds.count("back") != 1 or kinds.count("exit") < 1:
            raise Unsupported(f"want one entry, one back and some exit clauses, got {kinds}")
        self.entry = next(c for c in self.clauses if c.kind == "entry")
        self.back = next(c for c in self.clauses if c.kind == "back")
        self.exits = [c for c in self.clauses if c.kind == "exit"]
        self.query_edge = spec.get("query_edge", "exit")
        args = self.entry.post
        self.sorts = [a.sort() for a in args]
        self.names = spec.get("vars") or self.head_names()
        if len(self.names) != len(args):
            raise Unsupported(f"{len(args)} Inv arguments, {len(self.names)} names")
        self.vars = [z3.Const(n, s) for n, s in zip(self.names, self.sorts)]
        self.keep = frozenset(str(c) for c in self.entry.consts) if self.shared else frozenset()
        self.frame = [(a, self.resolve(a, how)) for a, how in sorted(spec.get("frame", {}).items())]
        self.decls = {n: v for n, v in zip(self.names, self.vars)}
        self.decls.update(dict(self.frame))

    def head_names(self):
        """The loop's variable names, from the back clause's head terms count@27 -> count."""
        out = []
        for a in self.back.pre:
            if not z3.is_const(a) or z3.is_int_value(a) or "@" not in str(a):
                raise Unsupported(f"head term {a} is not a transcript constant")
            out.append(str(a).split("@")[0])
        if len(set(out)) != len(out):
            raise Unsupported(f"head names collide: {out}")
        return out

    def resolve(self, alias, how):
        """A frame constant: entry:V is the entry clause's head term for variable V (its value
        before the loop); name:P the one entry constant named P@N."""
        if not self.shared:
            raise Unsupported("a frame needs shared constants")
        kind, _, what = how.partition(":")
        if kind == "entry":
            c = self.entry.post[self.names.index(what)]
        elif kind == "name":
            cs = [c for c in self.entry.consts if str(c).split("@")[0] == what]
            if len(cs) != 1:
                raise Unsupported(f"frame {alias}: {len(cs)} entry constants named {what}")
            c = cs[0]
        else:
            raise Unsupported(f"frame {alias}: {how}")
        if not (z3.is_const(c) and str(c) in self.keep):
            raise Unsupported(f"frame {alias}: {c} is not an entry constant")
        return c

    # formulas over the head variables
    def formula(self, text):
        if text.startswith("spacer:"):
            return self.spacer(text[len("spacer:"):])
        return z3.parse_smt2_string(f"(assert {text})", decls=self.decls)[0]

    def term(self, text):
        f = z3.parse_smt2_string(f"(declare-const |r!| Int)(assert (= |r!| {text}))", decls=self.decls)[0]
        return f.arg(1)

    def spacer(self, rel):
        out = open(os.path.join(os.path.dirname(self.path), rel)).read()
        i = out.index("(define-fun")
        depth, j = 0, i
        while True:
            depth += {"(": 1, ")": -1}.get(out[j], 0)
            j += 1
            if depth == 0:
                break
        app = "(Inv " + " ".join(f"|{n}|" for n in self.names) + ")"
        return z3.parse_smt2_string(out[i:j] + f"(assert {app})", decls=self.decls)[0]

    def at(self, e, args):
        return z3.substitute(e, *zip(self.vars, args))

    def close(self, e, st):
        """e at the concrete state st (head variables and frame)."""
        fr = [(c, read(st[a], c.sort())) for a, c in self.frame]
        return z3.substitute(e, *zip(self.vars, self.const(st)), *fr)

    def observed(self, args):
        return list(args) + [c for _, c in self.frame]

    # concrete states: the head variables, then the frame by alias
    def state(self, m, args):
        st = {n: show(m.eval(a, model_completion=True)) for n, a in zip(self.names, args)}
        st.update({a: show(m.eval(c, model_completion=True)) for a, c in self.frame})
        return st

    def const(self, st):
        return [read(st[n], s) for n, s in zip(self.names, self.sorts)]

    def eq(self, args, st):
        fr = [c == read(st[a], c.sort()) for a, c in self.frame]
        return z3.And([a == v for a, v in zip(args, self.const(st))] + fr)

    # bounded replay
    def unroll(self, k, target, want_model=False):
        """The least depth d <= k at which a state reached from an entry state satisfies
        target(xs): ('reached', trace) | ('not-reached-within-k', None) | ('inconclusive', why);
        with want_model, a third item: the model (or None)."""
        r = self._unroll(k, target)
        return r if want_model else r[:2]

    def _unroll(self, k, target):
        s = solver(self.timeout)
        xs = [[z3.Const(f"x{j}|{n}", srt) for n, srt in zip(self.names, self.sorts)] for j in range(k + 1)]
        e = self.entry.fresh("u0", self.keep)
        s.add(*e.rest)
        s.add(*[a == b for a, b in zip(xs[0], e.post)])
        for d in range(k + 1):
            if d > 0:
                b = self.back.fresh(f"u{d}", self.keep)
                s.add(*b.rest)
                s.add(*[a == p for a, p in zip(xs[d - 1], b.pre)])
                s.add(*[a == p for a, p in zip(xs[d], b.post)])
            s.push()
            s.add(target(xs[d]))
            r = s.check()
            if r == z3.sat:
                m = s.model()
                return "reached", [self.state(m, xs[j]) for j in range(d + 1)], m
            why = s.reason_unknown() if r == z3.unknown else None
            s.pop()
            if r == z3.unknown:
                return "inconclusive", why, None
        return "not-reached-within-k", None, None

    def reach_step(self, clause, viol):
        """Bounded replay of a whole edge: the least-depth reached head state from which clause
        has an instance X with viol(X). Returns (result, trace, X's post state or None)."""
        made = []

        def target(xs):
            X = clause.fresh(f"t{len(made)}", self.keep)
            made.append(X)
            return z3.And(*[a == b for a, b in zip(X.pre, xs)], *X.rest, viol(X))

        res, tr, m = self.unroll(self.k, target, want_model=True)
        if res != "reached":
            return res, tr, None
        X = made[-1]
        return res, tr, (self.state(m, X.post) if X.post is not None else None)


def show(v):
    if z3.is_int_value(v) or z3.is_bv_value(v):
        return str(v.as_long())
    if z3.is_true(v):
        return "true"
    if z3.is_false(v):
        return "false"
    raise Unsupported(f"value {v}")


def read(text, sort):
    if sort == z3.IntSort():
        return z3.IntVal(int(text))
    if sort == z3.BoolSort():
        return z3.BoolVal(text == "true")
    if z3.is_bv_sort(sort):
        return z3.BitVecVal(int(text), sort.size())
    raise Unsupported(f"sort {sort}")


def guard_parts(c):
    if z3.is_implies(c):
        return c.arg(0), c.arg(1)
    if z3.is_or(c) and c.num_args() == 2 and z3.is_not(c.arg(0)):
        return c.arg(0).arg(0), c.arg(1)
    return None


SMALL = 1 << 8


def small(p, args):
    return z3.And([z3.And(a >= -SMALL, a <= SMALL) for a in args if a.sort() == z3.IntSort()])


def find(p, build, args_of, limit):
    """Up to limit models of build() that differ on args_of(), small values first."""
    out, seen = [], []
    s = solver(p.timeout)
    s.add(build())
    for prefer_small in (True, False):
        while len(out) < limit:
            s.push()
            for key in seen:
                s.add(z3.Not(z3.And([a == v for a, v in zip(args_of(), key)])))
            if prefer_small:
                s.add(small(p, args_of()))
            r = s.check()
            if r != z3.sat:
                why = s.reason_unknown() if r == z3.unknown else None
                s.pop()
                if r == z3.unknown:
                    return out, why
                break
            m = s.model()
            seen.append([m.eval(a, model_completion=True) for a in args_of()])
            out.append(m)
            s.pop()
    return out, None


def replay_none(p, res, why):
    if res == "inconclusive":
        return {"result": "inconclusive", "k": p.k, "reason": str(why)}
    return {"result": "not-reached-within-k", "k": p.k}


def edge_ctis(p, inv, measure, limit):
    """CTI records of candidate inv (a conjunction) on every edge. On each edge, bounded replay
    first looks for a CTI whose pre-state a run reaches; then z3 is asked for any CTI."""
    recs, unk = [], []
    E, B = p.entry, p.back

    def first(clause, viol, edge, ob, **kw):
        res, tr, post = p.reach_step(clause, viol)
        if res == "inconclusive":
            unk.append((edge, ob, tr))
        elif res == "reached":
            r = dict(edge=edge, obligation=ob, s=tr[-1], s_prime=post, by="replay", **kw)
            return r, tr
        return None, None
    # entry: a positive (an entry state is reached by definition)
    ms, why = find(p, lambda: z3.And(*E.rest, z3.Not(p.at(inv, E.post))), lambda: p.observed(E.post), limit)
    if why:
        unk.append(("entry", "initiation", why))
    for m in ms:
        s1 = p.state(m, E.post)
        recs.append(dict(edge="entry", obligation="initiation", s=None, s_prime=s1, label="positive",
                         replay={"result": "reached", "depth": 0, "trace": [s1]}))
    # back: implication pairs, made positives when their pre-state is reached
    r, tr = first(B, lambda X: z3.And(p.at(inv, X.pre), z3.Not(p.at(inv, X.post))), "back", "preservation")
    if r:
        r.update(label="positive", replay={"result": "reached", "depth": len(tr), "trace": tr + [r["s_prime"]]})
        recs.append(r)
    ms, why = find(p, lambda: z3.And(p.at(inv, B.pre), *B.rest, z3.Not(p.at(inv, B.post))),
                   lambda: p.observed(B.pre + B.post), limit)
    if why:
        unk.append(("back", "preservation", why))
    for m in ms:
        s0, s1 = p.state(m, B.pre), p.state(m, B.post)
        if any(x["s"] == s0 and x["s_prime"] == s1 for x in recs):
            continue
        res, tr = p.unroll(p.k, lambda xs: p.eq(xs, s0))
        rec = dict(edge="back", obligation="preservation", s=s0, s_prime=s1)
        if res == "reached":
            rec.update(label="positive", replay={"result": "reached", "depth": len(tr), "trace": tr + [s1]})
        else:
            rec.update(label="implication", replay=replay_none(p, res, tr))
        recs.append(rec)
    # back: the measure
    if measure is not None:
        r0, r1 = p.at(measure, B.pre), p.at(measure, B.post)
        dec = lambda X: z3.Not(z3.And(p.at(measure, X.pre) >= 0, p.at(measure, X.post) < p.at(measure, X.pre)))
        r, tr = first(B, lambda X: z3.And(p.at(inv, X.pre), dec(X)), "back", "decrease")
        if r:
            r.update(label="rank-pair", replay={"result": "reached", "depth": len(tr), "trace": tr + [r["s_prime"]]},
                     lasso=r["s"] == r["s_prime"],
                     measure=[show(z3.simplify(p.close(measure, x))) for x in (r["s"], r["s_prime"])])
            recs.append(r)
        ms, why = find(p, lambda: z3.And(p.at(inv, B.pre), *B.rest, z3.Not(z3.And(r0 >= 0, r1 < r0))),
                       lambda: p.observed(B.pre + B.post), limit)
        if why:
            unk.append(("back", "decrease", why))
        for m in ms:
            s0, s1 = p.state(m, B.pre), p.state(m, B.post)
            if any(x["s"] == s0 and x["s_prime"] == s1 for x in recs):
                continue
            res, tr = p.unroll(p.k, lambda xs: p.eq(xs, s0))
            rec = dict(edge="back", obligation="decrease", s=s0, s_prime=s1, label="rank-pair",
                       measure=[show(m.eval(r0, model_completion=True)), show(m.eval(r1, model_completion=True))])
            if res == "reached":
                rec["replay"] = {"result": "reached", "depth": len(tr), "trace": tr + [s1]}
                rec["lasso"] = s0 == s1
            else:
                rec["replay"] = replay_none(p, res, tr)
            recs.append(rec)
    # exit: negatives (states from which the goal fails)
    for xi, X in enumerate(p.exits):
        r, tr = first(X, lambda Y: z3.And(p.at(inv, Y.pre), z3.Not(Y.goal)), p.query_edge, "use", exit=xi)
        if r:
            r.update(label="negative", s_prime=None, replay={"result": "reached", "depth": len(tr) - 1, "trace": tr})
            recs.append(r)
        ms, why = find(p, lambda: z3.And(p.at(inv, X.pre), *X.rest, z3.Not(X.goal)), lambda: p.observed(X.pre), limit)
        if why:
            unk.append((p.query_edge, "use", why))
        for m in ms:
            s0 = p.state(m, X.pre)
            if any(x["obligation"] == "use" and x.get("exit") == xi and x["s"] == s0 for x in recs):
                continue
            res, tr = p.unroll(p.k, lambda xs: p.eq(xs, s0))
            rec = dict(edge=p.query_edge, obligation="use", exit=xi, s=s0, s_prime=None, label="negative")
            rec["replay"] = ({"result": "reached", "depth": len(tr) - 1, "trace": tr}
                             if res == "reached" else replay_none(p, res, tr))
            recs.append(rec)
    for edge, ob, why in unk:
        recs.append(dict(edge=edge, obligation=ob, s=None, s_prime=None, label="inconclusive", reason=str(why)))
    return recs


def status_of(recs):
    rs = [r for r in recs if r["obligation"] != "decrease"]
    if any(r["label"] == "inconclusive" for r in rs):
        return "inconclusive"
    if any(r["label"] == "positive" for r in rs):
        return "rejected"
    if any(r["label"] == "negative" and r["replay"]["result"] == "reached" for r in rs):
        return "goal-violated"
    if any(r["label"] == "implication" for r in rs):
        return "not-inductive"
    if any(r["label"] == "negative" for r in rs):
        return "too-weak"
    return "inductive"


def rank_status(recs, has_measure):
    if not has_measure:
        return "none"
    rk = [r for r in recs if r["obligation"] == "decrease"]
    if any(r["label"] == "inconclusive" for r in rk):
        return "inconclusive"
    if any(r.get("lasso") for r in rk):
        return "nonterminating"
    if any(r["replay"]["result"] == "reached" for r in rk):
        return "rejected"
    if rk:
        return "not-proved"
    return "decreases"


def has_cti(recs):
    return any(r["label"] in ("positive", "implication", "negative") for r in recs)


def has_induction_cti(recs):
    """A CTI of initiation or preservation (what a guard can hide), not of the goal."""
    return any(r["label"] in ("positive", "implication") for r in recs)


def vacuity(p, inv, conj, cti):
    """Flags for an edge the candidate makes vacuous and for guarded conjuncts."""
    flags = []
    s = solver(p.timeout)
    s.add(p.at(inv, p.back.pre), *p.back.rest)
    if s.check() == z3.unsat:
        flags.append({"flag": "vacuous-back-edge"})
    for i, c in enumerate(conj):
        g = guard_parts(c)
        if g is None:
            continue
        a, b = g
        s = solver(p.timeout)
        s.add(inv, a)
        under = s.check()
        res, _ = p.unroll(p.k, lambda xs: p.at(a, xs))
        alone = z3.And(*([x for j, x in enumerate(conj) if j != i] + [b]))
        alone_recs = edge_ctis(p, alone, None, 1)
        f = {"flag": "guarded", "conjunct": i, "antecedent_under_candidate": str(under),
             "antecedent_reached_within_k": res, "unguarded_status": status_of(alone_recs)}
        if has_induction_cti(alone_recs) and not cti and (under == z3.unsat or res != "reached"):
            f["flag"] = "passes-only-because-antecedent-false"
        flags.append(f)
    return flags


def run_problem(spec, root):
    try:
        p = Problem(spec, root)
    except Unsupported as e:
        return [{"kind": "problem", "id": spec["id"], "status": "unsupported", "reason": str(e)}]
    out = [{"kind": "problem", "schema": SCHEMA, "id": p.id, "chc": spec["chc"], "chc_sha256": sha256(p.path),
            "origin": spec["origin"], "vars": p.names, "frame": spec.get("frame", {}), "shared": p.shared,
            "query_edge": p.query_edge, "k": p.k, "z3": z3.get_version_string(), "source": spec.get("source"),
            "mutation": spec.get("mutation"), "outcome": spec.get("outcome", "normal"), "note": spec.get("note", "")}]
    for cand in spec["candidates"]:
        cid = f"{p.id}/{cand['id']}"
        conj = [p.formula(t) for t in cand["conjuncts"]]
        inv = z3.And(*conj) if conj else z3.BoolVal(True)
        measure = p.term(cand["decreases"]) if cand.get("decreases") else None
        recs = edge_ctis(p, inv, measure, spec.get("per_edge", 2))
        # bounded replay of each conjunct: a reached state that falsifies it
        for i, c in enumerate(conj):
            res, tr = p.unroll(p.k, lambda xs: z3.Not(p.at(c, xs)))
            if res == "inconclusive":
                recs.append(dict(edge="back", obligation="preservation", s=None, s_prime=None,
                                 label="inconclusive", reason=f"replay of conjunct {i}: {tr}"))
            elif res == "reached" and not any(r["label"] == "positive" and r["s_prime"] == tr[-1] for r in recs):
                d = len(tr) - 1
                recs.append(dict(edge="entry" if d == 0 else "back",
                                 obligation="initiation" if d == 0 else "preservation",
                                 s=None if d == 0 else tr[-2], s_prime=tr[-1], label="positive",
                                 replay={"result": "reached", "depth": d, "trace": tr}, by="replay"))
        for r in recs:
            if r["label"] in ("positive", "implication"):
                r["falsified"] = [i for i, c in enumerate(conj) if z3.is_false(z3.simplify(p.close(c, r["s_prime"])))]
        out.append({"kind": "candidate", "id": cid, "conjuncts": cand["conjuncts"],
                    "decreases": cand.get("decreases"), "expect": cand.get("expect"),
                    "expect_rank": cand.get("expect_rank"), "expect_flag": cand.get("expect_flag"),
                    "source": cand.get("source"), "note": cand.get("note", ""),
                    "status": status_of(recs), "rank": rank_status(recs, measure is not None),
                    "flags": vacuity(p, inv, conj, has_induction_cti(recs)),
                    "ctis": sum(1 for r in recs if r["label"] != "inconclusive")})
        for n, r in enumerate(recs):
            out.append({"kind": "cti", "id": f"{cid}#{n}", "candidate": cid, **r,
                        "source": {"loop": spec.get("source"), "candidate": cand.get("source")}})
    return out


def dump(rec):
    return json.dumps(rec, sort_keys=True, separators=(",", ":"))


# checking a corpus from its inputs alone

def holds(p, e):
    v = z3.simplify(e)
    if z3.is_true(v) or z3.is_false(v):
        return z3.is_true(v)
    s = solver(p.timeout)
    s.add(z3.Not(e))
    return s.check() == z3.unsat


def edge_sat(p, cl, s0, s1):
    """Is there a run of clause cl from s0 to s1 (its other variables existential)?
    For an exit clause: one on which the goal fails."""
    s = solver(p.timeout)
    s.add(*cl.rest)
    if cl.pre is not None:
        s.add(p.eq(cl.pre, s0))
    if cl.post is not None:
        s.add(p.eq(cl.post, s1))
    if cl.goal is not None:
        s.add(z3.Not(cl.goal))
    return s.check()


def check_trace(p, tr):
    if edge_sat(p, p.entry, None, tr[0]) != z3.sat:
        return "trace[0] is not an entry state"
    for j in range(1, len(tr)):
        if edge_sat(p, p.back, tr[j - 1], tr[j]) != z3.sat:
            return f"trace step {j} is not a back edge"
    return None


def check_record(p, r, cand):
    if cand is None:
        return "no candidate record"
    if r["edge"] not in EDGES or r["obligation"] not in OBLIGATIONS.get(r["edge"], ()):
        return f"bad edge/obligation {r['edge']}/{r['obligation']}"
    if r["label"] not in LABELS:
        return f"bad label {r['label']}"
    if r["label"] == "inconclusive":
        return None
    conj = [p.formula(t) for t in cand["conjuncts"]]
    inv = z3.And(*conj) if conj else z3.BoolVal(True)
    I = lambda st: holds(p, p.close(inv, st))
    lab, ob = r["label"], r["obligation"]
    # ICE: a negative comes only from an exit edge; a back-edge pre-state is never one.
    if lab == "negative" and ob != "use":
        return "negative label off a use (goal) obligation"
    if lab == "implication" and ob != "preservation":
        return "implication off a back edge"
    if lab == "rank-pair" and ob != "decrease":
        return "rank pair off a decrease obligation"
    if ob == "initiation":
        if r["s_prime"] is None or edge_sat(p, p.entry, None, r["s_prime"]) != z3.sat:
            return "s' is not an entry state"
        if I(r["s_prime"]):
            return "candidate holds at s'"
    elif ob in ("preservation", "decrease"):
        if edge_sat(p, p.back, r["s"], r["s_prime"]) != z3.sat:
            return "(s, s') is not a back edge"
        if not I(r["s"]):
            return "candidate fails at s"
        if ob == "preservation" and I(r["s_prime"]):
            return "candidate holds at s'"
        if ob == "decrease":
            meas = p.term(cand["decreases"])
            r0, r1 = (p.close(meas, x) for x in (r["s"], r["s_prime"]))
            if holds(p, z3.And(r0 >= 0, r1 < r0)):
                return "measure decreases on (s, s')"
    elif ob == "use":
        if not I(r["s"]):
            return "candidate fails at s"
        if edge_sat(p, p.exits[r["exit"]], r["s"], None) != z3.sat:
            return "goal holds on every exit from s"
    rp = r["replay"]
    if rp["result"] == "reached":
        tr = rp["trace"]
        e = check_trace(p, tr)
        if e:
            return e
        if lab == "positive":
            if tr[-1] != r["s_prime"] or I(tr[-1]):
                return "positive's trace does not end at a state falsifying the candidate"
            if ob == "preservation" and len(tr) > 1 and r.get("s") is not None and tr[-2] != r["s"]:
                return "positive's trace does not pass through s"
        elif lab == "negative":
            if tr[-1] != r["s"]:
                return "trace does not reach s"
        elif lab == "rank-pair":
            if tr[-2:] != [r["s"], r["s_prime"]]:
                return "trace does not take (s, s')"
            if r.get("lasso") != (r["s"] == r["s_prime"]):
                return "lasso flag wrong"
        else:
            return "an implication whose pre-state was reached must be a positive"
    elif rp["result"] in ("not-reached-within-k", "inconclusive"):
        if lab == "positive":
            return "positive without a trace"
    else:
        return f"bad replay {rp['result']}"
    return None


def check(problems, outdir, root):
    errors = []
    for spec in problems:
        path = os.path.join(outdir, spec["id"] + ".jsonl")
        if not os.path.exists(path):
            errors.append(f"{spec['id']}: no corpus file")
            continue
        recs = [json.loads(l) for l in open(path)]
        if recs[0].get("status") == "unsupported":
            if spec.get("expect") != "unsupported":
                errors.append(f"{spec['id']}: unsupported: {recs[0]['reason']}")
            continue
        p = Problem(spec, root)
        if recs[0]["chc_sha256"] != sha256(p.path):
            errors.append(f"{spec['id']}: chc hash differs")
        cands = {r["id"]: r for r in recs if r["kind"] == "candidate"}
        if set(cands) != {f"{p.id}/{c['id']}" for c in spec["candidates"]}:
            errors.append(f"{spec['id']}: candidates differ from the problem file")
        for r in recs:
            if r["kind"] == "cti":
                e = check_record(p, r, cands.get(r["candidate"]))
                if e:
                    errors.append(f"{r['id']}: {e}")
        for c in cands.values():
            ctis = [r for r in recs if r["kind"] == "cti" and r["candidate"] == c["id"]]
            if c["status"] not in STATUSES or status_of(ctis) != c["status"]:
                errors.append(f"{c['id']}: status {c['status']} does not follow from its records")
            if rank_status(ctis, bool(c.get("decreases"))) != c["rank"]:
                errors.append(f"{c['id']}: rank {c['rank']} does not follow from its records")
            if c["status"] == "inductive" and has_cti(ctis):
                errors.append(f"{c['id']}: inductive with a CTI")
            for key, got in (("expect", c["status"]), ("expect_rank", c["rank"])):
                if c.get(key) and c[key] != got:
                    errors.append(f"{c['id']}: {key} {c[key]}, got {got}")
            if c.get("expect_flag") and c["expect_flag"] not in {f["flag"] for f in c["flags"]}:
                errors.append(f"{c['id']}: expected flag {c['expect_flag']}")
    return errors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["gen", "check"])
    ap.add_argument("problems")
    ap.add_argument("outdir")
    ap.add_argument("--only")
    a = ap.parse_args()
    root = os.path.dirname(os.path.abspath(a.problems))
    problems = json.load(open(a.problems))["problems"]
    if a.only:
        problems = [p for p in problems if p["id"] == a.only]
    if a.cmd == "gen":
        os.makedirs(a.outdir, exist_ok=True)
        rows = []
        for spec in problems:
            recs = run_problem(spec, root)
            with open(os.path.join(a.outdir, spec["id"] + ".jsonl"), "w") as f:
                for r in recs:
                    f.write(dump(r) + "\n")
            for r in recs:
                if r["kind"] == "candidate":
                    fl = ",".join(sorted({x["flag"] for x in r["flags"]})) or "-"
                    rows.append(f"{r['id']}\t{r['status']}\t{r['rank']}\t{r['ctis']}\t{fl}")
                elif r["kind"] == "problem" and r.get("status") == "unsupported":
                    rows.append(f"{r['id']}\tunsupported\t-\t0\t{r['reason']}")
                else:
                    continue
                print(rows[-1], flush=True)
        if not a.only:
            with open(os.path.join(a.outdir, "SUMMARY.tsv"), "w") as f:
                f.write("candidate\tstatus\trank\tctis\tflags\n" + "\n".join(rows) + "\n")
    else:
        errs = check(problems, a.outdir, root)
        for e in errs:
            print("FAIL", e)
        print(f"{'FAIL' if errs else 'OK'}: {len(errs)} error(s)")
        sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()
