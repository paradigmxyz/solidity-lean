#!/usr/bin/env python3
"""Mechanical translations from SMT-LIB into Lean. Nothing is simplified or edited.

  smt2lean_inv.py MODEL NAME
      A z3 Spacer model (define-fun Inv ...) as a shallow Lean 4 def: each SMT-LIB operator maps
      1:1 to a Lean operator, let stays let.

  smt2lean_inv.py loopvc --interface META.json [--candidate CAND.json | --spacer MODEL]
                         --root ROOT --out DIR
      A loop's exported Horn view (META.json names it; one clause per cutpoint edge) and a
      candidate invariant per cutpoint, as the exact obligations of initiation, preservation,
      termination, exit and outcome, written as a solar-verify-lean (version 2) export that
      Verify/Discharge/discharge.sh checks like any other. See loopvc/README.md.

  smt2lean_inv.py cti DIR
      After discharge.sh ran on DIR: for each required obligation it did not prove, asks z3 for a
      model of the query and writes DIR/discharge/cti.json (the candidate, the edge, its location
      and the cutpoint state before and after the edge) and DIR/discharge/residual/<id>.lean (the
      exact goal left open). A model is a counterexample to induction, not a reachable failure.
"""
import hashlib, json, os, re, subprocess, sys

# ---------------------------------------------------------------------------- s-expressions

TOKEN = re.compile(r';[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|;"]+')

def tokenize(s):
    return [t for t in TOKEN.findall(s) if not t.startswith(';')]

def parse(toks, i=0):
    if toks[i] == '(':
        out = []; i += 1
        while toks[i] != ')':
            x, i = parse(toks, i); out.append(x)
        return out, i + 1
    return toks[i], i + 1

def parse_all(text):
    toks = tokenize(text)
    out, i = [], 0
    while i < len(toks):
        x, i = parse(toks, i); out.append(x)
    return out

def show(e):
    if isinstance(e, str):
        return e
    return '(' + ' '.join(show(x) for x in e) + ')'

def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()

def sha256_file(p):
    with open(p, 'rb') as f:
        return sha256_bytes(f.read())

# ---------------------------------------------------------------------- Spacer model -> Lean

def ident(x):
    return x.replace('!', '_')

def is_bool(v):
    return isinstance(v, list) and v[0] in ('not', 'and', 'or', '=>', '<=', '>=', '<', '>', '=')

def lean(e):
    if isinstance(e, str):
        if re.fullmatch(r'\d+', e): return '(' + e + ' : Int)'
        if e == 'true': return 'True'
        if e == 'false': return 'False'
        return ident(e)
    op, *args = e
    if op == 'let':
        binds, body = args
        s = lean(body)
        for name, val in reversed(binds):
            ty = 'Prop' if is_bool(val) else 'Int'
            s = '(let ' + ident(name) + ' : ' + ty + ' := ' + lean(val) + '; ' + s + ')'
        return s
    a = [lean(x) for x in args]
    if op == 'not': return '(¬ ' + a[0] + ')'
    if op == 'and': return '(' + ' ∧ '.join(a) + ')' if a else 'True'
    if op == 'or': return '(' + ' ∨ '.join(a) + ')' if a else 'False'
    if op == '=>': return '(' + a[0] + ' → ' + a[1] + ')'
    if op == '-' and len(a) == 1: return '(-' + a[0] + ')'
    if op in ('+', '-', '*'): return '(' + (' ' + op + ' ').join(a) + ')'
    if op in ('<=', '>=', '<', '>'):
        m = {'<=': '≤', '>=': '≥', '<': '<', '>': '>'}[op]
        return '(' + a[0] + ' ' + m + ' ' + a[1] + ')'
    if op == '=': return '(' + a[0] + ' = ' + a[1] + ')'
    if op == 'ite': return '(if ' + a[0] + ' then ' + a[1] + ' else ' + a[2] + ')'
    raise SystemExit('unsupported operator: ' + op)

def model_main(path, name):
    text = open(path).read()
    d, _ = parse(tokenize(text[text.index('(define-fun'):]))
    _, fname, params, ret, body = d
    binders = ' '.join('(' + ident(p) + ' : Int)' for p, _t in params)
    print('/-- Verbatim from ' + path + ' (z3 Spacer model for ' + fname + '). -/')
    print('def ' + name + ' ' + binders + ' : Prop :=')
    print('  ' + lean(body))

# ----------------------------------------------- SMT-LIB -> solar-verify's deep embedding
# The translation of solar's crates/verify/src/lean.rs (Scope::term, sort, command), so that an
# obligation written here reads exactly as one solar-verify --emit-lean writes.

class Unsupported(Exception):
    pass

OPS = {
    'not': 'not', 'and': 'and', 'or': 'or', 'xor': 'xor', '=>': 'implies', '=': 'eq',
    'distinct': 'distinct', 'ite': 'ite', '+': 'add', '-': 'sub', '*': 'mul', 'div': 'div',
    'mod': 'mod', 'abs': 'abs', '<': 'lt', '<=': 'le', '>': 'gt', '>=': 'ge',
    'select': 'select', 'store': 'store', 'bv2nat': 'bv2nat', 'bv2int': 'bv2nat',
}
for _o in ('bvadd bvsub bvmul bvudiv bvurem bvsdiv bvsrem bvsmod bvneg bvand bvor bvxor bvnot '
           'bvshl bvlshr bvashr bvult bvule bvugt bvuge bvslt bvsle bvsgt bvsge concat').split():
    OPS[_o] = _o

def sort_lean(s):
    if s == 'Bool': return '.bool'
    if s == 'Int': return '.int'
    if isinstance(s, list) and len(s) == 3 and s[0] == '_' and s[1] == 'BitVec':
        return '(.bv %d)' % int(s[2])
    if isinstance(s, list) and len(s) == 3 and s[0] == 'Array':
        return '(.array %s %s)' % (sort_lean(s[1]), sort_lean(s[2]))
    raise Unsupported("unsupported sort '%s'" % show(s))

def lean_string(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

class Scope:
    def __init__(self):
        self.decls = []          # (name, [arg sorts], ret sort)
        self.by_name = {}

    def declare(self, name, args, ret):
        if name in self.by_name or name in OPS:
            raise Unsupported("symbol '%s' declared twice" % name)
        self.decls.append((name, args, ret))
        self.by_name[name] = len(self.decls) - 1
        return len(self.decls) - 1

    def term(self, t, bound):
        if isinstance(t, str):
            return self.atom(t, bound)
        if not t:
            raise Unsupported('empty application')
        head, args = t[0], t[1:]
        if isinstance(head, list):
            return self.indexed(head, args, bound, t)
        if head == '_':
            if len(args) == 2 and args[0].startswith('bv') and args[0][2:].isdigit():
                return '.bv %d %d' % (int(args[1]), int(args[0][2:]))
            raise Unsupported("unsupported literal '%s'" % show(t))
        if head == '!':
            body, attrs = args[0], args[1:]
            if any(k not in (':pattern', ':weight', ':qid', ':skolemid', ':named') for k in attrs[::2]):
                raise Unsupported("unsupported attribute in '%s'" % show(t))
            return self.term(body, bound)
        if head in ('forall', 'exists'):
            vars_, body = args
            sorts = []
            n = len(bound)
            for v in vars_:
                x, s = v
                sorts.append(sort_lean(s))
                bound.append(x)
            try:
                b = self.term(body, bound)
            finally:
                del bound[n:]
            return '.%s [%s] (%s)' % ('«forall»' if head == 'forall' else '«exists»', ', '.join(sorts), b)
        if head == 'let':
            raise Unsupported("unsupported 'let'")
        a = ', '.join(self.term(x, bound) for x in args)
        if head in bound:
            raise Unsupported("bound variable '%s' applied to arguments" % head)
        if head in OPS:
            return '.app .%s [%s]' % (OPS[head], a)
        if head in self.by_name:
            return '.fn %d [%s]' % (self.by_name[head], a)
        raise Unsupported("unsupported operator '%s'" % head)

    def atom(self, a, bound):
        for i, b in enumerate(reversed(bound)):
            if b == a:
                return '.var %d' % i
        if a in ('true', 'false'):
            return '.bool ' + a
        if a.isdigit():
            if len(a) > 1 and a.startswith('0'):
                raise Unsupported("bad numeral '%s'" % a)
            return '.int ' + a
        if a.startswith('#x'):
            return '.bv %d %d' % (4 * (len(a) - 2), int(a[2:], 16))
        if a.startswith('#b'):
            return '.bv %d %d' % (len(a) - 2, int(a[2:], 2))
        if a in self.by_name:
            if self.decls[self.by_name[a]][1]:
                raise Unsupported("function '%s' used as a constant" % a)
            return '.fn %d []' % self.by_name[a]
        raise Unsupported("undeclared symbol '%s'" % a)

    def indexed(self, h, args, bound, t):
        a = [self.term(x, bound) for x in args]
        if len(h) >= 2 and h[0] == '_':
            name, rest = h[1], h[2:]
            if name == 'int2bv' and len(rest) == 1: o = '(.int2bv %d)' % int(rest[0])
            elif name == 'extract' and len(rest) == 2: o = '(.extract %d %d)' % (int(rest[0]), int(rest[1]))
            elif name == 'zero_extend' and len(rest) == 1: o = '(.zeroExtend %d)' % int(rest[0])
            elif name == 'sign_extend' and len(rest) == 1: o = '(.signExtend %d)' % int(rest[0])
            else: raise Unsupported("unsupported operator in '%s'" % show(t))
            return '.app %s [%s]' % (o, ', '.join(a))
        if len(h) == 3 and h[0] == 'as' and h[1] == 'const':
            s = h[2]
            if not (isinstance(s, list) and s[0] == 'Array'):
                raise Unsupported("'as const' of a non-array sort in '%s'" % show(t))
            return '.constArray %s (%s)' % (sort_lean(s[1]), a[0])
        raise Unsupported("unsupported operator in '%s'" % show(t))

    def command(self, cmd):
        """The Lean assertion a command adds, if any (declare-const, declare-fun, define-fun, assert)."""
        op = cmd[0]
        if op == 'declare-const':
            self.declare(cmd[1], [], sort_lean(cmd[2])); return None
        if op == 'declare-fun':
            self.declare(cmd[1], [sort_lean(s) for s in cmd[2]], sort_lean(cmd[3])); return None
        if op == 'define-fun':
            names = [p[0] for p in cmd[2]]
            sorts = [sort_lean(p[1]) for p in cmd[2]]
            body = self.term(cmd[4], list(names))
            f = self.declare(cmd[1], sorts, sort_lean(cmd[3]))
            vars_ = ', '.join('.var %d' % i for i in reversed(range(len(names))))
            eq = '.app .eq [.fn %d [%s], %s]' % (f, vars_, body)
            return eq if not names else '.«forall» [%s] (%s)' % (', '.join(sorts), eq)
        if op == 'assert':
            return self.term(cmd[1], [])
        raise Unsupported("unsupported command '%s'" % op)

# ------------------------------------------------------------------------------ loop VCs

def atoms(t):
    if isinstance(t, str):
        return {t}
    out = set()
    for x in t:
        out |= atoms(x)
    return out

def binders_of(t):
    if isinstance(t, str):
        return []
    out = []
    if t and t[0] in ('forall', 'exists'):
        out += [v[0] for v in t[1]]
    for x in t:
        out += binders_of(x)
    return out

def subst(t, m, bound=()):
    """Substitution of free symbols by terms: SMT-LIB's meaning of a define-fun application."""
    if isinstance(t, str):
        return m[t] if t in m and t not in bound else t
    if t and t[0] in ('forall', 'exists'):
        names = tuple(v[0] for v in t[1])
        clash = set(names) & set(a for v in m.values() for a in atoms(v))
        if clash:
            raise Unsupported('a quantifier of the candidate binds a symbol of the edge: %s' % sorted(clash))
        return [t[0], t[1], subst(t[2], m, bound + names)]
    if t and t[0] == 'let':
        raise Unsupported("unsupported 'let'")
    return [subst(x, m, bound) for x in t]

def expand_lets(t, env=None):
    """Spacer's lets, replaced by what they name (the meaning SMT-LIB gives let)."""
    env = env or {}
    if isinstance(t, str):
        return env.get(t, t)
    if t and t[0] == 'let':
        inner = dict(env)
        for name, val in t[1]:
            inner[name] = expand_lets(val, env)
        return expand_lets(t[2], inner)
    if t and t[0] in ('forall', 'exists'):
        names = {v[0] for v in t[1]}
        return [t[0], t[1], expand_lets(t[2], {k: v for k, v in env.items() if k not in names})]
    return [expand_lets(x, env) for x in t]

def conjuncts(t):
    if isinstance(t, list) and t and t[0] == 'and':
        return [c for x in t[1:] for c in conjuncts(x)]
    return [t]

def split_clause(c):
    """(binders, body conjuncts, head) of an asserted Horn clause."""
    if isinstance(c, list) and c and c[0] == '!':
        c = c[1]
    binders = []
    if isinstance(c, list) and c and c[0] == 'forall':
        binders, c = c[1], c[2]
    if isinstance(c, list) and c and c[0] == '=>' and len(c) == 3:
        body = c[1]
        return binders, (body[1:] if isinstance(body, list) and body and body[0] == 'and' else [body]), c[2]
    return binders, [], c

def load_spacer(path, cut):
    answer = parse_all(open(path).read())
    if not answer or answer[0] != 'sat' or len(answer) < 2:
        raise SystemExit('%s is not a sat answer with a model' % path)
    for d in answer[1]:
        if isinstance(d, list) and d and d[0] == 'define-fun' and d[1].strip('|') == cut['predicate'].strip('|'):
            params = [p[0] for p in d[2]]
            names = ['|%s|' % p['name'] for p in cut['params']]
            if len(params) != len(names):
                raise SystemExit('the model of %s has %d parameters, the cutpoint %d' % (d[1], len(params), len(names)))
            body = subst(expand_lets(d[4]), dict(zip(params, names)))
            return {
                'id': 'spacer-' + sha256_file(path)[:12], 'origin': 'spacer', 'cutpoint': cut['id'],
                'clauses': [{'text': show(c), 'smt': show(c), 'span': None} for c in conjuncts(body)],
            }
    raise SystemExit('no model of %s in %s' % (cut['predicate'], path))

def rel(path, root):
    r = os.path.relpath(os.path.abspath(path), os.path.abspath(root))
    if r.startswith('..'):
        raise SystemExit('%s is outside the root %s' % (path, root))
    return r.replace(os.sep, '/')

def loc(span):
    return '%s:%s:%s' % (span['file'], span['line'], span['column']) if span else '-'

LITERAL = re.compile(r'\d+|#x[0-9a-fA-F]+|#b[01]+|true|false')

def loopvc_main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog='smt2lean_inv.py loopvc')
    ap.add_argument('--interface', required=True)
    ap.add_argument('--candidate')
    ap.add_argument('--spacer')
    ap.add_argument('--root', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args(argv)
    root = a.root
    here = os.path.dirname(os.path.abspath(__file__))
    lib = os.path.normpath(os.path.join(here, '..', 'Obligation'))
    meta = json.load(open(a.interface))
    horn_path = os.path.join(os.path.dirname(a.interface), meta['horn'])
    horn = parse_all(open(horn_path).read())
    cuts = {c['predicate']: c for c in meta['cutpoints']}
    preds = {'|%s|' % p for p in cuts} | set(cuts)
    macros = [c for c in horn if isinstance(c, list) and c and c[0] == 'define-fun']
    clauses = [c[1] for c in horn if isinstance(c, list) and c and c[0] == 'assert']
    supported = [e for e in meta['edges'] if e.get('supported', True)]
    if len(clauses) != len(supported):
        raise SystemExit('the Horn view has %d clauses, the interface %d supported edges' % (len(clauses), len(supported)))

    # The candidate: per cutpoint, clauses over the cutpoint's parameters.
    sources = [a.interface, horn_path]
    if a.spacer:
        if len(cuts) != 1:
            raise SystemExit('--spacer reads one cutpoint')
        cands = [load_spacer(a.spacer, next(iter(cuts.values())))]
        sources.append(a.spacer)
    elif a.candidate:
        cj = json.load(open(a.candidate))
        cands = cj if isinstance(cj, list) else [cj]
        sources.append(a.candidate)
    else:
        cands = meta['candidates']
    cand_of = {}
    for c in cands:
        if c['cutpoint'] in cand_of:
            raise SystemExit('two candidates for cutpoint %s' % c['cutpoint'])
        cand_of[c['cutpoint']] = c
    cand_id = '+'.join(cand_of[k]['id'] for k in sorted(cand_of))
    rankings = {r['cutpoint']: r for r in meta.get('rankings', [])}
    for s in meta['edges']:
        if s.get('span'):
            src = os.path.join(root, s['span']['file'])
            if os.path.exists(src) and src not in sources:
                sources.append(src)

    unit = meta['unit']
    contract, fn = unit.split('.', 1)
    modpath = 'LoopVc/%s/%s_loop%d' % (re.sub(r'\W', '_', contract), re.sub(r'\W', '_', fn), meta['loop'])
    # Under SolarVerifyVc, the root whose definitions vc_valid_prep unfolds (Valid.lean).
    ns = 'SolarVerifyVc.' + modpath.replace('/', '.')
    unsupported = []

    def params(cut):
        return ['|%s|' % p['name'] for p in cuts[cut]['params']]

    def instance(app):
        """The candidate at a predicate application: its cutpoint, (clause, formula) per clause
        at the arguments, and the arguments by parameter."""
        name = app if isinstance(app, str) else app[0]
        args = [] if isinstance(app, str) else app[1:]
        cut = name.strip('|')
        ps = params(cut)
        if len(ps) != len(args):
            raise Unsupported('%s applied to %d arguments, it has %d' % (cut, len(args), len(ps)))
        if cut not in cand_of:
            raise Unsupported('no candidate for cutpoint %s' % cut)
        out = []
        for cl in cand_of[cut]['clauses']:
            if cl.get('smt') is None:
                raise Unsupported("candidate clause '%s' is not over the cutpoint's parameters" % cl['text'])
            phi = parse_all(cl['smt'])[0]
            free = {x for x in atoms(phi) - set(ps) - set(OPS) - set(binders_of(phi)) if not LITERAL.fullmatch(x)}
            free -= {'forall', 'exists', '_', '!', 'ite'}
            if free:
                raise Unsupported("candidate clause '%s' names %s" % (cl['text'], sorted(free)))
            out.append((cl, subst(phi, dict(zip(ps, args)))))
        return cut, out, dict(zip([p.strip('|') for p in ps], args))

    def is_pred(t):
        h = t if isinstance(t, str) else (t[0] if t else None)
        return isinstance(h, str) and h in preds

    obligations = []
    for edge, cl in zip(supported, clauses):
        try:
            binders, body, head = split_clause(cl)
            pre = [instance(t) for t in body if is_pred(t)]
            facts = [t for t in body if not is_pred(t)]
            decls = [['declare-const', b[0], b[1]] for b in binders]
            guard = [phi for _cut, inst, _args in pre for _cl, phi in inst]
            g = ['and'] + guard if guard else 'true'
            base = dict(edge=edge, decls=decls, facts=facts, guard=g, pre={c: args for c, _i, args in pre})
            if is_pred(head):
                cut, inst, post = instance(head)
                kind = {'entry': 'initiation', 'back': 'preservation', 'call': 'call'}.get(edge['kind'], edge['kind'])
                for k, (c, phi) in enumerate(inst):
                    obligations.append(dict(base, kind=kind, goal=phi, clause=c, cutpoint=cut, post=post, tag='%s.c%d' % (kind, k)))
                if edge['kind'] == 'back' and cut in rankings and len(pre) == 1 and pre[0][0] == cut:
                    r = rankings[cut]
                    rt = parse_all(r['smt'])[0]
                    names = [p.strip('|') for p in params(cut)]
                    before = subst(rt, dict(zip(params(cut), [pre[0][2][p] for p in names])))
                    after = subst(rt, dict(zip(params(cut), [post[p] for p in names])))
                    goal = ['and', ['<=', '0', before], ['<', after, before]]
                    obligations.append(dict(base, kind='termination', goal=goal, clause=r, cutpoint=cut, post=post, tag='termination'))
            else:
                kind = {'exit': 'exit', 'revert': 'outcome-revert', 'oog': 'outcome-oog'}.get(edge['kind'], edge['kind'])
                obligations.append(dict(base, kind=kind, goal=head, clause=None, cutpoint=None, post={}, tag=kind))
        except Unsupported as e:
            unsupported.append((edge, str(e)))
    for e in meta['edges']:
        if not e.get('supported', True):
            unsupported.append((e, 'the exporter could not write this edge in the Horn fragment'))

    # The module: one script and one obligation per row, as solar-verify --emit-lean writes them.
    os.makedirs(os.path.join(a.out, os.path.dirname(modpath)), exist_ok=True)
    L = ['-- Generated by Verify/Infer/smt2lean_inv.py loopvc; do not edit.',
         'import Verify.Obligation', '', 'set_option maxRecDepth 100000', '',
         'namespace %s' % ns, 'open SolarVerify.Smt SolarVerify.Vc', '']
    rows = []
    for k, ob in enumerate(obligations):
        sc = Scope()
        asserts = []
        cmds = [show(m) for m in macros] + [show(d) for d in ob['decls']] + ['(assert %s)' % show(f) for f in ob['facts']]
        for m in macros + ob['decls']:
            r = sc.command(m)
            if r is not None:
                asserts.append(r)
        for f in ob['facts']:
            asserts.append(sc.command(['assert', f]))
        guard = sc.term(ob['guard'], [])
        goal = sc.term(ob['goal'], [])
        e = ob['edge']
        oid = '%s@loop%d#%s.%s' % (unit, meta['loop'], e['id'], ob['tag'])
        cl = ob['clause']
        what = cl['text'] if cl else (e.get('check') or e['kind'])
        L.append('/-- %s: %s of edge %s (%s) at %s, %s "%s" of candidate %s. -/' % (
            oid, ob['kind'], e['id'], e['kind'], loc(e.get('span')),
            'clause' if cl else 'goal', what, cand_id))
        L.append('def script%d : Script where' % k)
        L.append('  decls := [')
        for j, (n, args, ret) in enumerate(sc.decls):
            L.append('    ⟨%s, [%s], %s⟩%s' % (lean_string(n), ', '.join(args), ret, ',' if j + 1 < len(sc.decls) else ''))
        L.append('  ]')
        L.append('  asserts := [')
        for j, x in enumerate(asserts):
            L.append('    %s%s' % (x, ',' if j + 1 < len(asserts) else ''))
        L.append('  ]')
        L.append('')
        L.append('def ob%d : Obligation where\n  script := script%d\n  upto := %d\n  guard := %s\n  goal := %s\n' % (k, k, len(asserts), guard, goal))
        smt = ''.join(c + '\n' for c in cmds) + '(assert %s)\n(assert (not %s))\n(check-sat)\n' % (show(ob['guard']), show(ob['goal']))
        smt_file = '%s.ob%d.smt2' % (modpath, k)
        with open(os.path.join(a.out, smt_file), 'w') as f:
            f.write(smt)
        rows.append({
            'id': oid, 'lean': '%s.ob%d' % (ns, k), 'role': 'obligation', 'kind': ob['kind'],
            'edge': e['id'], 'edge_kind': e['kind'], 'outcome': e.get('outcome', 'normal'),
            'site': e.get('span'), 'check': e.get('check'), 'cutpoint': ob['cutpoint'],
            'candidate': cand_id,
            'spec': ({'text': cl['text'], 'span': cl.get('span')} if cl else None),
            'pre': {c: {p: show(t) for p, t in args.items()} for c, args in ob['pre'].items()},
            'post': {p: show(t) for p, t in ob['post'].items()},
            'smt': smt_file, 'smt_sha256': sha256_bytes(smt.encode()),
            'answer': 'not-run', 'required': True,
        })
    L.append('end %s' % ns)
    with open(os.path.join(a.out, modpath + '.lean'), 'w') as f:
        f.write('\n'.join(L) + '\n')

    units = [{
        'name': '%s loop%d [%s]' % (unit, meta['loop'], cand_id), 'status': 'generated',
        'module': modpath + '.lean', 'namespace': ns,
        'candidate': {k: v for k, v in sorted(cand_of.items())},
        'obligations': rows,
    }]
    # An edge or clause that could not be written stays required and has no module: discharge.sh
    # fails it as not exported, so it is inconclusive, never proved.
    for e, why in unsupported:
        units.append({
            'name': '%s loop%d edge %s' % (unit, meta['loop'], e['id']), 'status': 'unsupported',
            'reason': why, 'module': None,
            'obligations': [{'id': '%s@loop%d#%s' % (unit, meta['loop'], e['id']), 'required': True,
                             'role': 'obligation', 'answer': 'unsupported', 'reason': why}],
        })
    manifest = {
        'format': 'solar-verify-lean', 'version': 2,
        'generator': {'name': 'Verify/Infer/smt2lean_inv.py loopvc', 'interface': {
            'format': meta.get('format'), 'version': meta.get('version')}},
        'sources': [{'path': rel(p, root), 'sha256': sha256_file(p)} for p in sources],
        'lean': {'toolchain': open(os.path.join(here, '..', '..', 'lean-toolchain')).read().strip(),
                 'smt_sha256': sha256_file(os.path.join(lib, 'Smt.lean')),
                 'vc_sha256': sha256_file(os.path.join(lib, 'Vc.lean'))},
        'units': units,
    }
    with open(os.path.join(a.out, 'manifest.json'), 'w') as f:
        f.write(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print('loopvc: %d obligations for %s (candidate %s), %d edges unsupported' % (
        len(rows), unit, cand_id, len(unsupported)), file=sys.stderr)
    return 0

# ----------------------------------------------------------------------- CTIs and residuals

def z3_version(z3):
    try:
        return subprocess.run([z3, '--version'], capture_output=True, text=True).stdout.strip()
    except OSError:
        return None

def cti_main(argv):
    d = argv[0]
    z3 = os.environ.get('SOLAR_VERIFY_Z3', 'z3')
    manifest = json.load(open(os.path.join(d, 'manifest.json')))
    summary = {}
    with open(os.path.join(d, 'discharge', 'summary.tsv')) as f:
        next(f)
        for line in f:
            r = line.rstrip('\n').split('\t')
            summary[r[0]] = r[3]
    out, n_cti = [], 0
    os.makedirs(os.path.join(d, 'discharge', 'residual'), exist_ok=True)
    for u in manifest['units']:
        for ob in u['obligations']:
            if not ob.get('required') or summary.get(ob['id']) == 'proved':
                continue
            row = {'id': ob['id'], 'status': summary.get(ob['id'], 'missing'),
                   'candidate': ob.get('candidate'), 'edge': ob.get('edge'), 'kind': ob.get('kind'),
                   'site': ob.get('site'), 'spec': ob.get('spec')}
            if u.get('module') is None:
                row.update(verdict='inconclusive', reason=u.get('reason'))
                out.append(row); continue
            terms = [('pre', p, t) for _c, args in sorted(ob['pre'].items()) for p, t in args.items()]
            terms += [('post', p, t) for p, t in ob['post'].items()]
            q = open(os.path.join(d, ob['smt'])).read()
            if terms:
                q += '(get-value (%s))\n' % ' '.join(t for _c, _p, t in terms)
            try:
                res = subprocess.run([z3, '-in', '-smt2', '-T:60'], input=q, capture_output=True, text=True, timeout=90).stdout
            except subprocess.TimeoutExpired:
                res = 'timeout'
            first = res.split('\n', 1)[0].strip()
            if first == 'sat':
                vals = parse_all(res.split('\n', 1)[1]) if terms else []
                vals = vals[0] if vals else []
                state = {}
                for (c, p, _t), v in zip(terms, vals):
                    state.setdefault(c, {})[p] = show(v[1])
                row.update(verdict='cti', solver=z3_version(z3), **state)
                n_cti += 1
            else:
                row.update(verdict='inconclusive', reason='z3: ' + (first or 'no answer'))
            out.append(row)
            safe = re.sub(r'[^A-Za-z0-9_]', '_', ob['id'])
            with open(os.path.join(d, 'discharge', 'residual', safe + '.lean'), 'w') as f:
                f.write('-- Open: %s (%s).\n-- The exact goal no backend proved: a proof of it closes the obligation when\n'
                        '-- discharge.sh accepts it as a certificate (backend cert).%s\n'
                        'import Verify.Obligation\nimport %s\n\ntheorem residual : %s.Valid := by\n  skip\n' % (
                            ob['id'], summary.get(ob['id'], 'missing'),
                            '\n-- z3 found a counterexample to induction (cti.json): the candidate fails here.' if row['verdict'] == 'cti' else '',
                            u['module'][:-5].replace('/', '.'), ob['lean']))
    with open(os.path.join(d, 'discharge', 'cti.json'), 'w') as f:
        f.write(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('cti: %d open obligations, %d with a counterexample to induction (%s)' % (
        len(out), n_cti, os.path.join(d, 'discharge', 'cti.json')), file=sys.stderr)
    return 0

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'loopvc':
        sys.exit(loopvc_main(sys.argv[2:]))
    if len(sys.argv) > 1 and sys.argv[1] == 'cti':
        sys.exit(cti_main(sys.argv[2:]))
    model_main(sys.argv[1], sys.argv[2])
