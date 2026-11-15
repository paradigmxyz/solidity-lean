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
# Reads solar-verify's loop-cut interface (--emit-loopvc, format 1: crates/verify's
# docs/loopvc-interface.md) and a candidate, and writes the candidate's obligations. Lean computes
# them: the obligations are what the interface's own Template.instances gives at the candidate,
# printed as terms, and a bridge module proves each template's instances equal to them by rfl.

def atoms(t):
    if isinstance(t, str):
        return {t}
    out = set()
    for x in t:
        out |= atoms(x)
    return out

def subst(t, m, bound=()):
    """Substitution of free symbols by terms: SMT-LIB's meaning of a define-fun application."""
    if isinstance(t, str):
        return m[t] if t in m and t not in bound else t
    if t and t[0] in ('forall', 'exists'):
        return [t[0], t[1], subst(t[2], m, bound + tuple(v[0] for v in t[1]))]
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

LITERAL = re.compile(r'-?\d+|#x[0-9a-fA-F]+|#b[01]+|true|false')

def spacer_candidate(path, iface):
    """Spacer's model of the cut's predicate, over the cut's parameters, as a candidate; the
    ranking function stays the interface's (a Horn solver gives none)."""
    answer = parse_all(open(path).read())
    if not answer or answer[0] != 'sat' or len(answer) < 2:
        raise SystemExit('%s is not a sat answer with a model' % path)
    cut = iface['cut']
    for d in answer[1]:
        if isinstance(d, list) and d and d[0] == 'define-fun' and d[1].strip('|') == cut['predicate'].strip('|'):
            params = [p[0] for p in d[2]]
            if len(params) != len(cut['params']):
                raise SystemExit('the model has %d parameters, the cut %d' % (len(params), len(cut['params'])))
            body = subst(expand_lets(d[4]), dict(zip(params, [p['symbol'] for p in cut['params']])))
            return {
                'id': 'spacer-' + sha256_file(path)[:12],
                'conjuncts': [{'term': show(c), 'text': show(c), 'origin': 'spacer', 'site': None} for c in conjuncts(body)],
                'rank': iface['candidate'].get('rank'),
            }
    raise SystemExit('no model of %s in %s' % (cut['predicate'], path))

def rel(path, root):
    r = os.path.relpath(os.path.abspath(path), os.path.abspath(root))
    if r.startswith('..'):
        raise SystemExit('%s is outside the root %s' % (path, root))
    return r.replace(os.sep, '/')

def lean_env(here):
    """lean and the LEAN_PATH of the discharge library (Verify/Discharge/Reconstruct), which
    builds Verify.Obligation."""
    pkg = os.path.normpath(os.path.join(here, '..', 'Discharge', 'Reconstruct'))
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=pkg, capture_output=True, text=True, check=True).stdout.strip()
    root = os.path.normpath(os.path.join(here, '..', '..'))
    r = subprocess.run(['elan', 'which', 'lean'], cwd=root, capture_output=True, text=True)
    return (r.stdout.strip() if r.returncode == 0 else 'lean'), lp

def run_lean(leanbin, lp, args, cwd):
    r = subprocess.run([leanbin, '-DmaxHeartbeats=0', '-DmaxRecDepth=100000'] + args, cwd=cwd,
                       env=dict(os.environ, LEAN_PATH=lp), capture_output=True, text=True)
    if r.returncode != 0 or re.search(r'(^|\n)[^\n]*error', r.stdout + r.stderr):
        raise SystemExit('lean %s failed:\n%s%s' % (' '.join(args), r.stdout[-4000:], r.stderr[-2000:]))
    return r.stdout

KIND = {('invariant', 'entry'): 'initiation', ('invariant', 'back'): 'preservation',
        ('rank', 'back'): 'termination', ('path', 'exit'): 'exit'}

def loopvc_main(argv):
    import argparse, shutil, tempfile
    ap = argparse.ArgumentParser(prog='smt2lean_inv.py loopvc')
    ap.add_argument('--export', required=True, help='a solar-verify --emit-loopvc directory')
    ap.add_argument('--unit', required=True, help='Contract.function')
    ap.add_argument('--candidate', help='a candidate as the interface writes one: {conjuncts, rank}')
    ap.add_argument('--spacer', help="z3 Spacer's answer for the unit's Horn view")
    ap.add_argument('--root', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args(argv)
    a.export, a.out = os.path.abspath(a.export), os.path.abspath(a.out)
    here = os.path.dirname(os.path.abspath(__file__))
    lib = os.path.normpath(os.path.join(here, '..', 'Obligation'))
    contract, fn = a.unit.split('.', 1)
    mod = '%s/%s' % (contract, fn)
    jpath = os.path.join(a.export, mod + '.loopvc.json')
    iface = json.load(open(jpath))
    if (iface.get('format'), iface.get('version')) != ('solar-verify-loopvc', 1):
        raise SystemExit('%s is not solar-verify-loopvc format 1' % jpath)
    cut = iface['cut']
    horn = iface['horn']['file']
    horn = os.path.join(a.export, horn if '/' in horn else os.path.join(contract, horn))
    sources = [jpath, horn, os.path.join(a.export, 'LoopVc.lean'), os.path.join(a.export, mod + '.lean'),
               os.path.join(a.export, mod + '_loopvc.lean')]
    if iface['horn'].get('sha256') and sha256_file(horn) != iface['horn']['sha256']:
        raise SystemExit('the Horn view is not the one the interface names')
    if iface['lean'].get('library_sha256') and sha256_file(sources[2]) != iface['lean']['library_sha256']:
        raise SystemExit('LoopVc.lean is not the one the interface names')
    if a.spacer:
        cand = spacer_candidate(a.spacer, iface)
        sources.append(a.spacer)
    elif a.candidate:
        cand = dict(json.load(open(a.candidate)))
        cand.setdefault('id', os.path.basename(a.candidate).split('.json')[0])
        sources.append(a.candidate)
    else:
        cand = dict(iface['candidate'], id='annotated')
    cid = re.sub(r'\W', '_', cand['id'])

    # The candidate in the embedding, numbered as the unit's script declares its symbols.
    script_file = os.path.join(a.export, '%s.script%d.smt2' % (mod, cut['head']['script']))
    sources.append(script_file)
    cmds = [l for l in open(script_file).read().split('\n') if l.strip()]
    sc = Scope()
    for c in cmds:
        x = parse_all(c)[0]
        if x[0] in ('declare-const', 'declare-fun', 'define-fun'):
            sc.command(x)
    params = [p['symbol'] for p in cut['params']]
    for p in cut['params']:
        if sc.by_name.get(p['symbol']) != p['lean_symbol']:
            raise SystemExit('parameter %s is not symbol %s of the script' % (p['symbol'], p['lean_symbol']))
    defined = {x[1] for x in (parse_all(c)[0] for c in cmds) if x[0] == 'define-fun'}
    def cand_term(t, what):
        e = parse_all(t)[0]
        free = {x for x in atoms(e) - set(params) - set(OPS) if not LITERAL.fullmatch(x)} - defined
        free -= {'forall', 'exists', '_', '!'} | {v[0] for v in _bound(e)}
        if free:
            raise SystemExit("the candidate's %s '%s' names %s, not only the cut's parameters" % (what, t, sorted(free)))
        return e, sc.term(e, [])
    conj = [cand_term(c['term'], 'conjunct') for c in cand['conjuncts']]
    rank = cand_term(cand['rank']['term'], 'ranking function') if cand.get('rank') else None
    if not conj:
        raise SystemExit('the candidate has no conjunct')

    # Lean: build the interface's modules, and print every template's instances at the candidate.
    leanbin, lp = lean_env(here)
    tmp = tempfile.mkdtemp(prefix='loopvc-')
    try:
        for m in ['LoopVc', mod, mod + '_loopvc']:
            os.makedirs(os.path.join(tmp, os.path.dirname(m)), exist_ok=True)
            run_lean(leanbin, lp + ':' + tmp, ['-o', os.path.join(tmp, m + '.olean'), os.path.join(a.export, m + '.lean')], a.export)
        tns = 'SolarVerifyLoopVc.%s.%s' % (contract, fn)
        cand_lean = '{ conj := [%s], rank := %s }' % (', '.join(t for _e, t in conj), 'some (%s)' % rank[1] if rank else 'none')
        temps = iface['templates']
        pr = ['import %s' % (mod + '_loopvc').replace('/', '.'), 'open SolarVerify.Smt SolarVerify.Vc SolarVerify.LoopVc',
              "def cand' : Cand := %s" % cand_lean]
        for t in temps:
            k = t['id'][1:]
            pr.append('#eval do')
            pr.append("  for o in (%s.t%s.instances %s.cut cand') do" % (tns, k, tns))
            for f in ('script', 'upto', 'guard', 'goal'):
                pr.append('    IO.println "@@%s %s"' % (t['id'], f))
                pr.append('    IO.println (Std.Format.pretty (repr o.%s) 100000)' % f)
        with open(os.path.join(tmp, 'Print.lean'), 'w') as f:
            f.write('\n'.join(pr) + '\n')
        out = run_lean(leanbin, lp + ':' + tmp, [os.path.join(tmp, 'Print.lean')], tmp)
        parts = re.split(r'^@@(t\d+) (script|upto|guard|goal)\n', out, flags=re.M)[1:]
        insts = []
        for i in range(0, len(parts), 3):
            tid, field, val = parts[i], parts[i + 1], parts[i + 2].strip()
            if field == 'script':
                insts.append({'template': tid})
            insts[-1][field] = val
        scripts = []
        for o in insts:
            if o['script'] not in scripts:
                scripts.append(o['script'])

        ns = 'SolarVerifyVc.LoopVc.%s.%s_%s' % (contract, fn, cid)
        modpath = 'LoopVc/%s/%s_%s' % (contract, fn, cid)
        os.makedirs(os.path.join(a.out, os.path.dirname(modpath)), exist_ok=True)
        L = ['-- Generated by Verify/Infer/smt2lean_inv.py loopvc; do not edit.',
             "-- The instances of %s's loop-cut templates (%s) at candidate %s." % (a.unit, rel(jpath, a.root), cand['id']),
             'import Verify.Obligation', '', 'set_option maxRecDepth 100000', '',
             'namespace %s' % ns, 'open SolarVerify.Smt SolarVerify.Vc', '']
        for s, text_ in enumerate(scripts):
            L.append("/-- The function's script with the candidate at the loop head. -/")
            L.append('def script%d : Script :=\n  %s\n' % (s, text_))
        def inst_smt(e):
            """The candidate put back in an SMT-LIB term, as Template.instances does on terms."""
            if isinstance(e, list) and e and e[0] == cut['predicate']:
                m = dict(zip(params, [inst_smt(x) for x in e[1:]]))
                cs = [subst(c, m) for c, _t in conj]
                return cs[0] if len(cs) == 1 else ['and'] + cs
            if isinstance(e, list) and e and e[0] == cut['rank'] and rank:
                return subst(rank[0], dict(zip(params, [inst_smt(x) for x in e[1:]])))
            if isinstance(e, list):
                return [inst_smt(x) for x in e]
            return e
        rows, k = [], 0
        bridge = ['import Lean', 'import %s' % (mod + '_loopvc').replace('/', '.'), 'import %s' % modpath.replace('/', '.'), '',
                  'open SolarVerify.Smt SolarVerify.Vc SolarVerify.LoopVc', '',
                  'namespace %s.Bridge' % ns, '',
                  "/-- The candidate, in the interface's terms. -/",
                  'def cand : Cand := %s' % cand_lean, '']
        if not a.candidate and not a.spacer:
            bridge += ['/-- It is the candidate of the run. -/',
                       'theorem cand_eq : cand = %s.cand := rfl' % tns, '']
        head_cmd = parse_all(cut['head']['template'])[0]
        for t in temps:
            mine = [o for o in insts if o['template'] == t['id']]
            names = []
            for j, o in enumerate(mine):
                kind = KIND.get((t['role'], t['edge']), '%s-%s' % (t['edge'], t['role']))
                c = cand['conjuncts'][j] if t['role'] == 'invariant' else None
                oid = '%s@%s#%s%s' % (a.unit, cut['id'], t['id'], '.c%d' % j if t['role'] == 'invariant' else '')
                L.append('/-- %s: %s of edge %s (template %s, %s)%s, candidate %s. -/' % (
                    oid, kind, t['edge'], t['id'], t['role'],
                    (', conjunct "%s"' % c['text']) if c else '', cand['id']))
                L.append('def ob%d : Obligation where\n  script := script%d\n  upto := %s\n  guard := %s\n  goal := %s\n' % (
                    k, scripts.index(o['script']), o['upto'], o['guard'], o['goal']))
                names.append('%s.ob%d' % (ns, k))
                cs = [parse_all(x)[0] for x in cmds[:t['commands']]]
                hc = cut['head']['command']
                if hc < len(cs):
                    cs[hc] = head_cmd
                goal = parse_all(t['goal'])[0]
                post = {}
                if t['role'] == 'invariant':
                    args = [inst_smt(x) for x in goal[1:]]
                    post = {p['name']: show(x) for p, x in zip(cut['params'], args)}
                    goal = subst(conj[j][0], dict(zip(params, args)))
                else:
                    goal = inst_smt(goal)
                smt = ''.join(show(inst_smt(x)) + '\n' for x in cs)
                smt += '(assert %s)\n(assert (not %s))\n(check-sat)\n' % (show(inst_smt(parse_all(t['guard'])[0])), show(goal))
                smt_file = '%s.ob%d.smt2' % (modpath, k)
                with open(os.path.join(a.out, smt_file), 'w') as f:
                    f.write(smt)
                pre = {} if t['edge'] == 'entry' else {cut['id']: {p['name']: p['symbol'] for p in cut['params']}}
                inst0 = (t.get('instances') or [{}])[0]
                rows.append({
                    'id': oid, 'lean': '%s.ob%d' % (ns, k), 'role': 'obligation', 'kind': kind,
                    'edge': t['edge'], 'template': t['id'], 'template_role': t['role'], 'cutpoint': cut['id'],
                    'site': (c or {}).get('site') or inst0.get('site') or cut.get('site'), 'candidate': cand['id'],
                    'spec': ({'text': c['text'], 'span': c.get('site')} if c else
                             {'text': cand['rank']['text'], 'span': cand['rank'].get('site')} if t['role'] == 'rank' else
                             {'text': inst0.get('kind', t['role']), 'span': inst0.get('site')}),
                    'pre': pre, 'post': post, 'smt': smt_file, 'smt_sha256': sha256_bytes(smt.encode()),
                    'answer': 'not-run', 'required': True,
                })
                k += 1
            bridge.append('theorem %s_exact : %s.%s.instances %s.cut cand = [%s] := rfl' % (
                t['id'], tns, t['id'], tns, ', '.join(names)))
            bridge.append('')
        L.append('end %s' % ns)
        with open(os.path.join(a.out, modpath + '.lean'), 'w') as f:
            f.write('\n'.join(L) + '\n')
        bridge += ['end %s.Bridge' % ns, '', 'open Lean Elab Command in',
                   '#eval show CommandElabM Unit from do',
                   '  for n in [%s] do' % ', '.join('`%s.Bridge.%s_exact' % (ns, t['id']) for t in temps),
                   '    let axs ← Lean.collectAxioms n',
                   '    IO.println s!"AXIOMS {n}: {String.intercalate \" \" (axs.toList.map toString)}"']
        bpath = os.path.join(a.out, 'bridge', modpath + '_bridge.lean')
        os.makedirs(os.path.dirname(bpath), exist_ok=True)
        with open(bpath, 'w') as f:
            f.write('\n'.join(bridge) + '\n')
        # The bridge must check now: each template's instances are exactly the obligations written.
        os.makedirs(os.path.join(tmp, os.path.dirname(modpath)), exist_ok=True)
        run_lean(leanbin, lp + ':' + tmp, ['-o', os.path.join(tmp, modpath + '.olean'), os.path.join(a.out, modpath + '.lean')], a.out)
        bout = run_lean(leanbin, lp + ':' + tmp, [bpath], tmp)
        checked = [l for l in bout.splitlines() if l.startswith('AXIOMS')]
        if len(checked) != len(temps):
            raise SystemExit('the bridge reported %d of %d templates' % (len(checked), len(temps)))
        for line in checked:
            if set(line.split(': ', 1)[1].split()) - {'propext', 'Classical.choice', 'Quot.sound'}:
                raise SystemExit('the bridge uses another axiom: ' + line)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if cut.get('site'):
        p = os.path.join(a.root, cut['site']['file'])
        if p not in sources:
            sources.append(p)
    manifest = {
        'format': 'solar-verify-lean', 'version': 2,
        'generator': {'name': 'Verify/Infer/smt2lean_inv.py loopvc', 'interface': {
            'format': iface['format'], 'version': iface['version'], 'formulas_sha256': iface['sha256']['formulas']}},
        'sources': [{'path': rel(p, a.root), 'sha256': sha256_file(p)} for p in sources],
        'lean': {'toolchain': open(os.path.join(here, '..', '..', 'lean-toolchain')).read().strip(),
                 'smt_sha256': sha256_file(os.path.join(lib, 'Smt.lean')),
                 'vc_sha256': sha256_file(os.path.join(lib, 'Vc.lean'))},
        'units': [{
            'name': '%s %s [%s]' % (a.unit, cut['id'], cand['id']), 'status': 'generated',
            'module': modpath + '.lean', 'namespace': ns, 'bridge': rel(bpath, a.out),
            'candidate': cand,
            # A revert path owes nothing without succeeds-if (the interface's contract): listed, no row.
            'reverts': iface.get('reverts', []),
            'obligations': rows,
        }],
    }
    with open(os.path.join(a.out, 'manifest.json'), 'w') as f:
        f.write(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print('loopvc: %d obligations for %s at %s (candidate %s); bridge checked' % (
        len(rows), a.unit, cut['id'], cand['id']), file=sys.stderr)
    return 0

def _bound(t):
    if isinstance(t, str):
        return []
    out = []
    if t and t[0] in ('forall', 'exists'):
        out += list(t[1])
    for x in t:
        out += _bound(x)
    return out

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
