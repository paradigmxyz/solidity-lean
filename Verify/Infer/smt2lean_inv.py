#!/usr/bin/env python3
"""Mechanical translation of a z3 Spacer model (define-fun Inv ...) into a Lean 4 def.
No simplification or editing: each SMT-LIB operator maps 1:1 to a Lean operator, let stays let."""
import sys, re

def tokenize(s):
    return re.findall(r'\(|\)|[^\s()]+', s)

def parse(toks, i=0):
    if toks[i] == '(':
        out = []; i += 1
        while toks[i] != ')':
            x, i = parse(toks, i); out.append(x)
        return out, i + 1
    return toks[i], i + 1

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

text = open(sys.argv[1]).read()
name = sys.argv[2]
toks = tokenize(text[text.index('(define-fun'):])
d, _ = parse(toks)
_, fname, params, ret, body = d
binders = ' '.join('(' + ident(p) + ' : Int)' for p, _t in params)
print('/-- Verbatim from ' + sys.argv[1] + ' (z3 Spacer model for ' + fname + '). -/')
print('def ' + name + ' ' + binders + ' : Prop :=')
print('  ' + lean(body))
