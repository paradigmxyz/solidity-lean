#!/usr/bin/env python3
"""Checks the axiom pass's output and greps its import closure.

Usage: axiom-closure.py LOG... -- CLOSURE...

Each LOG is the output of one SolidCore/Refinement/Axioms file; every "depends on axioms" line
must name only propext, Classical.choice and Quot.sound, and no line may report an error or an
axiom violation. Each CLOSURE lists the modules of one file's environment with their sources; the
script strips comments from every source outside the toolchain and Mathlib's ecosystem and greps
it for sorry, native_decide, bv_decide and ofReduceBool, and checks that no SolidCore.Witness
module and no Corpus/C4/SeqPart module is in any closure.

A grep hit fails the pass unless it is one of KNOWN's, each a vendored or tactic-fallback line
that no audited declaration reaches. That is sound because the grep is a second line of defence:
native_decide closes a goal through an axiom of its own (Lean 4.35 names it
<decl>._native.native_decide.ax_*; older Lean used Lean.ofReduceBool) and bv_decide through
Lean.ofReduceBool, and #print axioms and the sweep report every axiom other than propext,
Classical.choice and Quot.sound that a declaration's proof reaches, failing the pass on it. A
known line that is gone also fails the pass, so the list cannot go stale.
"""
import re, sys

args = sys.argv[1:]
cut = args.index('--')
logs, closures = args[:cut], args[cut + 1:]
ok = True
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
printed = 0
for log in logs:
    text = open(log).read()
    for m in re.finditer(r"^'(.+)' depends on axioms: \[([^\]]*)\]", text, re.M):
        printed += 1
        axs = {a.strip() for a in m.group(2).split(',') if a.strip()}
        if not axs <= allowed:
            ok = False
            print(f'VIOLATION {log}: {m.group(1)} {sorted(axs)}')
    for m in re.finditer(r"^'(.+)' does not depend on any axioms", text, re.M):
        printed += 1
    for line in text.splitlines():
        if 'error' in line or 'AXIOM-VIOLATION' in line:
            ok = False
            print(f'{log}: {line}')
    for line in text.splitlines():
        if 'axiom sweep:' in line:
            print(f'{log}: {line.split("info: ")[-1]}')
print(f'#print axioms lines: {printed}')

skip = re.compile(r'/(toolchains|packages/(mathlib|batteries|aesop|Qq|plausible|importGraph|LeanSearchClient|proofwidgets|Cli))/', re.I)
pat = re.compile(r'\bsorry\b|\bnative_decide\b|\bbv_decide\b|\bofReduceBool\b|decide\s*\+\s*native|Lean\.trustCompiler|^\s*axiom\s')

def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == '\n': out.append('\n')
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)

files = {}
for c in closures:
    for line in open(c):
        mod, path = line.split()
        files.setdefault(path, set()).add(c)
        if mod.startswith('SolidCore.Witness') or re.match(r'SolidCore\.Refinement\.Corpus\.C4\.SeqPart', mod):
            ok = False
            print(f'FORBIDDEN MODULE in {c}: {mod}')
        if path == '?':
            print(f'note: no source for {mod} in {c}')
# Grep hits allowed by path suffix and stripped line; see the module docstring.
KNOWN = {
    # Symex's symex_bv tries the kernel-checked symex_omega first and falls back on bv_decide;
    # a proof that took the fallback would depend on Lean.ofReduceBool, which the axiom checks
    # above report.
    ('SolidCore/Refinement/Evm/Symex.lean', '| bv_decide (config := { enums := false })))'),
    # Vendored evmyul: the private lemmas fromBytes'_cons_mod and fromBytes'_cons_div, behind
    # EvmYul.zeroPadBytes_toBytes'_fromBytes'_eq_of_length_eq_32 and the zeroPadBytes theorems
    # after it, which depend on their EvmYul.fromBytes'_cons_*._native.native_decide.ax_* axioms;
    # no audited declaration reaches them (the sweep reports none outside the three axioms).
    ('vendor/evmyul/EvmYul/UInt256.lean', 'rw [show 2 ^ 8 = UInt8.size by native_decide]'),
}
seen = set()
scanned = 0
for path in sorted(files):
    if path == '?' or skip.search(path):
        continue
    scanned += 1
    src = strip(open(path).read())
    for k, line in enumerate(src.splitlines(), 1):
        if pat.search(line):
            known = next((e for e in KNOWN if path.endswith('/' + e[0]) and line.strip() == e[1]), None)
            if known:
                seen.add(known)
                print(f'known {path}:{k}: {line.strip()[:160]}')
                continue
            ok = False
            print(f'HIT {path}:{k}: {line.strip()[:160]}')
for e in sorted(KNOWN - seen):
    ok = False
    print(f'STALE known hit, not found: {e[0]}: {e[1]}')
print(f'closure: {len(files)} source files, {scanned} scanned outside the toolchain and Mathlib')
print('AXIOM PASS OK' if ok else 'AXIOM PASS FAILED')
sys.exit(0 if ok else 1)
