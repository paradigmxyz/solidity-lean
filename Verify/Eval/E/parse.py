#!/usr/bin/env python3
"""Parse one lane E run (Verify/Eval/E/run.sh) into a JSON line."""
import json, os, re, sys
name, code, log, olean = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
txt = open(log).read()
tm = open(log + '.time').read()
def ms(label):
    m = re.search(r'^\s*' + re.escape(label) + r' ([0-9.]+)(ms|s)$', txt, re.M)
    if not m: return 0.0
    v = float(m.group(1)); return v * 1000 if m.group(2) == 's' else v
r = {'fixture': name, 'exit': code}
r['elab_ms'] = round(ms('elaboration'), 1)
r['tactic_ms'] = round(ms('tactic execution'), 1)
r['kernel_ms_profiler'] = round(ms('type checking'), 1)
EXCL = ('import', 'interpretation', 'type checking', 'initialization', 'parsing', 'linting',
        'module linting', 'declTypeLinter', 'tacticAnalysis')
prof = {}
for m in re.finditer(r'^\s+([a-z][a-zA-Z .]*?) ([0-9.]+)(ms|s)$', txt, re.M):
    prof[m.group(1)] = round(float(m.group(2)) * (1000 if m.group(3) == 's' else 1), 1)
r['profile'] = prof
r['elab_total_ms'] = round(sum(v for k, v in prof.items() if k not in EXCL), 1)
m = re.search(r'e_stats \S+: decls=(\d+) kernel_ms=([0-9.e+-]+) max_decl_kernel_ms=([0-9.e+-]+) dag_sum=(\d+) dag_union=(\d+) tree_sum=(\d+)', txt)
if m:
    r.update(decls=int(m.group(1)), kernel_recheck_all_ms=round(float(m.group(2)), 2),
             max_decl_kernel_ms=round(float(m.group(3)), 2), dag_sum=int(m.group(4)),
             dag_union=int(m.group(5)), tree_sum=int(m.group(6)))
m = re.search(r'proof_stats \S+: tree=(\d+) dag=(\d+) aux_decls=(\d+) aux_dag=(\d+)', txt)
if m: r.update(main_tree=int(m.group(1)), main_dag=int(m.group(2)), aux_decls=int(m.group(3)), aux_dag=int(m.group(4)))
m = re.search(r'kernel_recheck \S+: ok in ([0-9.e+-]+) ms', txt)
if m: r['kernel_recheck_main_ms'] = round(float(m.group(1)), 2)
m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', tm)
if m: r['peak_rss_kb'] = int(m.group(1))
m = re.search(r'Elapsed \(wall clock\) time.*: (\S+)', tm)
if m: r['wall'] = m.group(1)
r['olean_bytes'] = os.path.getsize(olean) if os.path.exists(olean) and code == 0 else None
if code != 0: r['error'] = '\n'.join(l for l in txt.splitlines() if 'error' in l)[:600]
r['log'] = log
print(json.dumps(r))
