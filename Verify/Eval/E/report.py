#!/usr/bin/env python3
"""Lane E report: tables with doubling ratios from ~/evalE/results.jsonl (Verify/Eval/E/run.sh).

  python3 Verify/Eval/E/report.py [results.jsonl] > table.md
"""
import json, re, sys, collections
path = sys.argv[1] if len(sys.argv) > 1 else __import__('os').path.expanduser('~/evalE/results.jsonl')
rows = {}
def wall_ms(w):
    parts = [float(x) for x in w.split(':')]
    s = 0.0
    for x in parts: s = s * 60 + x
    return s * 1000
for l in open(path):
    r = json.loads(l)
    if r.get('wall'):
        pr = r.get('profile', {})
        r['wall_ms'] = round(wall_ms(r['wall']))
        # The profiler's cumulative elaboration times overlap (theorem bodies elaborate as tasks);
        # wall time less import, the interpreted stats commands and the kernel is the honest one.
        r['elab_wall_ms'] = round(r['wall_ms'] - pr.get('import', 0) - pr.get('interpretation', 0)
                                  - pr.get('type checking', 0))
    rows[r['fixture']] = r
fam = collections.defaultdict(dict)
for name, r in rows.items():
    m = re.match(r'([A-Za-z]+?)(\d+)_(\w+)$', name)
    if not m: continue
    fam[(m.group(1), m.group(3))][int(m.group(2))] = r
COLS = [('wall_ms', 'wall ms'), ('elab_wall_ms', 'elab ms (wall-based)'), ('elab_total_ms', 'elab ms (profiler sum)'), ('kernel_ms_profiler', 'kernel ms (prof)'),
        ('kernel_recheck_all_ms', 'kernel ms (recheck all)'), ('max_decl_kernel_ms', 'max decl kernel ms'),
        ('dag_union', 'DAG (all decls, shared)'), ('dag_sum', 'DAG sum'), ('tree_sum', 'tree sum'),
        ('decls', 'decls'), ('olean_bytes', '.olean B'), ('peak_rss_kb', 'RSS KB')]
def ratio(a, b):
    try: return '%.2f' % (b / a) if a else '-'
    except TypeError: return '-'
families = sorted(set(f for f, _ in fam))
for f in families:
    print('\n### %s\n' % f)
    print('| variant | N | ' + ' | '.join(c[1] for c in COLS) + ' | x2 kernel | x2 elab | x2 DAG |')
    print('|' + '---|' * (len(COLS) + 5))
    for (ff, v), bysize in sorted(fam.items()):
        if ff != f: continue
        prev = None
        for N in sorted(bysize):
            r = bysize[N]
            if r.get('exit') != 0:
                print('| %s | %d | FAILED: %s |' % (v, N, (r.get('error') or '')[:80].replace('|', '/').replace('\n', ' ')))
                prev = None; continue
            vals = ' | '.join(str(r.get(c[0], '')) for c in COLS)
            if prev:
                rk = ratio(prev['kernel_recheck_all_ms'], r['kernel_recheck_all_ms'])
                re_ = ratio(prev['elab_wall_ms'], r['elab_wall_ms'])
                rd = ratio(prev['dag_union'], r['dag_union'])
            else: rk = re_ = rd = '-'
            print('| %s | %d | %s | %s | %s | %s |' % (v, N, vals, rk, re_, rd))
            prev = r
