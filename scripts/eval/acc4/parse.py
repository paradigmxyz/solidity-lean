#!/usr/bin/env python3
"""Join the trace profiler output, /usr/bin/time and the kernel recheck CSV into one row per
declaration of the generated acc4-flag modules. Usage: parse.py <out-dir> <modules...>"""
import csv, json, re, sys, collections, pathlib

out = pathlib.Path(sys.argv[1]); mods = sys.argv[2:]
LINE = re.compile(r'^(\s*)\[([^\]]+)\] \[([0-9.]+)\] \S+\s?(.*)$')

def nodes(data):
    for x in data.split('\n'):
        m = LINE.match(x)
        if m: yield len(m.group(1)) // 2, m.group(2), float(m.group(3)) * 1000, m.group(4)

rows, steps = [], collections.Counter()
for mod in mods:
    tr = out / 'trace' / f'{mod}.jsonl'
    t = (out / 'time' / f'{mod}.txt').read_text()
    rss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', t).group(1)) // 1024
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', t).group(1)
    tk = (out / 'time' / f'{mod}.kernel.txt').read_text()
    krss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', tk).group(1)) // 1024
    decl = collections.defaultdict(lambda: dict(elab_ms=0.0, kernel_build_ms=0.0, line=None, top=collections.Counter()))
    errors = 0
    for l in tr.read_text().splitlines():
        try: m = json.loads(l)
        except Exception: continue
        if m.get('severity') == 'error': errors += 1
        line = m['pos']['line']
        stack = []
        for depth, cls, ms, txt in nodes(m['data']):
            stack = stack[:depth] + [(cls, txt)]
            if depth == 0 and cls == 'Elab.async' and txt.startswith('elaborating proof of '):
                n = txt.split('elaborating proof of ', 1)[1].strip(); d = decl[n]
                d['elab_ms'] += ms; d['line'] = d['line'] or line; cur = n
            elif depth == 0 and cls == 'Elab.command':
                mm = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|def|abbrev|lemma|instance|opaque)\s+(\S+)', txt)
                if mm:
                    cur = mm.group(2); decl[('cmd', line)]['elab_ms'] += ms; decl[('cmd', line)]['name'] = cur
            elif depth == 1 and cls == 'Kernel':
                mm = re.search(r'typechecking declarations \[(.*)\]', txt)
                if mm:
                    for n in mm.group(1).split(', '):
                        decl[n.strip()]['kernel_build_ms'] += ms
            elif depth == 2 and cls == 'Elab.step' and stack[0][0] == 'Elab.async' and stack[0][1].startswith('elaborating proof of '):
                n = stack[0][1].split('elaborating proof of ', 1)[1].strip()
                head = txt.split()[0] if txt.split() else '?'
                decl[n]['top'][head] += ms; steps[(mod, head)] += ms
    # Fold the synchronous command time (header, and the whole proof when not async) by name.
    byname = {}
    for k, v in list(decl.items()):
        if isinstance(k, tuple):
            n = v.get('name'); byname[n] = byname.get(n, 0) + v['elab_ms']; del decl[k]
    kern = {}
    kp = out / 'kernel' / f'{mod}.csv'
    if kp.exists():
        for r in csv.DictReader(kp.open()): kern[r['decl']] = r
    for name, r in kern.items():
        short = name
        d = None
        for cand in (name, name.split('.')[-1]):
            if cand in decl: d = decl[cand]; break
        cmd = byname.get(name.split('.')[-1], 0.0)
        rows.append(dict(module=mod, decl=name, kind=r['kind'],
            line=(d or {}).get('line') or '', elab_async_ms=round((d or {}).get('elab_ms', 0.0), 1),
            elab_cmd_ms=round(cmd, 1),
            kernel_build_ms=round((d or {}).get('kernel_build_ms', 0.0), 1),
            kernel_recheck_ms=round(float(r['kernel_ms']), 2),
            tree_nodes=r['tree_nodes'], dag_nodes=r['dag_nodes'], type_dag_nodes=r['type_dag_nodes'],
            kernel_status=r['status'], module_wall=wall, module_peak_rss_mib=rss, recheck_peak_rss_mib=krss,
            module_errors=errors,
            top_tactics=';'.join(f'{h}={v:.0f}' for h, v in (d or {}).get('top', collections.Counter()).most_common(3))))
w = csv.DictWriter(open(out / 'acc4_obligations.csv', 'w', newline=''), fieldnames=list(rows[0].keys()))
w.writeheader(); w.writerows(rows)
with open(out / 'acc4_tactics.csv', 'w', newline='') as f:
    c = csv.writer(f); c.writerow(['module', 'tactic', 'ms'])
    for (m, h), v in steps.most_common(): c.writerow([m, h, round(v, 1)])
print(len(rows), 'rows')
