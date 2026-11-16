#!/usr/bin/env python3
"""Join the trace profiler output, the RSS/wall record and the kernel recheck CSV of the generated
acc4-flag modules into one row per command (an obligation: a theorem, a kernel_rfl, a def) and one
row per tactic head. Usage: parse.py <out-dir> <modules...>

elab_ms     the command's own profiler time plus its async proof elaboration ("elaborating proof
            of X"), which includes the kernel check when Lean runs it inside the async task.
kernel_ms   profiler [Kernel] nodes ("typechecking declarations [..]") inside the command or its
            proof task, i.e. kernel time during the real build.
recheck_ms  the same declarations re-added to the kernel alone by Kernel.lean (warm, no elaboration).
dag/tree    proof value size of those declarations (DAG after ShareCommon; tree capped at 10^7).
"""
import csv, json, re, sys, collections, pathlib
out = pathlib.Path(sys.argv[1]); mods = sys.argv[2:]
LINE = re.compile(r'^(\s*)\[([^\]]+)\] \[([0-9.]+)\] \S+\s?(.*)$')
def nodes(data):
    for x in data.split('\n'):
        m = LINE.match(x)
        if m: yield len(m.group(1)) // 2, m.group(2), float(m.group(3)) * 1000, m.group(4)
def rss(path, key):
    m = re.search(key + r'.*?: (\d+)', path.read_text()); return int(m.group(1)) // 1024 if m else ''
cmds, tac = [], collections.Counter()
for mod in mods:
    kern = {r['decl']: r for r in csv.DictReader((out / 'kernel' / f'{mod}.csv').open())}
    tfile = out / 'time' / f'{mod}.txt'
    wall = re.search(r'Elapsed .*?: (\S+)', tfile.read_text()).group(1)
    peak = rss(tfile, 'Peak single process RSS sampled'); krss = rss(out / 'time' / f'{mod}.kernel.txt', 'Peak single process RSS sampled')
    by_line = collections.OrderedDict(); owner = {}
    for l in (out / 'trace' / f'{mod}.jsonl').read_text().splitlines():
        try: m = json.loads(l)
        except Exception: continue
        line = m['pos']['line']; stack = []; top = None
        for depth, cls, ms, txt in nodes(m['data']):
            stack = stack[:depth] + [(cls, txt)]
            if depth == 0:
                if cls == 'Elab.command':
                    c = by_line.setdefault(line, dict(text=txt.strip()[:90], elab=0.0, kernel=0.0, decls=[], heads=collections.Counter()))
                    c['elab'] += ms; top = c
                elif cls == 'Elab.async' and txt.startswith('elaborating proof of '):
                    n = txt.split('elaborating proof of ', 1)[1].strip()
                    c = by_line.setdefault(line, dict(text=n, elab=0.0, kernel=0.0, decls=[], heads=collections.Counter()))
                    c['elab'] += ms; top = c
                else:
                    top = None
                continue
            if top is None: continue
            if cls == 'Kernel':
                mm = re.search(r'typechecking declarations \[(.*)\]', txt)
                if mm:
                    top['kernel'] += ms
                    for n in mm.group(1).split(', '):
                        if n not in top['decls']: top['decls'].append(n)
            if cls == 'Elab.step' and stack[0][0] == 'Elab.async' and all(s[0] != 'Elab.step' for s in stack[1:depth]):
                head = (txt.split() or ['?'])[0]; top['heads'][head] += ms; tac[(mod, head)] += ms
            if cls == 'addDecl':
                mm = re.search(r'adding declarations \[(.*)\]', txt)
                if mm:
                    for n in mm.group(1).split(', '):
                        if n not in top['decls']: top['decls'].append(n)
    for line, c in by_line.items():
        ks = [kern[d] for d in c['decls'] if d in kern]
        cmds.append(dict(module=mod, line=line, command=c['text'].replace('\n', ' '),
            decls=len(c['decls']), elab_ms=round(c['elab'], 1), kernel_ms=round(c['kernel'], 1),
            recheck_ms=round(sum(float(k['kernel_ms']) for k in ks), 2),
            dag_nodes=sum(int(k['dag_nodes']) for k in ks), tree_nodes=sum(int(k['tree_nodes']) for k in ks),
            rejected=sum(k['status'] != 'ok' for k in ks),
            top_tactics=';'.join(f'{h}={v:.0f}' for h, v in c['heads'].most_common(3)),
            module_wall=wall, module_peak_rss_mib=peak, recheck_peak_rss_mib=krss))
cmds = [c for c in cmds if c['elab_ms'] > 0 or c['decls']]
w = csv.DictWriter(open(out / 'acc4_commands.csv', 'w', newline=''), fieldnames=list(cmds[0].keys()))
w.writeheader(); w.writerows(cmds)
with open(out / 'acc4_tactics.csv', 'w', newline='') as f:
    c = csv.writer(f); c.writerow(['module', 'tactic', 'ms'])
    for (m, h), v in tac.most_common(): c.writerow([m, h, round(v, 1)])
print(len(cmds), 'commands')
