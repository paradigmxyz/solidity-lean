#!/usr/bin/env python3
"""Run a command and record its wall time and its peak RSS: the process tree's summed RSS and the
largest single process, sampled every 50 ms from /proc, plus getrusage's ru_maxrss of children.
Usage: memtime.py <out.txt> <cmd...>; writes lines GNU time -v also uses."""
import os, sys, time, subprocess, resource
out = sys.argv[1]; cmd = sys.argv[2:]
t0 = time.monotonic(); p = subprocess.Popen(cmd)
peak_tree = peak_one = 0
def tree(pid):
    kids = {}
    for d in os.listdir('/proc'):
        if d.isdigit():
            try:
                f = open(f'/proc/{d}/stat').read().rsplit(')', 1)[1].split()
                kids.setdefault(int(f[1]), []).append(int(d))
            except Exception: pass
    st, res = [pid], []
    while st:
        x = st.pop(); res.append(x); st += kids.get(x, [])
    return res
while p.poll() is None:
    tot = one = 0
    for x in tree(p.pid):
        try:
            for l in open(f'/proc/{x}/status'):
                if l.startswith('VmRSS:'):
                    v = int(l.split()[1]); tot += v; one = max(one, v)
        except Exception: pass
    peak_tree = max(peak_tree, tot); peak_one = max(peak_one, one)
    time.sleep(0.05)
wall = time.monotonic() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
m, s = divmod(wall, 60)
with open(out, 'w') as f:
    f.write(f'Command: {" ".join(cmd)}\n')
    f.write(f'Exit status: {p.returncode}\n')
    f.write(f'Elapsed (wall clock) time (h:mm:ss or m:ss): {int(m)}:{s:05.2f}\n')
    f.write(f'User time (seconds): {ru.ru_utime:.2f}\nSystem time (seconds): {ru.ru_stime:.2f}\n')
    f.write(f'Maximum resident set size (kbytes): {ru.ru_maxrss}\n')
    f.write(f'Peak tree RSS sampled (kbytes): {peak_tree}\nPeak single process RSS sampled (kbytes): {peak_one}\n')
sys.exit(p.returncode)
