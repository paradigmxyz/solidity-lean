import json, os, subprocess, sys, time, threading, resource
out = sys.argv[1]; cmd = sys.argv[2:]
log = open(out + ".log", "ab", buffering=0)
t0 = time.time()
p = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
peak = {"tree_rss_kb": 0, "largest_proc_rss_kb": 0}
done = threading.Event()
def tree_rss():
    kids = {}
    tot = 0; big = 0
    for pid in os.listdir("/proc"):
        if not pid.isdigit(): continue
        try:
            with open(f"/proc/{pid}/stat") as f: s = f.read()
            fields = s[s.rindex(")")+2:].split()
            sid = int(fields[3])
            if sid != p.pid: continue
            with open(f"/proc/{pid}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):
                        kb = int(line.split()[1]); tot += kb; big = max(big, kb)
        except Exception: pass
    return tot, big
def sample():
    while not done.is_set():
        t, b = tree_rss()
        peak["tree_rss_kb"] = max(peak["tree_rss_kb"], t); peak["largest_proc_rss_kb"] = max(peak["largest_proc_rss_kb"], b)
        done.wait(1.0)
th = threading.Thread(target=sample, daemon=True); th.start()
rc = p.wait(); done.set(); th.join()
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
rec = {"cmd": cmd, "exit": rc, "wall_s": round(time.time() - t0, 1), "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t0)),
       "peak_tree_rss_mb": round(peak["tree_rss_kb"]/1024), "peak_proc_rss_mb_sampled": round(peak["largest_proc_rss_kb"]/1024),
       "ru_maxrss_mb": round(ru.ru_maxrss/1024)}
json.dump(rec, open(out + ".slot.json", "w"), indent=1)
print(json.dumps(rec)); sys.exit(rc)
