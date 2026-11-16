
import re,csv,statistics as st,hashlib
rows=[]
def cat(o,c):
  x=re.search(r'\t'+c+r' ([0-9.]+)(m?s)\n',o); return float(x.group(1))*(1 if x.group(2)=='ms' else 1000) if x else 0.0
for m in ['Evm1','Evm2','Evm3','Evm4','Evm5','Sched']:
  for mode in ['orig','sk']:
    W=[];R=[];T=[];K=[]
    for rep in [1,2]:
      t=open(f'{m}.{mode}.{rep}.time').read(); o=open(f'{m}.{mode}.{rep}.out').read()
      mm,ss=re.search(r'Elapsed .*?: (\S+)',t).group(1).split(':'); W.append(int(mm)*60+float(ss))
      R.append(int(re.search(r'Peak single process RSS sampled \(kbytes\): (\d+)',t).group(1))//1024)
      T.append(cat(o,'tactic execution')+cat(o,'simp')); K.append(cat(o,'type checking'))
    kc=list(csv.DictReader(open(f'{m}.{mode}.kernel.csv')))
    main=[r for r in kc if r['decl'].endswith('_run') and r['kind']=='theorem'][0]
    h=[hashlib.sha256(open(f'{m}.{mode}.{r}.olean','rb').read()).hexdigest()[:16] for r in (1,2)]
    rows.append(dict(module=m,mode=mode,wall_s=round(st.mean(W),2),wall_runs='/'.join(f'{w:.2f}' for w in W),tactic_simp_ms=round(st.mean(T)),kernel_profiler_ms=round(st.mean(K)),kernel_recheck_ms=round(float(main['kernel_ms']),1),dag_nodes=main['dag_nodes'],tree_nodes=main['tree_nodes'],peak_rss_mib=max(R),olean_rep1=h[0],olean_rep2=h[1]))
w=csv.DictWriter(open('skip_ab.csv','w',newline=''),fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
for r in rows: print(r['module'],r['mode'],r['wall_runs'],r['tactic_simp_ms'],r['kernel_profiler_ms'],r['kernel_recheck_ms'],r['dag_nodes'],r['tree_nodes'],r['peak_rss_mib'],r['olean_rep1']==r['olean_rep2'])
