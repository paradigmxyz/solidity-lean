import json,shutil,sys,pathlib
src=pathlib.Path(sys.argv[1])
def e1(r): r['final']['theorem']='Certified.flag_4ce5cf9a.Final.other'
def e2(r): r['final']['statement']='True'
def e3(r): r['replay']['closure']=3967
def e4(r): del r['replay']['replayed'][100]
def e5(r): r['final']['excluded']=[]; r['statuses']['excluded']=[]
for n,f in [('control',None),('theorem',e1),('statement',e2),('closure',e3),('dropmodule',e4),('excluded',e5)]:
    d=pathlib.Path(n)/'replay'; shutil.copytree(src,d)
    if f:
        r=json.loads((d/'record.json').read_text()); f(r); (d/'record.json').write_text(json.dumps(r,indent=2)+'\n')
