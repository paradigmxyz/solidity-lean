
import pathlib,graphlib
root=pathlib.Path('Certified/flag_4ce5cf9a')
mods={}
for f in root.rglob('*.lean'):
    m='.'.join(f.with_suffix('').parts)
    imps=[l.split()[1] for l in f.read_text().splitlines() if l.startswith('import ')]
    mods[m]=[i for i in imps if i.startswith('Certified.flag_4ce5cf9a')]
order=list(graphlib.TopologicalSorter(mods).static_order())
open(__import__('os').path.expanduser('~/bench/order.txt'),'w').write(chr(10).join(order)+chr(10))
print(len(order)); print(' '.join(o.replace('Certified.flag_4ce5cf9a.','') for o in order))
