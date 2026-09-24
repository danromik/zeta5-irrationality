from part import *
import part, part2
from collections import Counter
R3=[mpf(0),a[0],b[0],mpf(2)]
for name,vf in [("tight",part.Vlo),("loose",part2.Vlo2)]:
  part.Vlo=vf
  for delta in [mpf('1e-4'),mpf('5e-4')]:
    cs=part.cells(delta,gaps=R3,maxd=40)
    reg=Counter(0 if r<=a[0] else (1 if r<=b[0] else 2) for l,r,d in cs)
    print(name,"delta",delta,"cells",len(cs),"maxdepth",max(d for _,_,d in cs),dict(reg))
