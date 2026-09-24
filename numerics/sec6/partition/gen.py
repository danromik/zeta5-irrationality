# greedy partition of [0,2] on the 1e-12 grid, loose V bound (no monotonicity of G_c needed)
import part
from part import *
import part2
part.Vlo=part2.Vlo2
mp.dps=20
S=10**12
def B(l,r): return part.Bcell(mpf(l)/S, mpf(r)/S)
gapsN=[0]+A[::-1]+B_ if False else None
gapsN=[0]+A[::-1]+[x for x in __import__('data').B]+[2*S]
import sys
delta=mpf(sys.argv[1]) if len(sys.argv)>1 else mpf('1e-4')
pts=[0]
for i in range(len(gapsN)-1):
    l=gapsN[i]; R=gapsN[i+1]
    while l<R:
        if M0-B(l,R)>=delta: pts.append(R); break
        lo,hi=0,R-l
        while hi-lo>1:
            m=(lo+hi)//2
            if M0-B(l,l+m)>=delta: lo=m
            else: hi=m
        assert lo>0
        r=l+max(1,lo*97//100); pts.append(r); l=r
print(len(pts)-1, "cells", file=sys.stderr)
worst=min(M0-B(pts[i],pts[i+1]) for i in range(len(pts)-1))
print("worst margin",worst,file=sys.stderr)
open("pts.txt","w").write("\n".join(map(str,pts)))
