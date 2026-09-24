import part
from part import *
import part2
part.Vlo=part2.Vlo2
mp.dps=20
S=10**12
Mt=M0-mpf(3)/10
def B(l,r): return part.Bcell(mpf(l)/S, mpf(r)/S)
pts=[2*S]; l=2*S; R=4*S; delta=mpf('1e-3')
while l<R:
    if Mt-B(l,R)>=delta: pts.append(R); break
    lo,hi=0,R-l
    while hi-lo>1:
        m=(lo+hi)//2
        if Mt-B(l,l+m)>=delta: lo=m
        else: hi=m
    r=l+lo*97//100; pts.append(r); l=r
print(pts, [float(Mt-B(pts[i],pts[i+1])) for i in range(len(pts)-1)])
# python cross-check of Lean margins for demo cells
P=list(map(int,open('pts.txt').read().split()))
print([int(1e6*(M0-B(P[i],P[i+1]))) for i in range(0,5)])
print([int(1e6*(M0-B(P[i],P[i+1]))) for i in range(500,505)])
# true sup of 2U-V on [2,4] and at 4
print(F(mpf(2)), F(mpf(4)))
