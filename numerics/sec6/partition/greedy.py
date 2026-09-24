import part
from part import *
tightV=part.Vlo
import part2
looseV=part2.Vlo2
mp.dps=20
def greedy(delta,gaps):
    pts=[]
    for i in range(len(gaps)-1):
        l=gaps[i]; R=gaps[i+1]
        while l<R:
            if M0-part.Bcell(l,R)>=delta: pts.append((l,R)); break
            # binary search largest w
            lo,hi=mpf(0),R-l
            for _ in range(40):
                m=(lo+hi)/2
                if M0-part.Bcell(l,l+m)>=delta: lo=m
                else: hi=m
            if lo==0: raise Exception("stuck")
            r=l+lo*mpf('0.98'); pts.append((l,r)); l=r
    return pts
AAg=part.AAp
for name,vf in [("tight",tightV),("loose",looseV)]:
    part.Vlo=vf
    for delta in [mpf('1e-4')]:
        cs=greedy(delta,AAg); print(name,"greedy A-grid",len(cs))
