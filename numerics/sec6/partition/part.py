from data import *
mp.dps=25
def G(c,t):
    if t==0: return c*log(c*c)-2*c
    s=sqrt(t); return c*log(t+c*c)-2*c+2*s*atan(c/s)
def Vlo(l,r): return 2*pi*sqrt(l)+G(1,l)-6*G(alpha,r)
def Uhi(l,r): return sum(cj*max(Uom(l,aj,bj),Uom(r,aj,bj)) for aj,bj,cj in zip(a,b,c))
def Bcell(l,r): return 2*Uhi(l,r)-Vlo(l,r)
AAp=[mpf(0)]+a[::-1]+b+[mpf(2)]   # no q+- needed
def cells(delta, gaps=AAp, maxd=30):
    out=[]
    def rec(l,r,d):
        if M0-Bcell(l,r)>=delta: out.append((l,r,d)); return
        if d>maxd: raise Exception("fail %s"%l)
        m=(l+r)/2; rec(l,m,d+1); rec(m,r,d+1)
    for i in range(len(gaps)-1): rec(gaps[i],gaps[i+1],0)
    return out
import sys
for delta in [mpf('1e-3'),mpf('2e-4'),mpf('5e-5')]:
    cs=cells(delta); print("delta",delta,"cells",len(cs),"maxdepth",max(d for _,_,d in cs))
