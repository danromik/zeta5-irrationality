# exact control: Gf n i j at n=1 (K=40,N=3,h=37), computed from the t-side definition muOver
from fractions import Fraction as Fr
from math import factorial
from sympy import bernoulli as sB
import sys
n=1; K=40*n; N=3*n; h=37*n
def pmul(a,b):
    r=[Fr(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def padd(a,b):
    r=[Fr(0)]*max(len(a),len(b))
    for i,x in enumerate(a): r[i]+=x
    for i,x in enumerate(b): r[i]+=x
    return r
def pscale(a,c): return [c*x for x in a]
def peval(a,v):
    s=Fr(0)
    for c in reversed(a): s=s*v+c
    return s
def pdivmod_monic(a,b):
    a=a[:]; db=len(b)-1
    if len(a)-1<db: return [Fr(0)], a
    q=[Fr(0)]*(len(a)-db)
    for i in range(len(a)-1, db-1, -1):
        c=a[i]
        if c!=0:
            q[i-db]=c
            for j in range(db+1): a[i-db+j]-=c*b[j]
    return q, a[:db]
def pderiv(a): return [i*a[i] for i in range(1,len(a))]
def D(m):
    r=[Fr(1)]
    for j in range(1,m+1): r=pmul(r,[Fr(j*j),Fr(1)])
    return r
def qb(i):
    if i==0: return [Fr(1)]
    c=Fr((-1)**i*2, factorial(2*i))
    return pscale(pmul([Fr(0),Fr(1)], D(i-1)), c)
Bern={}
def Bn(k):
    if k not in Bern:
        b=sB(k); Bern[k]=Fr(int(b.p), int(b.q)) if k!=1 else Fr(-1,2)
    return Bern[k]
def muMono(e): return Fr((-1)**e)*Bn(2*e+2)*(2*e+3)*(2*e+4)*(2*e+5)/24
def H5(j): return sum(Fr(1,v**5) for v in range(1,j+1))
H5c={j:H5(j) for j in range(0,K+1)}
Dtail=[Fr(1)]
for j in range(N+1,K+1): Dtail=pmul(Dtail,[Fr(j*j),Fr(1)])
Dtd=pderiv(Dtail)
DN5=[Fr(1)]
for _ in range(5): DN5=pmul(DN5,D(N))
kap=Fr(factorial(K)**2, factorial(N)**12)
Q=[qb(i) for i in range(h)]
def Gf(i,j):
    A=pmul(DN5, pmul(Q[i],Q[j]))
    q,r=pdivmod_monic(A,Dtail)
    c0=sum((q[e]*muMono(e) for e in range(len(q)) if q[e]!=0), Fr(0))
    c1=Fr(0)
    for jj in range(N+1,K+1):
        res=peval(r,Fr(-jj*jj))/peval(Dtd,Fr(-jj*jj))
        # muPole = j^4 X - j^4 H5 - 1/4 + 1/(2j)
        c1+=res*jj**4
        c0+=res*(-jj**4*H5c[jj]-Fr(1,4)+Fr(1,2*jj))
    return kap*c0, kap*c1
def vp(q,p):
    if q==0: return None
    a,b=q.numerator,q.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v
def flog(p,n):
    k=0;m=1
    while m*p<=n: m*=p;k+=1
    return k
primes=[2,3,5,7,11,13,37,41,43,199,211]
worst={p:10**9 for p in primes}
import itertools, time
t0=time.time()
pairs=[(i,j) for i in range(h) for j in range(i,h)]
step=int(sys.argv[1]) if len(sys.argv)>1 else 1
for (i,j) in pairs[::step]:
    c0,c1=Gf(i,j)
    for p in primes:
        for c in (c0,c1):
            v=vp(c,p)
            if v is not None: worst[p]=min(worst[p],v)
for p in primes:
    L=flog(p,5*K); b=-6*L-vp(Fr(24),p) if vp(Fr(24),p) is not None else -6*L
    b24 = -6*L-(vp(Fr(24),p) or 0)
    print(f"p={p}: min v_p over entries = {worst[p]}, target bound -6log_p(5K)-v_p(24) = {b24}, no-24 bound {-6*L}, slack {worst[p]-b24}")
print("entries:", len(pairs[::step]), "time", time.time()-t0)
