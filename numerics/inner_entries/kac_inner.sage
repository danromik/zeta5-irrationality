# Known-answer control for InnerEntries on the paper's basis (4.5), with L0 (the size of the
# zero class) a free parameter.  Usage: sage kac_inner.sage K p L0 [step]
# Checks, for every entry (u,v):
#  T5  pullback:  mu_X(D_N^5 E_u E_v / D_tail)  ==  tauExtOf_X(S, (-1)^h x^5 A(-x^2)),  S = {+-j : N<j<=K}
#  T6  class count exponent  min_a (u_a - t_a) - 4  ==  min((4.3), min_{1<=c<=m} (4.2))
#  T4  v_p^G(entry) >= that exponent
#  TW  2*exponent >= 2w_u + 2w_v   (the weights)
import sys
K = int(sys.argv[1]); p = int(sys.argv[2]); L0 = int(sys.argv[3])
n = K//40; N = 3*n; h = 37*n
Rt = PolynomialRing(QQ,'t'); t = Rt.gen()
Rx = PolynomialRing(QQ,'x'); x = Rx.gen()
RX = PolynomialRing(QQ,'X'); X = RX.gen()
tail = list(range(N+1,K+1))
DN = prod([t+QQ(j)**2 for j in range(1,N+1)], Rt(1))
Dtail = prod([t+QQ(j)**2 for j in tail], Rt(1)); W5 = DN**5
H5=[QQ(0)]*(K+1)
for j in range(1,K+1): H5[j]=H5[j-1]+QQ(1)/QQ(j)**5
dden={}
for j in tail:
    vv=QQ(1)
    for l in tail:
        if l!=j: vv*= QQ(l)**2-QQ(j)**2
    dden[j]=vv
def MUe(e): return QQ(-1)**e*bernoulli(2*e+2)*(2*e+3)*(2*e+4)*(2*e+5)/24
def entry_mu(num):
    quo,rem = num.quo_rem(Dtail)
    a=QQ(0)
    for d,c in enumerate(quo.list()):
        if c!=0: a+=c*MUe(d)
    b=QQ(0)
    for j in tail:
        cj=num(-QQ(j)**2)/dden[j]
        if cj!=0:
            a+=cj*(-QQ(j)**4*H5[j]-QQ(1)/4+QQ(1)/(2*j)); b+=cj*QQ(j)**4
    return a+b*X
def kappa(d): return QQ(0) if d<3 else QQ(d*(d-1)*(d-2))*bernoulli(d-3)/24
def dIdx(r): return r if r>=0 else -r-1
def H5x(m):
    return sum([QQ(1)/QQ(v)**5 for v in range(1,m+1)], QQ(0))
S = sorted([j for j in tail]+[-j for j in tail])
Q = prod([x-r for r in S], Rx(1)); dQ = Q.derivative()
H5d = {r: H5x(dIdx(r)) for r in S}
def tauExtOf(Wx):
    P, R = Wx.quo_rem(Q)
    c0 = sum([c*kappa(d) for d,c in enumerate(P.list())], QQ(0)); c1 = QQ(0)
    for r in S:
        cr = R(r)/dQ(r)
        c0 += cr*H5d[r]; c1 -= cr
    return c0 + c1*X
def vG(f):
    if f==0: return +Infinity
    return min(QQ(c).valuation(p) for c in f.list() if c!=0)

m=(p-1)//2; mN=N//p; mK=K//p
def ell(A,a): return len([j for j in range(1,A+1) if (j-a)%p==0 or (j+a)%p==0])
lK={a:ell(K,a) for a in range(1,m+1)}; lN={a:ell(N,a) for a in range(1,m+1)}
b={a:3*lN[a] for a in range(1,m+1)}
tot = h - L0 + 3*(N-mN); T = tot//m; E = tot - m*T
order = sorted(range(1,m+1), key=lambda a:(-lK[a],a))
eps={a:0 for a in range(1,m+1)}
for a in order[:E]: eps[a]=1
L={a:T-b[a]+eps[a] for a in range(1,m+1)}; L[0]=L0
Z={a:T+eps[a] for a in range(1,m+1)}
assert min(L.values())>=0 and sum(L.values())==h
cap = min([2*Z[c]-(lK[c]+4) for c in range(1,m+1)])
labs=[]; rows=[]; w2=[]
for a in range(0,m+1):
    for i in range(L[a]):
        poly = prod([(t+QQ(c)**2)**L[c] for c in range(0,m+1) if c!=a], Rt(1))*(t+QQ(a)**2)**i
        rows.append(poly); labs.append((a,i))
        w2.append(min(4*i+12*mN-2*mK+1, cap) if a==0 else 2*i+2*b[a]-lK[a]-4)
def nu(u,c):
    a,i = labs[u]
    return i if c==a else L[c]
def roots_of_W(u,v):
    # multiset of x-roots of (-1)^h x^5 D_N(-x^2)^5 E_u(-x^2) E_v(-x^2)
    rs = [0]*5
    for j in range(1,N+1): rs += [j,-j]*5
    for c in range(0,m+1):
        k = nu(u,c)+nu(v,c)
        rs += ([c,-c] if c>0 else [0,0])*k
    return rs
tcount = [sum(1 for r in S if r%p==a) for a in range(p)]
def exp_class(u,v):
    rs = roots_of_W(u,v)
    uc = [0]*p
    for y in rs: uc[y%p]+=1
    return min(uc[a]-tcount[a] for a in range(p)) - 4, max(uc)
def exp_paper(u,v):
    e43 = 2*nu(u,0)+2*nu(v,0)+12*mN-2*mK+1
    e42 = min(nu(u,c)+nu(v,c)+6*lN[c]-lK[c]-4 for c in range(1,m+1))
    return min(e43, e42)
bad={'T5':0,'T6':0,'T4':0,'TW':0}; tight=0; cnt=0; maxu=0
step = int(sys.argv[4]) if len(sys.argv)>4 else 1
for u in range(0,h,step):
    for v in range(u,h,step):
        A = W5*rows[u]*rows[v]
        e_mu = entry_mu(A)
        Wx = (-1)**h * x**5 * A(-x**2)
        e_tau = tauExtOf(RX(e_mu.list()) if False else Wx)
        if RX(e_tau) != e_mu: bad['T5']+=1
        ec, mu_ = exp_class(u,v); maxu=max(maxu,mu_)
        ep = exp_paper(u,v)
        if ec != ep: bad['T6']+=1
        vv = vG(e_mu)
        if vv < ec: bad['T4']+=1
        if vv == ec: tight+=1
        if 2*ec < w2[u]+w2[v]: bad['TW']+=1
        cnt+=1
print("K=%d p=%d L0=%d h=%d  entries tested %d  failures %s  tight(v==exponent) %d  max class zero count %d (p+1=%d)"%(K,p,L0,h,cnt,bad,tight,maxu,p+1))
