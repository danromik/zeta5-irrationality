# MUST-FAIL variant of ob_control.sage: identical except that muPole omits the +1/(2j) term of
# (2.3).  The entry bounds must then fail (they do: 13 failures at K = 40), which shows that the
# p. 12 divided-difference step needs that term.
# Known-answer controls for Zeta5/OuterBasis.lean (outer_local_analysis), exact arithmetic.
# Tests the STUB STATEMENTS of the decomposition, with the SAME definitions as the Lean file:
#   cls, Tset, Eset, dim, rows (4.11) + zero-class rows, c_e, muOver0, muL.
# Usage: sage ob_mustfail.sage K p1 p2 ...
import sys
K = int(sys.argv[1]); n = K//40; N = 3*n; h = 37*n
primes = [int(a) for a in sys.argv[2:]]
Rt.<t> = PolynomialRing(QQ)
RX.<X> = PolynomialRing(QQ)
tail = list(range(N+1, K+1))
W = prod([t+j^2 for j in range(1,N+1)], Rt(1))^5
Dtail = prod([t+j^2 for j in tail], Rt(1))
H5 = [QQ(0)]*(K+1)
for j in range(1,K+1): H5[j] = H5[j-1] + QQ(1)/QQ(j)^5
def muMono(e): return (-1)^e*bernoulli(2*e+2)*(2*e+3)*(2*e+4)*(2*e+5)/24
def muPole(j): return QQ(j)^4*(X - H5[j]) - QQ(1)/4
dden = {}
for j in tail:
    dden[j] = prod([QQ(l)^2-QQ(j)^2 for l in tail if l != j], QQ(1))
def vG(f,p):
    if f == 0: return Infinity
    return min(QQ(c).valuation(p) for c in RX(f).list() if c != 0)
def vq(x,p):
    return Infinity if x == 0 else QQ(x).valuation(p)
def ell(p,A,a): return len([j for j in range(1,A+1) if j%p == a%p or (j+a)%p == 0])
fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        if fails < 30: print("FAIL", msg)
for p in primes:
    m = (p-1)//2
    # OuterHyp
    assert p >= 7 and K < 3*p and 2*K < p^2 and 2*N < p and 5*N <= 2*p-2, p
    mK = K//p
    def cls(r): return r%p if r%p <= m else p - r%p
    Tset = {c: [r for r in tail if cls(r) == c] for c in range(m+1)}
    def dim(c): return mK if c == 0 else ell(p,K,c) - (1 if c <= N else 0)
    # (T1) counts
    for c in range(m+1):
        check(len(Tset[c]) == dim(c), ("card Tset", p, c))
    for a in range(1,m+1):
        E = [r for r in Tset[a] if r > p]
        check(len(E) == max(0, ell(p,K,a)-2), ("card Eset", p, a))
        S = [r for r in Tset[a] if not r > p]
        check(set(S) <= {a, p-a}, ("Tset minus Eset", p, a))
    check(Tset[0] == ([p] if mK == 1 else [p,2*p] if mK == 2 else []), ("Tset0", p))
    check(sum(dim(c) for c in range(m+1)) == h, ("sum dim", p))
    # rows
    def P(a): return prod([t+r^2 for r in tail if cls(r) != a], Rt(1))
    def q(a,i):
        if a == 0: return Rt(1) if i == 0 else t + p^2
        l = ell(p,K,a); l2 = max(0,l-2)
        if i+2 < l: return (t+a^2)^i
        E = prod([t+r^2 for r in Tset[a] if r > p], Rt(1))
        return E*(t+a^2)^(i-l2)
    rows = []; labels = []; wts = []
    for a in range(m+1):
        for i in range(dim(a)):
            rows.append(P(a)*q(a,i)); labels.append((a,i))
            if a == 0:
                w = -1 if mK <= 1 else (-4 if i == 0 else 0)
            else:
                l = ell(p,K,a); d = 1 if a <= N else 0
                w = min(0, 2*i+6*d-l-4) if i+2 < l else 0
            wts.append(w)
    check(len(rows) == h, ("row count", p))
    # (T2) reduction mod p = hermite
    Fp = GF(p); Rp.<s> = PolynomialRing(Fp)
    for (a,i), f in zip(labels, rows):
        herm = prod([(s + Fp(c)^2)^dim(c) for c in range(m+1) if c != a], Rp(1))*(s+Fp(a)^2)^i
        check(Rp(f.change_ring(ZZ).change_ring(Fp)) == herm, ("hermite", p, a, i))
        check(f.degree() < h and f.is_monic(), ("deg/monic", p, a, i))
    U = matrix(QQ, h, h, lambda i,j: rows[i][j])
    check(U.det() != 0 and QQ(U.det()).valuation(p) == 0, ("unimodular", p))
    # c_e and mu0
    ce = {}
    def c_of(e):
        if e not in ce:
            if e < 2*p-3: ce[e] = 0
            else:
                x = p*muMono(e)
                check(vq(x,p) >= 0, ("v(mu) >= -1", p, e))
                ce[e] = ZZ(Mod(x.numerator(),p)*Mod(x.denominator(),p)^(-1))
        return ce[e]
    for e in range(0, 4*p+10):
        check(vq(muMono(e) - c_of(e)/p, p) >= 0, ("mu0 integral", p, e))
        if e < 2*p-3: check(vq(muMono(e),p) >= 0, ("mu integral small e", p, e))
    # (T4) muPole valuations
    for r in range(1, K+1):
        v = vG(muPole(r), p)
        check(v >= -5, ("muPole -5", p, r))
        if r < p: check(v >= 0, ("muPole 0", p, r))
        if r % p == 0: check(v >= -1, ("muPole -1", p, r))
    # (T3) entries
    def split(A):
        quo, rem = A.quo_rem(Dtail)
        poly0 = sum(c*(muMono(d) - c_of(d)/p) for d,c in enumerate(quo.list()))
        lam = sum(c*c_of(d) for d,c in enumerate(quo.list()))
        res = RX(0)
        for r in tail:
            cr = A(-r^2)/dden[r]
            if cr != 0: res += cr*muPole(r)
        return poly0, res, lam, quo
    Lmat = matrix(QQ, h, h)
    nent = 0
    for u in range(h):
        for v in range(u, h):
            (a,i),(b,j) = labels[u], labels[v]
            A = W*rows[u]*rows[v]
            poly0, res, lam, quo = split(A)
            Lmat[u,v] = lam; Lmat[v,u] = lam
            check(vq(poly0,p) >= 0, ("poly part integral", p, labels[u], labels[v]))
            check(all(c in ZZ for c in quo.list()), ("quotient integer", p))
            check(lam in ZZ, ("L integer", p))
            if a != b:
                check(res == 0, ("cross class residue", p, labels[u], labels[v]))
            elif a >= 1:
                l = ell(p,K,a); d = 1 if a <= N else 0
                if i+2 < l and j+2 < l:
                    check(vG(res,p) >= i+j+6*d-l-4, ("2a", p, labels[u], labels[v], vG(res,p)))
                else:
                    check(vG(res,p) >= 0, ("2b", p, labels[u], labels[v], vG(res,p)))
            else:
                bound = {(1,0,0): -1, (2,0,0): -3, (2,0,1): -1, (2,1,1): 1}[(mK,i,j)]
                check(vG(res,p) >= bound, ("zero", p, labels[u], labels[v], vG(res,p)))
            check(vG(poly0 + res, p) >= (wts[u]+wts[v])/2, ("final", p, labels[u], labels[v]))
            nent += 1
    rp = max(0, K+4*N-2*p+2)
    L0 = matrix(QQ, h, h, lambda i,j: split(W*t^(i+j))[2])
    for i in range(h):
        for j in range(h):
            if i+j < K-6*N+2*p-3: check(L0[i,j] == 0, ("L0 zero", p, i, j))
    check(L0.rank() <= rp, ("rank L0", p))
    check(Lmat == U*L0*U.transpose(), ("L = U L0 U^T", p))
    check(Lmat.rank() <= rp, ("rank L", p))
    # (T7) residue formula, a few random S, F
    import random
    random.seed(p)
    for trial in range(5):
        S = [r for r in tail if random.random() < 0.3]
        F = Rt([random.randint(-5,5) for _ in range(random.randint(1,8))])
        A = F*prod([t+r^2 for r in tail if r not in S], Rt(1))
        for r in tail:
            lhs = A(-r^2)/dden[r]
            rhs = (F(-r^2)/prod([QQ(s)^2-QQ(r)^2 for s in S if s != r], QQ(1))) if r in S else 0
            check(lhs == rhs, ("residue formula", p, r))
    print("K=%d p=%d: h=%d mK=%d entries=%d rankL=%d r_p=%d  cumulative fails=%d" % (K,p,h,mK,nent,Lmat.rank(),rp,fails))
print("TOTAL FAILS:", fails)
