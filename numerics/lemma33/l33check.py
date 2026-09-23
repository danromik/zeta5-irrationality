from fractions import Fraction as F
from sympy import bernoulli as sB, Rational, factorial, binomial, Poly, symbols, div, diff, expand, prod
import math, itertools, sys
x = symbols('x')

def B(k):
    # Mathlib convention: B_1 = -1/2
    if k == 1: return Rational(-1,2)
    return Rational(sB(k))

def Lfun(P):
    P = Poly(P, x)
    return sum(c*B(k) for (k,), c in P.terms())

def tau(P):
    return Lfun(diff(P, x, 3))/24

def vp(q, p):
    q = Rational(q)
    if q == 0: return None
    num, den = q.p, q.q
    v = 0
    while num % p == 0: num//=p; v+=1
    while den % p == 0: den//=p; v-=1
    return v

def flog(p, n):
    # Nat.log p n
    if n < p: return 0
    k=0; m=1
    while m*p <= n: m*=p; k+=1
    return k

def H5(m): return sum(Rational(1, v**5) for v in range(1, m+1))
def dIdx(r): return r if r>=0 else -r-1

def binomx(y, k):
    return prod([(y - i) for i in range(k)]) / factorial(k) if k>0 else Rational(1)

def tauX_g(K, A):
    poles = [r for r in range(-K, K+1) if r != 0]
    Qx = prod([(x - r) for r in poles])
    Kf2 = factorial(K)**2
    num = expand(Kf2*A)
    Pq, Rm = div(Poly(num, x), Poly(Qx, x))
    t0 = tau(Pq.as_expr())
    Qd = diff(Qx, x)
    cs = {}
    for r in poles:
        cs[r] = Rational(num.subs(x, r)) / Rational(Qd.subs(x, r))
    c0 = t0 + sum(cs[r]*H5(dIdx(r)) for r in poles)
    c1 = -sum(cs.values())
    return c0, c1, t0, cs

if __name__ == "__main__":
    bad = []
    for K in [2,3,4,5,6,7,8]:
        for d in [2*K, 3*K, 5*K-1]:
            for p in [2,3,5,7,11,13]:
                L = flog(p, max(2*K, d+1))
                bound6 = -6*L
                worst = 10**9
                for k in range(0, d+1):
                    A = binomx(x+K, k)
                    c0, c1, t0, cs = tauX_g(K, A)
                    for c in (c0, c1):
                        v = vp(c, p)
                        if v is not None: worst = min(worst, v)
                print(K, d, p, "min v =", worst, "bound(no24) =", bound6, "slack", worst-bound6, "v24", vp(24,p))
                if worst < bound6: bad.append((K,d,p,worst,bound6))
    print("violations of no-24 bound:", bad)
