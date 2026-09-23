from sympy import Rational, factorial, binomial, Poly, symbols, div, diff, expand, prod, bernoulli as sB
from l33check import *
x = symbols('x')

def coeff4(P):
    return Poly(P, x).coeff_monomial(x**4)

# 1. tau(Delta S) = [x^4] S, random S
import random
random.seed(1)
ok=True
for trial in range(30):
    deg = random.randint(0, 14)
    S = sum(Rational(random.randint(-9,9), random.randint(1,9))*x**e for e in range(deg+1))
    P = expand(S.subs(x, x+1) - S)
    if tau(P) != coeff4(S): ok=False; print("FAIL", S)
print("tau(DeltaS)=[x^4]S:", ok)

# 2,3,4: closed forms for g_k
def e4recip(lo, hi):
    vals = [Rational(1, i) for i in range(lo, hi+1)]
    # e_4 of vals
    from itertools import combinations
    return sum(a*b*c*d for a,b,c,d in combinations(vals, 4))

bad = 0
for K in [2,3,4,5]:
    poles = [r for r in range(-K, K+1) if r != 0]
    Qx = prod([(x - r) for r in poles])
    for k in range(0, 5*K):
        A = expand(binomx(x+K, k))
        Pq, Rm = div(Poly(A, x), Poly(Qx, x))
        if k <= 2*K:
            if Pq.degree() > 0: bad += 1; print("quot not const", K, k)
        else:
            m = k - 2*K - 1
            expect = expand(x*binomx(x-K-1, m)*factorial(m)/factorial(k))
            if expand(Pq.as_expr() - expect) != 0: bad += 1; print("quot mismatch", K, k)
            t = factorial(K)**2 * tau(Pq.as_expr())
            closed = (-1)**m / binomial(k, K) * ( Rational(k-K+1, k-2*K+1)*e4recip(K+1, k-K+1) - Rational(k-K, k-2*K)*e4recip(K+1, k-K) )
            if t != closed: bad += 1; print("closed form mismatch", K, k, t, closed)
            # S formula check
            a = K+1
            S = (m+1)*binomx(x-a, m+2) + (a+m)*binomx(x-a, m+1)
            if expand(S.subs(x,x+1) - S - x*binomx(x-a, m)) != 0: bad += 1; print("S mismatch")
print("closed-form checks bad =", bad)
