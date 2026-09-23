from sympy import Rational, factorial, Poly, symbols, div, diff, expand, prod
from l33check import *
t, x, X = symbols('t x X')
def muMono(e): return (-1)**e * B(2*e+2)*(2*e+3)*(2*e+4)*(2*e+5)/24
def muPole(j): return j**4*(X - H5(j)) - Rational(1,4) + Rational(1, 2*j)
def muOver(N, K, Bt):
    Dtail = prod([(t + j**2) for j in range(N+1, K+1)])
    q, r = div(Poly(Bt, t), Poly(Dtail, t))
    val = sum(c*muMono(e) for (e,), c in q.terms()) if not q.is_zero else 0
    Dd = diff(Dtail, t)
    for j in range(N+1, K+1):
        res = Rational(r.as_expr().subs(t, -j**2)) / Rational(Dd.subs(t, -j**2))
        val += res*muPole(j)
    return expand(val)
def tauExtOf(K, U):
    poles = [r for r in range(-K, K+1) if r != 0]
    Qx = prod([(x - r) for r in poles])
    q, rm = div(Poly(U, x), Poly(Qx, x))
    val = tau(q.as_expr())
    Qd = diff(Qx, x)
    for r in poles:
        c = Rational(rm.as_expr().subs(x, r))/Rational(Qd.subs(x, r))
        val += c*(H5(dIdx(r)) - X)
    return expand(val)
import random
random.seed(3)
bad=0
for (N,K) in [(1,3),(1,4),(2,5)]:
    DN = prod([(t + j**2) for j in range(1, N+1)]) + 0*t
    for trial in range(6):
        deg = random.randint(0, 3*K)
        Bt = sum(Rational(random.randint(-9,9), random.randint(1,5))*t**e for e in range(deg+1))
        lhs = muOver(N, K, Bt)
        U = expand(x**5 * Bt.subs(t, -x**2) * DN.subs(t, -x**2))
        rhs = expand((-1)**K * tauExtOf(K, U))
        if expand(lhs - rhs) != 0: bad += 1; print("MISMATCH", N, K, Bt, lhs, rhs)
print("pullback mismatches:", bad)
