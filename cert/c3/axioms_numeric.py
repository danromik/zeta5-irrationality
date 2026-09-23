#!/usr/bin/env python3
"""Independent numerical checks of the two axioms (third certification).
Hermite: w(y) taken from the LEAN definition (Basic.lean `wt`), summed in closed form
sum_{l>=1} l^4 q^l = q(1+11q+11q^2+q^3)/(1-q)^5, q = exp(-2 pi y); Hurwitz zeta from mpmath.
PNT: prime Riemann sums from a numpy sieve, for test functions NOT used by earlier certifiers."""
from mpmath import mp, mpf, pi, exp, quad, zeta, inf, expm1
import numpy as np, math
mp.dps = 40
def wt(y):
    if y == 0: return 1 / pi
    q = exp(-2 * pi * y)
    return (2 * pi)**4 * y**5 / 12 * q * (1 + 11*q + 11*q**2 + q**3) / (-expm1(-2*pi*y))**5
print("HERMITE  a        LHS = int_0^oo w/(y^2+a^2)            RHS = a^4 zeta(5,a) - 1/(2a) - 1/4     diff")
for a in [mpf("0.01"), mpf("0.2"), mpf("0.7"), mpf(1), mpf("1.5"), mpf(4), mpf(25), mpf(1000)]:
    lhs = quad(lambda y: wt(y) / (y**2 + a**2), [0, a / 4, a, 1, 4, 20, inf])
    rhs = a**4 * zeta(5, a) - 1 / (2 * a) - mpf(1) / 4
    print(f"  {float(a):8.3f}  {mp.nstr(lhs, 28):>34s}  {mp.nstr(rhs, 28):>34s}  {mp.nstr(lhs - rhs, 3)}")
print("  int_0^oo w = 5/12 ?", mp.nstr(quad(wt, [0, 1, 4, 20, inf]) - mpf(5) / 12, 3))

X = 3 * 10**7
sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(X**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0].astype(np.float64); L = np.log(P)
def S(a, b, phi, X):
    lo, hi = math.floor(a * X), math.floor(b * X)
    m = (P > lo) & (P <= hi)
    return float(np.sum(phi(P[m] / X) * L[m]) / X)
tests = [
    ("y^2 on [1/2,3/2]", 0.5, 1.5, lambda y: y**2, 13/12),
    ("cos(3y) on [0,2]", 0.0, 2.0, lambda y: np.cos(3*y), math.sin(6)/3),
    ("1_{y<0.7} - 2*1_{y>1.3} on [0.2,2]", 0.2, 2.0, lambda y: (y < 0.7) - 2.0*(y > 1.3), 0.5 - 1.4),
    ("frac(5y) on [0,1]", 0.0, 1.0, lambda y: 5*y - np.floor(5*y), 0.5),
]
print("PNT (prime Riemann sums)")
for name, a, b, phi, I in tests:
    vals = [S(a, b, phi, Xv) for Xv in (10**5, 10**6, 10**7)]
    print(f"  {name:36s} X=1e5 {vals[0]: .6f}  1e6 {vals[1]: .6f}  1e7 {vals[2]: .6f}   integral {I: .6f}")
