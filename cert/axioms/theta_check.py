#!/usr/bin/env python3
"""cert/axioms/theta_check.py -- independent numerical check of the one axiom
Zeta5.Axioms.chebyshev_theta_asymptotic : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1),
with Mathlib's  theta x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p.

Written for the certification (shares no code with numerics/axioms/pnt_theta.py).  A numpy sieve
gives the primes; θ is summed with math.fsum (exact-rounded) and cross-checked at small x with
mpmath at 40 digits.  Also evaluated at NON-integer and negative real x (Lean's ⌊x⌋₊ is 0 for
x < 0, so θ = 0 there; the filter atTop only sees large x), and compared with the unconditional
Rosser–Schoenfeld-type window |θ(x) − x| < x/(2 log x) for x ≥ 563 (Rosser and Schoenfeld, 1962) as a
consistency check of the implementation.  usage: python3 cert/axioms/theta_check.py"""
import math, numpy as np, mpmath
N = 10**8
s = np.ones(N + 1, dtype=bool); s[:2] = False
for i in range(2, int(N**0.5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0]
print(f"primes <= {N}: {len(P)} (pi(10^8) = 5761455 expected)")
logs = np.log(P.astype(np.float64))
cum = np.cumsum(logs)          # float64 running sum, checked against fsum at checkpoints
def theta(x):
    if x < 0: return 0.0                       # ⌊x⌋₊ = 0
    n = math.floor(x)
    k = np.searchsorted(P, n, side='right')    # primes p with p <= ⌊x⌋
    return float(cum[k-1]) if k else 0.0
# fsum cross-check at 10^6 and mpmath at 10^4
k6 = np.searchsorted(P, 10**6, side='right')
print(f"theta(1e6): cumsum {theta(1e6)!r} vs fsum {math.fsum(logs[:k6])!r}")
mpmath.mp.dps = 40
t4 = mpmath.fsum(mpmath.log(int(p)) for p in P[P <= 10**4])
print(f"theta(1e4): numpy {theta(1e4)!r} vs mpmath {mpmath.nstr(t4, 25)}")
print(f"theta(-5) = {theta(-5)}, theta(1.9) = {theta(1.9)}, theta(2) = {theta(2)} (log 2 = {math.log(2)})")
print(f"{'x':>16} {'theta(x)/x':>14} {'|theta-x|/(x/(2 log x))':>26}")
ok = True
for x in [1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 3.3e7, 1e8, 10**7.5, 12345678.9, 99999999.5]:
    r = theta(x) / x
    w = abs(theta(x) - x) / (x / (2 * math.log(x)))
    if x >= 563 and w >= 1: ok = False
    print(f"{x:16.1f} {r:14.8f} {w:26.6f}")
# approach to 1: max |θ(x)/x − 1| over x in [X, 10^8] at primes (extremes of θ(x)/x − 1 occur just before/at primes)
for X in [10**4, 10**5, 10**6, 10**7]:
    k = np.searchsorted(P, X)
    pp = P[k:].astype(np.float64)
    hi = cum[k:] / pp                     # at x = p
    lo = cum[k-1:-1] / (pp - 1e-9)        # just before p
    print(f"sup_(x in [{X:.0e}, 1e8]) |theta(x)/x - 1| ~ {max(abs(hi-1).max(), abs(lo-1).max()):.6f}")
print("window check (x >= 563):", "OK" if ok else "*** FAIL ***")
