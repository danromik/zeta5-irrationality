"""Known-answer controls for Zeta5.PrimeSum.eq_5_7_uniformity.

Computes, in exact arithmetic, the three errors of the statement:
  E1 = gamma_p^in - p*Gam(K/p)               over inner primes (K/M < p <= K/3)
  E2 = v_p(S_K) - p*NR(K/p)                  over inner primes
  E3 = -(v_p(S_K) + gamma_p^out) - K*Tout(p/K)  over K/3 < p <= 2h
Everything from the DEFINITIONS in Zeta5/Basic.lean and Zeta5/AppendixB.lean
(gammaIn with w2 / w2zero / Int.toNat; Gam with the z-integral done exactly
by breakpoints; NR, JR; gammaOut; R0, dRank, Tout).  vS by Legendre directly
on the factorials of (2.5) (sum over all a>=1, no cutoff assumptions).
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from sympy import primerange

alpha = Fr(3, 40); lam = Fr(37, 40); H = Fr(23, 20)

def floor(q):  # exact floor of a Fraction
    return q.numerator // q.denominator

def fract(q):
    return q - floor(q)

def ellR(x, z):
    return floor(x - z) + floor(x + z) + 1

def Gam_exact(x):
    """(5.4) with the z-integral computed exactly: integrand is a step function
    of z on (0,1/2) with breakpoints among {fract(y), 1-fract(y)} for y in {x, alpha x}."""
    T = floor(2 * H * x)
    s = H * x - Fr(T, 2)
    q = floor(2 * x)
    nplus = (2 * x - q) / 2
    bps = {Fr(0), Fr(1, 2)}
    for y in (x, alpha * x):
        for c in (fract(y), 1 - fract(y)):
            if 0 < c < Fr(1, 2):
                bps.add(c)
    bps = sorted(bps)
    integ = Fr(0)
    for lo, hi in zip(bps, bps[1:]):
        z = (lo + hi) / 2
        b = 3 * ellR(alpha * x, z)
        l = ellR(x, z)
        integ += (hi - lo) * (T - b) * (T + b - l - 5)
    return integ + s * (2 * T - q - 5) + max(Fr(0), s - nplus)

def JR(u):
    m = floor(2 * u)
    return m * u - Fr(m * (m + 1), 4)

def NR(x):
    return 2 * lam * x * floor(x) - 12 * lam * x * floor(alpha * x) - 2 * JR(lam * x)

def vp_fact(m, p):
    s = 0; q = p
    while q <= m:
        s += m // q; q *= p
    return s

def vS(n, p):
    K, N, h = 40 * n, 3 * n, 37 * n
    v = 2 * h * vp_fact(K, p) + (h - 1) * (2 if p == 2 else 0)
    v -= 12 * h * vp_fact(N, p)
    # sum_{i=1}^{h-1} 2 v_p((2i)!) ; use Legendre summed over i in closed form per power
    tot = 0; q = p
    while q <= 2 * (h - 1):
        # sum_{i=1}^{h-1} floor(2i/q)
        tot += sum_floor_2i(h - 1, q)
        q *= p
    v -= 2 * tot
    return v

def sum_floor_2i(L, q):
    # sum_{i=1}^{L} floor(2i/q), exact, O(L/q + 1) via blocks
    # direct numpy for simplicity
    # independent of the k-sum formula proved in Lean: floor(2i/q) = (2i - (2i mod q))/q,
    # and 2i mod q is q-periodic in i.
    full, rem = divmod(L, q)
    per = np.arange(1, q + 1, dtype=np.int64)
    per_sum = int(((2 * per) % q).sum())
    part = np.arange(1, rem + 1, dtype=np.int64)
    part_sum = int(((2 * part) % q).sum())
    modsum = full * per_sum + part_sum
    tot2i = L * (L + 1)
    assert (tot2i - modsum) % q == 0
    return (tot2i - modsum) // q

def gamma_in(n, M, p):
    """(4.4)-(4.8) exactly.  Returns (gamma, T, E)."""
    K, N, h = 40 * n, 3 * n, 37 * n
    L0 = 4 * M + 10
    m = (p - 1) // 2
    mN = N // p; mK = K // p
    target = h - L0 + 3 * (N - mN)
    T, E = divmod(target, m)
    a = np.arange(1, m + 1, dtype=np.int64)
    ellK = (K + p - a) // p + (K + a) // p
    ellN = (N + p - a) // p + (N + a) // p
    b = 3 * ellN
    # eps: first E classes in decreasing order of ellK (stable; ties arbitrary)
    order = np.argsort(-ellK, kind='stable')
    eps = np.zeros(m, dtype=np.int64)
    eps[order[:E]] = 1
    L = T - b + eps
    assert (L >= 0).all()
    # sum_{i<L} (2i + 2b - ellK - 4) = L(L-1) + L(2b - ellK - 4)
    ordinary = int((L * (L - 1) + L * (2 * b - ellK - 4)).sum())
    Z = T + eps
    inner_min = int((2 * Z - ellK - 4).min())
    zero = 0
    for i in range(L0):
        zero += min(4 * i + 12 * mN - 2 * mK + 1, inner_min)
    return ordinary + zero, T, E

def gammaOut(n, p):
    K, N = 40 * n, 3 * n
    if K < p:
        return 0
    v = K % p
    u = max(0, N + v - p + 1)
    t = min(N, v) + u
    r = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * t - 1 - min(r, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * t - min(r, p + u)

def R0(y):
    if y < Fr(1, 2):
        return 8 - 9 * y - 8 * alpha - 5 * min(alpha, 1 - 2 * y) - 5 * max(Fr(0), 1 + alpha - 3 * y)
    if y < 1:
        return (7 * (1 - y) - 6 * min(alpha, 1 - y) - 6 * max(Fr(0), 1 + alpha - 2 * y)
                + max(Fr(0), 1 + 4 * alpha - 2 * y))
    return Fr(0)

def dRank(y):
    if y < Fr(1, 2):
        return max(Fr(0), 1 + 4 * alpha - 3 * y - max(Fr(0), 1 + alpha - 3 * y))
    return Fr(0)

def Tout(y):
    return (R0(y) - dRank(y) - 2 * lam * floor(1 / y)
            + sum(max(Fr(0), 2 * lam - j * y) for j in range(1, 6)))

def run(n, M, do_inner=True):
    K, N, h = 40 * n, 3 * n, 37 * n
    out = {}
    if do_inner:
        e1 = []; e2 = []
        for p in primerange(K // M + 1, K // 3 + 1):
            if not (K < p * M and 3 * p <= K):
                continue
            x = Fr(K, p)
            g, T, E = gamma_in(n, M, p)
            e1.append((float(g - p * Gam_exact(x)), p))
            e2.append((float(vS(n, p) - p * NR(x)), p))
        out['E1'] = (min(e1), max(e1), len(e1))
        out['E2'] = (min(e2), max(e2), len(e2))
    e3 = []
    for p in primerange(2, 2 * h + 1):
        if not (K < 3 * p):
            continue
        y = Fr(p, K)
        val = -(vS(n, p) + gammaOut(n, p)) - K * Tout(y)
        e3.append((float(val), p))
    out['E3'] = (min(e3), max(e3), len(e3))
    return out

if __name__ == '__main__':
    M = int(sys.argv[1]); ns = [int(a) for a in sys.argv[2:]]
    for n in ns:
        print('M', M, 'K', 40 * n, 'size_ok(K>=200M^2)', 40 * n >= 200 * M * M, run(n, M), flush=True)
