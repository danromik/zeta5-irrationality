"""Exact-rational helpers for testing the InnerEntries decomposition.
Polynomials: dense lists of Fractions, low-to-high."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import random

@lru_cache(maxsize=None)
def bern(n):
    if n == 0:
        return F(1)
    s = F(0)
    for j in range(n):
        s += comb(n + 1, j) * bern(j)
    return -s / (n + 1)

@lru_cache(maxsize=None)
def kappa(d):
    if d < 3:
        return F(0)
    return F(d * (d - 1) * (d - 2)) * bern(d - 3) / 24

@lru_cache(maxsize=None)
def H5(m):
    if m <= 0:
        return F(0)
    return H5(m - 1) + F(1, m ** 5)

def dIdx(r):
    return r if r >= 0 else -r - 1

INF = 10 ** 9
def vp(x, p):
    x = F(x)
    if x == 0:
        return INF
    n, d = x.numerator, x.denominator
    v = 0
    while n % p == 0:
        n //= p; v += 1
    while d % p == 0:
        d //= p; v -= 1
    return v

def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0)) for i in range(n)])

def scal(c, a):
    return trim([F(c) * x for x in a])

def mul(a, b):
    if not a or not b:
        return []
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            r[i + j] += x * y
    return trim(r)

def divmod_monic(a, b):
    a = [F(x) for x in a]
    b = trim(b)
    assert b[-1] == 1
    q = [F(0)] * max(0, len(a) - len(b) + 1)
    for k in range(len(a) - len(b), -1, -1):
        c = a[k + len(b) - 1]
        q[k] = c
        if c != 0:
            for i, y in enumerate(b):
                a[i + k] -= c * y
    return trim(q), trim(a[:len(b) - 1])

def ev(a, x):
    s = F(0)
    for c in reversed(a):
        s = s * x + c
    return s

def deriv(a):
    return trim([i * a[i] for i in range(1, len(a))])

def comp_lin(a, c0, c1):
    """a(c0 + c1 z)"""
    res = []
    lin = [F(c0), F(c1)]
    powr = [F(1)]
    for c in a:
        res = add(res, scal(c, powr))
        powr = mul(powr, lin)
    return res

def tau(P):
    return sum((P[d] * kappa(d) for d in range(len(P))), F(0))

def Tpoly(S):
    r = [F(1)]
    for s in S:
        r = mul(r, [F(-s), F(1)])
    return r

def tauExtOf_X(S, W):
    """returns (c0, c1): tau_X(W/Q) = c0 + c1 X, Q = prod_{r in S}(x-r)."""
    Q = Tpoly(S)
    P, Rm = divmod_monic(W, Q)
    dQ = deriv(Q)
    c0 = tau(P)
    c1 = F(0)
    res = {}
    for r in S:
        cr = ev(Rm, F(r)) / ev(dQ, F(r))
        res[r] = cr
        c0 += cr * H5(dIdx(r))
        c1 -= cr
    return c0, c1, P, res
