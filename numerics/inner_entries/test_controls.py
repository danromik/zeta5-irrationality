"""Controls: distribution of E; must-fail variants.
C1: violate degree hypothesis (u_a > p+1 in some class)  -> T4 should fail sometimes
C2: violate unit-difference hypothesis (same-class poles differing by p^2) -> should fail sometimes
C3: claim E+1 instead of E  -> fails whenever tight
"""
import random
from core import *
from collections import Counter

def instance(p, rng, overdeg=False, closepoles=False):
    half = p * p // 2 - 1
    nS = rng.randint(1, 3 * p)
    S = sorted(rng.sample(range(-half, half + 1), nS))
    if closepoles:
        a = rng.randrange(p)
        base = a + p * rng.randint(-2, 2)
        extra = [base, base + p * p, base - p * p, base + 2 * p * p]
        S = sorted(set(S) | set(extra))
    rho = []
    for a in range(p):
        ta = sum(1 for r in S if r % p == a)
        hi = p + 1 if not overdeg else p + 8
        lo = max(0, ta - 1)
        ua = rng.randint(lo, min(hi, ta + rng.randint(0, 5) + (8 if overdeg else 0)))
        if overdeg and a == 0:
            ua = p + 2 + rng.randint(0, 6)
        for _ in range(ua):
            rho.append(a + p * rng.randint(-half // p, half // p))
    W = [F(rng.choice([1, -1]))]
    for y in rho:
        W = mul(W, [F(-y), F(1)])
    return S, rho, W

def check(p, S, rho, W):
    c0, c1, P, res = tauExtOf_X(S, W)
    u = [sum(1 for y in rho if y % p == a) for a in range(p)]
    tt = [sum(1 for r in S if r % p == a) for a in range(p)]
    E = min(u[a] - tt[a] for a in range(p)) - 4
    v = min(vp(c0, p), vp(c1, p))
    return E, v

rng = random.Random(7)
for p in [7, 11]:
    Es = Counter(); fails = 0; n = 0
    for _ in range(80):
        S, rho, W = instance(p, rng)
        E, v = check(p, S, rho, W)
        Es[E] += 1; n += 1
        if v < E: fails += 1
    print(f"p={p} baseline: E distribution {sorted(Es.items())}; failures {fails}/{n}")
    f1 = 0; n1 = 0
    for _ in range(60):
        S, rho, W = instance(p, rng, overdeg=True)
        E, v = check(p, S, rho, W)
        n1 += 1
        if v < E: f1 += 1
    print(f"p={p} C1 (u_0 > p+1): failures {f1}/{n1}")
    f2 = 0; n2 = 0
    for _ in range(60):
        S, rho, W = instance(p, rng, closepoles=True)
        E, v = check(p, S, rho, W)
        n2 += 1
        if v < E: f2 += 1
    print(f"p={p} C2 (poles differing by p^2): failures {f2}/{n2}")
    f3 = 0; n3 = 0
    for _ in range(60):
        S, rho, W = instance(p, rng)
        E, v = check(p, S, rho, W)
        n3 += 1
        if v < E + 1: f3 += 1
    print(f"p={p} C3 (claim E+1): failures {f3}/{n3}")
