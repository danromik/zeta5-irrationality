"""Large-E regime: every class has many more near zeros than near poles.
Also C1': the minimizing class violates deg <= p+1."""
import random
from core import *
from collections import Counter

def inst(p, rng, kmin, kmax, over_class=None, over_u=None):
    half = p * p // 2 - 1
    S = []
    per = {}
    for a in range(p):
        ta = rng.randint(0, 3)
        cands = [a + p * k for k in range(-half // p, half // p + 1) if abs(a + p * k) <= half]
        rs = rng.sample(cands, min(ta, len(cands)))
        S += rs
    S = sorted(set(S))
    rho = []
    for a in range(p):
        ta = sum(1 for r in S if r % p == a)
        ua = min(p + 1, ta + rng.randint(kmin, kmax))
        if over_class is not None and a == over_class:
            ua = over_u
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
    e = [u[a] - tt[a] for a in range(p)]
    E = min(e) - 4
    v = min(vp(c0, p), vp(c1, p))
    return E, v, u, tt

rng = random.Random(11)
for p in [7, 11, 13]:
    Es = Counter(); fails = 0; tight = 0; n = 0
    for _ in range(60):
        S, rho, W = inst(p, rng, 2, p - 2)
        E, v, u, tt = check(p, S, rho, W)
        Es[E] += 1; n += 1
        if v < E: fails += 1
        if v == E: tight += 1
    print(f"p={p} large-E: E distribution {sorted(Es.items())}; failures {fails}/{n}; tight {tight}")
# C1': class 0 is the minimizer and has u_0 > p+1
for p in [7, 11]:
    fails = 0; n = 0
    for _ in range(60):
        # class 0: t_0 poles; need u_0 = p+2.. with e_0 minimal
        half = p * p // 2 - 1
        S0 = [p * k for k in range(-half // p, half // p + 1) if k != 0 and abs(p * k) <= half]
        t0 = len(S0)
        u0 = p + 2 + rng.randint(0, 3)
        S, rho, W = inst(p, rng, u0 - t0 + 3, u0 - t0 + 5)
        # rebuild with class-0 structure
        S = sorted((set(r for r in S if r % p != 0)) | set(S0))
        rho = [y for y in rho if y % p != 0] + [p * rng.randint(-half // p, half // p) for _ in range(u0)]
        W = [F(1)]
        for y in rho:
            W = mul(W, [F(-y), F(1)])
        E, v, u, tt = check(p, S, rho, W)
        n += 1
        if v < E: fails += 1
    print(f"p={p} C1' (minimizing class has deg > p+1): failures {fails}/{n}")
