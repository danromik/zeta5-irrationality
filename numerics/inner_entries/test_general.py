"""Tests of the proposed InnerEntries decomposition on random instances.
T1  Raabe:          p^4 tau(P) = sum_{a<p} tau(P(a+pz))
T2  residue bound:  v(c_r) >= u_a - t_a + 1   (a = r mod p)
T3  class bound:    v(tau(P(a+pz))) >= min(e_a, min_{far r} v(c_r) + 2)
T4  general:        v^G(tauExtOf X S W) >= min_a e_a - 4
"""
import random, sys
from core import *

def run(p, seed, trials=60, spread=None):
    random.seed(seed)
    bad = {'T1': 0, 'T2': 0, 'T3': 0, 'T4': 0}
    tight4 = 0
    minslack4 = INF
    for t in range(trials):
        half = p * p // 2 - 1
        # poles: random set, |r| <= half  (so same-class differences have v_p = 1)
        nS = random.randint(1, 3 * p)
        S = sorted(random.sample(range(-half, half + 1), nS))
        # zeros: per class, choose a count between 0 and p+1, biased to exceed poles
        rho = []
        for a in range(p):
            ta = sum(1 for r in S if r % p == a)
            ua = random.randint(max(0, ta - 1), min(p + 1, ta + random.randint(0, 5)))
            for _ in range(ua):
                rho.append(a + p * random.randint(-half // p, half // p))
        eps = random.choice([1, -1])
        W = [F(eps)]
        for y in rho:
            W = mul(W, [F(-y), F(1)])
        c0, c1, P, res = tauExtOf_X(S, W)
        u = [sum(1 for y in rho if y % p == a) for a in range(p)]
        tt = [sum(1 for r in S if r % p == a) for a in range(p)]
        e = [u[a] - tt[a] for a in range(p)]
        E = min(e) - 4
        # T1
        lhs = F(p) ** 4 * tau(P)
        pis = [comp_lin(P, a, p) for a in range(p)]
        rhs = sum((tau(pi) for pi in pis), F(0))
        if lhs != rhs:
            bad['T1'] += 1
        # T2
        for r, cr in res.items():
            if vp(cr, p) < e[r % p] + 1:
                bad['T2'] += 1
        # T3
        for a in range(p):
            far = [vp(cr, p) for r, cr in res.items() if r % p != a]
            f = min(far) if far else INF
            if vp(tau(pis[a]), p) < min(e[a], f + 2):
                bad['T3'] += 1
        # T4
        v = min(vp(c0, p), vp(c1, p))
        if v < E:
            bad['T4'] += 1
        minslack4 = min(minslack4, v - E)
        if v == E:
            tight4 += 1
    return bad, tight4, minslack4

if __name__ == '__main__':
    for p in [7, 11, 13]:
        for seed in range(3):
            bad, tight, ms = run(p, 1000 * p + seed, trials=40)
            print(f"p={p} seed={seed}: failures {bad}; tight(T4 equality) {tight}/40; min slack {ms}")
            sys.stdout.flush()
