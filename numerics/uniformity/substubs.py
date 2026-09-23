"""Numerical tests of the intermediate statements (sub-lemma stubs) of Uniformity.lean,
in exact arithmetic, before proving them."""
import sys
from fractions import Fraction as Fr
import numpy as np
from sympy import primerange
from controls import (floor, fract, ellR, Gam_exact, NR, vS, gamma_in, gammaOut, R0, dRank,
                      Tout, alpha, lam, H, sum_floor_2i)

def d0(u): return min(u, 1 - u)
def e0(u): return 1 if u <= Fr(1, 2) else -1

def IT(x, T):
    dF, eF = d0(fract(x)), e0(fract(x))
    dG, eG = d0(fract(alpha * x)), e0(fract(alpha * x))
    U = T - 6 * alpha * x + 6 * eG * dG
    V = T + 6 * alpha * x - 2 * x - 5 - 6 * eG * dG + 2 * eF * dF
    return (U * V / 2 + (3 * eG * U - 3 * eG * V - 9) * dG + (-(eF * U)) * dF
            + 3 * eF * eG * min(dG, dF))

def check(n, M):
    K, N, h = 40 * n, 3 * n, 37 * n
    L0 = 4 * M + 10
    worst = {'rho/M2': Fr(0), 'Z0/M2': Fr(0), 'delta/M': Fr(0), 'Ggap/m': Fr(0), 'Gam_split': 0,
             'IT_succ': 0, 'eps_sum': 0, 'U_eq': 0, 'Tcase': set(), 'bound/M2': Fr(0)}
    for p in primerange(K // M + 1, K // 3 + 1):
        if not (K < p * M and 3 * p <= K):
            continue
        x = Fr(K, p); m = (p - 1) // 2
        mN, mK = N // p, K // p
        target = h - L0 + 3 * (N - mN)
        T, E = divmod(target, m)
        a = np.arange(1, m + 1, dtype=np.int64)
        ellK = (K + p - a) // p + (K + a) // p
        ellN = (N + p - a) // p + (N + a) // p
        # rho
        F = (T - 3 * ellN) * (T + 3 * ellN - ellK - 5)
        rho = int(F.sum()) - p * IT(x, Fr(T))
        worst['rho/M2'] = max(worst['rho/M2'], abs(rho) / M**2)
        # Gam split (Gam_eq) and IT_succ
        TR = floor(2 * H * x)
        s = H * x - Fr(TR, 2); q = floor(2 * x); nplus = (2 * x - q) / 2
        if Gam_exact(x) != IT(x, Fr(TR)) + s * (2 * TR - q - 5) + max(Fr(0), s - nplus):
            worst['Gam_split'] += 1
        if IT(x, Fr(T + 1)) - IT(x, Fr(T)) != T - x - 2:
            worst['IT_succ'] += 1
        worst['Tcase'].add(TR - T)
        # eps sum
        order = np.argsort(-ellK, kind='stable')
        eps = np.zeros(m, dtype=np.int64); eps[order[:E]] = 1
        assert q == 2 * K // p
        assert set(np.unique(ellK)) <= {q, q + 1}
        U = int((ellK == q + 1).sum())
        if int((eps * ellK).sum()) != E * q + min(E, U):
            worst['eps_sum'] += 1
        if U != K - mK - m * q:
            worst['U_eq'] += 1
        # zero block
        Z = T + eps
        inner_min = int((2 * Z - ellK - 4).min())
        Z0 = sum(min(4 * i + 12 * mN - 2 * mK + 1, inner_min) for i in range(L0))
        worst['Z0/M2'] = max(worst['Z0/M2'], Fr(abs(Z0), M**2))
        delta = Fr(T, 2) - L0 - 3 * mN
        assert E - p * (H * x - Fr(T, 2)) == delta
        worst['delta/M'] = max(worst['delta/M'], abs(delta) / M)
        bound = abs(Z0) + abs(rho) + abs(delta) * (abs(2 * T - q) + 9) + 1
        g, _, _ = gamma_in(n, M, p)
        err = g - p * Gam_exact(x)
        assert abs(err) <= bound, (p, err, bound)
        worst['bound/M2'] = max(worst['bound/M2'], bound / M**2)
        # G lemma
        mm = 2 * h // p
        G = sum_floor_2i(h - 1, p)
        f = mm * h - Fr(p * mm * (mm + 1), 4)
        assert 0 <= f - G <= mm, (p, f - G, mm)
        worst['Ggap/m'] = max(worst['Ggap/m'], (f - G) / max(mm, 1))
    return {k: (float(v) if isinstance(v, Fr) else v) for k, v in worst.items()}

def check_outer(n):
    K, N, h = 40 * n, 3 * n, 37 * n
    worst_c = 0; worst_g = 0
    for p in primerange(2, 2 * h + 1):
        if not (K < 3 * p):
            continue
        G = sum_floor_2i(h - 1, p)
        mm = 2 * h // p
        assert mm <= 5
        S5 = sum(max(0, 2 * h - j * p) for j in range(1, 6))
        assert S5 == 2 * (mm * h) - Fr(p * mm * (mm + 1), 2)
        worst_g = max(worst_g, abs(S5 - 2 * G))
        y = Fr(p, K)
        c = K * R0(y) - K * dRank(y) + gammaOut(n, p)
        worst_c = max(worst_c, abs(c))
    return worst_c, worst_g

if __name__ == '__main__':
    M = int(sys.argv[1])
    for n in map(int, sys.argv[2:]):
        print('inner M', M, 'K', 40 * n, check(n, M), flush=True)
        print('outer K', 40 * n, 'max|K R0 - K d + gammaOut|, max|S5-2G| =', check_outer(n), flush=True)
    # outer sweep over all small n
    wc = 0; wg = 0
    for n in range(1, 400):
        c, g = check_outer(n)
        wc = max(wc, c); wg = max(wg, g)
    print('outer sweep n<400:', float(wc), float(wg))
