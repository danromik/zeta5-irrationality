#!/usr/bin/env python3
"""
Numeric sanity check of the statement of Zeta5.HermiteBasis.det_coeffMatrix_unimodular
(and of its intermediate stubs), in exact integer arithmetic.

Statement being tested.  p prime; nodes u : kappa -> ZMod p injective; multiplicities
m : kappa -> N; hh = sum m; sigma : Fin hh ~ Sigma a, Fin (m a); integer polynomials
g_k (k < hh) with  g_k mod p  ==  hermitePoly u m a i
                              :=  prod_{c != a} (X + u_c)^{m_c} * (X + u_a)^i ,  (a,i) = sigma k.
Conclusion: U = [coeff_i(g_k)]_{k,i < hh} has det U != 0 and v_p(det U) = 0, i.e. p does not
divide the integer det U.

PART A  random tests (the claim must hold every time)
PART B  MUST-FAIL control: two nodes equal mod p (both multiplicities >= 1) -> p | det U always
PART C  known-answer control: the paper's outer basis (4.11), built as in the referee audit of
        the preprint (see README, 'Provenance'), at K = 40, 80, 120 and every prime satisfying (4.9);
        check (i) every row reduces mod p EXACTLY to hermitePoly with u_c = c^2, m_c = number of
        tail poles in class c (= outerDim), the row's (class, index) label giving sigma; and
        (ii) v_p(det U) = 0.
PART D  known-answer control: inner basis (4.5) shape (rows are literally hermitePoly over Z
        with integer nodes c^2, 0 <= c <= (p-1)/2), random L_c.
"""
import random, sys
from itertools import product

random.seed(20260923)

def pmul(a, b):
    if not a or not b: return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r

def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]

def ppow(a, e):
    r = [1]
    for _ in range(e): r = pmul(r, a)
    return r

def trim(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return a

def pmod(a, p):
    return trim([x % p for x in a])

def coeff(a, i):
    return a[i] if i < len(a) else 0

def det_bareiss(M):
    """exact integer determinant (fraction-free Bareiss)."""
    n = len(M)
    if n == 0: return 1
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = None
            for r in range(k + 1, n):
                if A[r][k] != 0: sw = r; break
            if sw is None: return 0
            A[k], A[sw] = A[sw], A[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]

def det_mod_p(M, p):
    """determinant mod p by Gaussian elimination over F_p."""
    n = len(M); A = [[x % p for x in row] for row in M]; d = 1
    for k in range(n):
        piv = next((r for r in range(k, n) if A[r][k]), None)
        if piv is None: return 0
        if piv != k: A[k], A[piv] = A[piv], A[k]; d = -d
        d = d * A[k][k] % p
        inv = pow(A[k][k], p - 2, p)
        for r in range(k + 1, n):
            if A[r][k]:
                f = A[r][k] * inv % p
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[k])]
    return d % p

def vp(x, p):
    assert x != 0
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

def hermite_mod_p(u, m, a, i, p):
    """hermitePoly u m a i reduced mod p, as a trimmed list of residues."""
    r = [1]
    for c in range(len(u)):
        if c != a:
            r = pmul(r, ppow([u[c] % p, 1], m[c]))
    r = pmul(r, ppow([u[a] % p, 1], i))
    return pmod(r, p)

def random_lift(u, m, a, i, p, extra_deg):
    """an integer polynomial reducing mod p to hermitePoly u m a i: every linear factor gets its
    own random lift u_c + p*t of its node (as in the outer basis, where t + j^2 with
    j = +-c mod p stands for t + c^2), plus p * (random integer polynomial)."""
    r = [1]
    for c in range(len(u)):
        e = m[c] if c != a else i
        for _ in range(e):
            r = pmul(r, [u[c] + p * random.randint(-3, 3), 1])
    noise = [p * random.randint(-5, 5) for _ in range(extra_deg + 1)]
    return trim(padd(r, noise))

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 97, 101]

def one_case(p, u, m, lift=True, extra=0):
    rows = [(a, i) for a in range(len(u)) for i in range(m[a])]
    random.shuffle(rows)            # sigma: an arbitrary bijection Fin hh ~ Sigma a, Fin (m a)
    hh = len(rows)
    assert hh == sum(m)
    g = []
    for (a, i) in rows:
        if lift:
            gk = random_lift(u, m, a, i, p, extra)
        else:
            gk = [1]
            for c in range(len(u)):
                if c != a: gk = pmul(gk, ppow([u[c], 1], m[c]))
            gk = pmul(gk, ppow([u[a], 1], i))
        # the hypothesis hg, checked (so the generator itself is tested)
        assert pmod(gk, p) == hermite_mod_p(u, m, a, i, p), (p, u, m, a, i)
        g.append(gk)
    U = [[coeff(g[k], j) for j in range(hh)] for k in range(hh)]
    return det_bareiss(U), hh

# ---------------------------------------------------------------- PART A
A_tot = A_ok = 0; A_maxh = 0
for trial in range(1500):
    p = random.choice(PRIMES)
    r = random.randint(1, min(p, 6))
    nodes = random.sample(range(p), r)               # distinct mod p
    u = [x + p * random.randint(-2, 2) for x in nodes]  # integer representatives
    m = [random.randint(0, 5) for _ in range(r)]
    extra = random.randint(0, 3) + sum(m)            # noise up to degree >= hh (must not matter)
    d, hh = one_case(p, u, m, lift=True, extra=extra)
    A_tot += 1; A_maxh = max(A_maxh, hh)
    if d != 0 and d % p != 0: A_ok += 1
    else: print("PART A FAILURE", p, u, m, d)
print(f"PART A (random lifts, distinct nodes): {A_ok}/{A_tot} have det U != 0 and p | det U false"
      f"   (hh up to {A_maxh})")

# ---------------------------------------------------------------- PART B (must fail)
B_tot = B_fail = 0
for trial in range(1000):
    p = random.choice(PRIMES)
    r = random.randint(2, min(p + 1, 6))
    if p >= r - 1:
        nodes = random.sample(range(p), r - 1)
    nodes = nodes + [random.choice(nodes)]            # force a collision mod p
    random.shuffle(nodes)
    u = [x + p * random.randint(-2, 2) for x in nodes]
    m = [random.randint(0, 4) for _ in range(r)]
    # make sure the colliding pair both have positive multiplicity
    coll = [(i, j) for i in range(r) for j in range(i + 1, r) if (u[i] - u[j]) % p == 0]
    i0, j0 = coll[0]
    m[i0] = max(m[i0], 1); m[j0] = max(m[j0], 1)
    d, hh = one_case(p, u, m, lift=True, extra=random.randint(0, 3) + sum(m))
    B_tot += 1
    if d % p == 0: B_fail += 1
    else: print("PART B control did NOT fail", p, u, m, d)
print(f"PART B (MUST-FAIL: two nodes equal mod p): {B_fail}/{B_tot} have p | det U")

# ---------------------------------------------------------------- PART C (outer basis (4.11))
def outer_run(K, N, p):
    h = K - N
    tail = list(range(N + 1, K + 1))
    mh = (p - 1) // 2
    t = lambda s: [s, 1]                      # t + s
    def prod(fs):
        r = [1]
        for f in fs: r = pmul(r, f)
        return r
    Dtail = prod(t(j * j) for j in tail)
    def cls(j):                               # class c in 0..mh with j = +-c mod p
        c = j % p
        return c if c <= mh else p - c
    mult = [0] * (mh + 1)
    for j in tail: mult[cls(j)] += 1
    u = [c * c for c in range(mh + 1)]
    rows = []; labels = []
    def divexact(a, b):                       # a / b for monic b, exact
        a = list(a); q = [0] * (len(a) - len(b) + 1)
        for k in range(len(a) - len(b), -1, -1):
            q[k] = a[k + len(b) - 1]
            for s in range(len(b)): a[k + s] -= q[k] * b[s]
        assert trim(a) == [], "not exact"
        return q
    for a in range(1, mh + 1):
        cls_all = [j for j in range(1, K + 1) if (j - a) % p == 0 or (j + a) % p == 0]
        ell = len(cls_all); delta = 1 if a <= N else 0
        cls_tail = [j for j in cls_all if j > N]
        assert len(cls_tail) == ell - delta == mult[a]
        if ell - delta == 0: continue
        Qa = prod(t(j * j) for j in cls_tail); Pa = divexact(Dtail, Qa)
        big = [j for j in cls_tail if j > p]
        nbig = len(big)
        if K >= p: assert nbig == ell - 2, (a, ell, big)
        Ea = prod(t(j * j) for j in big)
        for i in range(ell - delta):
            if i < nbig: q = ppow(t(a * a), i)
            else:        q = pmul(Ea, ppow(t(a * a), i - nbig))
            rows.append(pmul(Pa, q)); labels.append((a, i))
    zcls = [j for j in tail if j % p == 0]
    assert len(zcls) == mult[0]
    if zcls:
        Q0 = prod(t(j * j) for j in zcls); P0 = divexact(Dtail, Q0)
        rows.append(P0); labels.append((0, 0))
        if len(zcls) == 2:
            rows.append(pmul(P0, t(p * p))); labels.append((0, 1))
        assert len(zcls) <= 2
    assert len(rows) == h == sum(mult)
    # (i) the hypothesis hg, row by row
    for g, (a, i) in zip(rows, labels):
        assert len(trim(g)) - 1 < h
        if pmod(g, p) != hermite_mod_p(u, mult, a, i, p):
            return ("HYPOTHESIS FAILS", a, i)
    # sigma is a bijection onto Sigma a, Fin (mult a)
    assert sorted(labels) == sorted((a, i) for a in range(mh + 1) for i in range(mult[a]))
    U = [[coeff(g, j) for j in range(h)] for g in rows]
    d = det_mod_p(U, p)          # det U mod p != 0  implies det U != 0 and v_p(det U) = 0
    return ("ok", d != 0, h, mult[0])

C_tot = C_ok = 0
for n in (1, 2, 3):
    K, N = 40 * n, 3 * n
    ps = [p for p in range(7, 3 * K) if all(p % q for q in range(2, int(p ** .5) + 1))
          and p <= K < 3 * p and p * p > 2 * K and 2 * N < p and 5 * N <= 2 * p - 2]
    res = []
    for p in ps:
        r = outer_run(K, N, p)
        C_tot += 1
        if r[0] == "ok" and r[1]: C_ok += 1
        res.append((p, r))
    print(f"PART C K={K}: primes {ps}")
    for p, r in res:
        if not (r[0] == "ok" and r[1]): print("   PART C FAILURE", p, r)
print(f"PART C (outer basis (4.11), K=40,80,120, all (4.9) primes): hypothesis hg holds exactly and "
      f"v_p(det U)=0 at {C_ok}/{C_tot} primes")

# also p > K (second assertion of Prop 4.3; zero class empty, no E_a): a few primes
C2_tot = C2_ok = 0
for n in (1, 2):
    K, N = 40 * n, 3 * n
    for p in [q for q in range(K + 1, K + 40) if all(q % s for s in range(2, int(q ** .5) + 1))]:
        r = outer_run(K, N, p); C2_tot += 1
        if r[0] == "ok" and r[1]: C2_ok += 1
        else: print("   PART C' FAILURE", K, p, r)
print(f"PART C' (outer rows at p > K): hypothesis + unimodular at {C2_ok}/{C2_tot} primes")

# ---------------------------------------------------------------- PART D (inner basis (4.5))
D_tot = D_ok = 0
for trial in range(300):
    p = random.choice([7, 11, 13, 17, 19, 23, 29, 31])
    mh = (p - 1) // 2
    u = [c * c for c in range(mh + 1)]
    m = [random.randint(0, 4) for _ in range(mh + 1)]
    d, hh = one_case(p, u, m, lift=False)
    D_tot += 1
    if d != 0 and d % p != 0: D_ok += 1
    else: print("PART D FAILURE", p, m, d)
print(f"PART D (inner basis (4.5) with nodes c^2, 0<=c<=(p-1)/2, random L_c): {D_ok}/{D_tot} unimodular")
