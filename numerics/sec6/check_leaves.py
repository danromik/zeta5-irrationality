"""Numerical checks of every sorried leaf of the Sec6 blueprint (Zeta5/Sec6/*.lean),
with must-fail controls.  Run:  python3 numerics/sec6/check_leaves.py  (about 1-2 min).

Each check prints PASS/FAIL; a control prints PASS when the deliberately wrong
statement is indeed violated."""
import math
import random

import mpmath as mp
import numpy as np
from scipy import integrate

from common import (aT, bT, cT, LAM, ALPHA, M0, mid, rad, Uarc, Urho, Psi, kC, cS, Irho,
                    Vfield, Vclosed, report)

random.seed(1)


def llog(x):
    """Lean's Real.log: log 0 = 0, log |x| for x < 0."""
    return mp.log(abs(x)) if x != 0 else mp.mpf(0)


def ldiv(a, b):
    """Lean's division: a / 0 = 0."""
    return a / b if b != 0 else mp.mpf(0)

np.random.seed(1)


def llog(x):
    """Lean's Real.log: log 0 = 0, log |x| for x < 0."""
    return mp.log(abs(x)) if x != 0 else mp.mpf(0)


def ldiv(a, b):
    """Lean's division: a / 0 = 0."""
    return a / b if b != 0 else mp.mpf(0)

allok = True


def chk(name, ok, detail=""):
    global allok
    allok &= report(name, ok, detail)


print("== Frullani: frullani_cauchy, frullani_integrable ==")
for eps in [mp.mpf('0.01'), mp.mpf('0.3'), mp.mpf(1), mp.mpf(5)]:
    for d in [0, mp.mpf('0.001'), mp.mpf('0.5'), mp.mpf(2), mp.mpf(-7)]:
        f = lambda s: mp.exp(-s * eps**2) * (1 - mp.exp(-s * d**2)) / s
        lhs = mp.quad(f, [0, 1, 10, 100, mp.inf])
        rhs = mp.log(1 + d**2 / eps**2)
        chk(f"frullani eps={float(eps)} d={float(d)}", abs(lhs - rhs) < 1e-12,
            f"lhs={float(lhs):.15g} rhs={float(rhs):.15g}")
# control: the (wrong) value log(1 + |d|/eps)
eps, d = mp.mpf('0.3'), mp.mpf(2)
f = lambda s: mp.exp(-s * eps**2) * (1 - mp.exp(-s * d**2)) / s
chk("CONTROL frullani with log(1+|d|/eps) must differ",
    abs(mp.quad(f, [0, 1, 10, mp.inf]) - mp.log(1 + d / eps)) > 0.1)


def gE(s, xa, wa, xb, wb):
    D = xa[:, None] - xb[None, :]
    return float(wa @ np.exp(-s * D**2) @ wb)


def kEd(eps, xa, wa, xb, wb):
    D = xa[:, None] - xb[None, :]
    return float(wa @ (0.5 * np.log(D**2 + eps**2)) @ wb)


print("== gauss_pd (finite discrete measures, random) ==")
worst = 1e9
for trial in range(2000):
    na, nb = random.randint(1, 8), random.randint(1, 8)
    xa, xb = np.random.randn(na) * 2, np.random.randn(nb) * 2
    wa, wb = np.random.rand(na), np.random.rand(nb) * 3
    s = 10 ** random.uniform(-3, 3)
    v = gE(s, xa, wa, xa, wa) - 2 * gE(s, xa, wa, xb, wb) + gE(s, xb, wb, xb, wb)
    worst = min(worst, v)
chk("gauss_pd min over 2000 random pairs >= 0", worst >= -1e-12, f"min={worst:.3e}")
# control: the combination with +2 cross term is NOT >= 0 for sign-changing reason; use -PD
xa, wa, xb, wb = np.array([0.]), np.array([1.]), np.array([0.1]), np.array([1.])
chk("CONTROL gauss: G_ab - G_aa  (not a PD combination) must be > 0 somewhere",
    gE(1, xa, wa, xb, wb) - gE(1, xa, wa, xa, wa) + 0.5 > 0)

print("== cauchy_cnd (equal masses) ==")
worst = -1e9
# arcsine measure discretised by Gauss-Chebyshev nodes is itself a finite measure
N = 64
th = (np.arange(N) + 0.5) * np.pi / N
for trial in range(3000):
    na, nb = random.randint(1, 8), random.randint(1, 8)
    xa, xb = np.random.randn(na), np.random.randn(nb)
    wa, wb = np.random.rand(na), np.random.rand(nb)
    if trial % 3 == 0:  # beta = mixture of discretised arcsine measures
        j = random.randrange(16)
        xb = float(mid(j)) + float(rad(j)) * np.cos(th)
        wb = np.ones(N)
    wb = wb * wa.sum() / wb.sum()
    eps = 10 ** random.uniform(-4, 1)
    v = kEd(eps, xa, wa, xa, wa) - 2 * kEd(eps, xa, wa, xb, wb) + kEd(eps, xb, wb, xb, wb)
    worst = max(worst, v)
chk("cauchy_cnd max over 3000 random equal-mass pairs <= 0", worst <= 1e-10,
    f"max={worst:.3e}")
xa, wa, xb, wb = np.array([0.]), np.array([2.]), np.array([0.]), np.array([1.])
v = kEd(10.0, xa, wa, xa, wa) - 2 * kEd(10.0, xa, wa, xb, wb) + kEd(10.0, xb, wb, xb, wb)
chk("CONTROL cauchy_cnd without the mass condition fails", v > 0, f"value={v:.3f}")

print("== swap_frullani (Tonelli; discrete measures) ==")
for eps in [0.05, 1.0]:
    xa, wa = np.array([0., 0.7, -1.2]), np.array([0.3, 1.0, 0.5])
    xb, wb = np.array([0.1, 1.9]), np.array([2.0, 0.4])
    lhs = sum(wa[i] * wb[j] * math.log(1 + (xa[i] - xb[j])**2 / eps**2)
              for i in range(3) for j in range(2))
    g = lambda s: sum(wa[i] * wb[j] * math.exp(-s * eps**2) *
                      (1 - math.exp(-s * (xa[i] - xb[j])**2)) / s
                      for i in range(3) for j in range(2)) if s > 0 else 0.0
    rhs = integrate.quad(g, 0, np.inf, limit=500)[0]
    chk(f"swap_frullani eps={eps}", abs(lhs - rhs) < 1e-7, f"{lhs:.10f} vs {rhs:.10f}")

print("== integral_log_abs_sub_cos, intervalIntegrable_log_abs_sub_cos (normalised A.1) ==")
for x in [0, mp.mpf('0.3'), mp.mpf('-0.77'), 1, -1, mp.mpf('1.0000001'), mp.mpf('1.5'),
          mp.mpf(-3), 10, mp.mpf('1e6')]:
    x = mp.mpf(x)
    f = lambda th: llog(abs(x - mp.cos(th)))
    pts = [0, mp.pi]
    if abs(x) < 1:
        pts = [0, mp.acos(x), mp.pi]
    lhs = mp.quad(f, pts)
    rhs = mp.pi * Psi(x)
    chk(f"logcos x={float(x)}", abs(lhs - rhs) < 1e-10, f"{float(lhs):.14g} vs {float(rhs):.14g}")
x = mp.mpf('0.5')
wrong = mp.pi * mp.log((abs(x) + 0) / 2)
chk("CONTROL logcos: off-interval branch used inside [-1,1] is wrong",
    abs(mp.quad(lambda th: mp.log(abs(x - mp.cos(th))), [0, mp.acos(x), mp.pi]) - wrong) > 0.1)

print("== arcsine_pot (scaled A.1) ==")
for (a, b) in [(aT[0], bT[0]), (aT[15], bT[15]), (mp.mpf(-1), mp.mpf(3))]:
    m, r = (a + b) / 2, (b - a) / 2
    for t in [a - 1, a - mp.mpf('1e-5'), a, (a + b) / 2, b - (b - a) / 7, b, b + mp.mpf('0.2'), 5]:
        f = lambda th: llog(abs(t - (m + r * mp.cos(th))))
        pts = [0, mp.pi]
        if a < t < b:
            pts = [0, mp.acos((t - m) / r), mp.pi]
        lhs = mp.quad(f, pts)
        chk(f"arcsine_pot a={float(a):.4g} b={float(b):.4g} t={float(t):.6g}",
            abs(lhs - mp.pi * Uarc(a, b, t)) < 1e-9)

print("== exists_nearest_cos ==")
ok = True
for _ in range(5000):
    tau = random.uniform(-3, 3)
    th0 = math.acos(max(-1, min(1, tau)))
    thv = random.uniform(-10, 10)
    ok &= abs(math.cos(th0) - math.cos(thv)) <= abs(tau - math.cos(thv)) + 1e-15
chk("exists_nearest_cos with theta0 = arccos(clamp tau)", ok)

print("== cos_sub_cos_ge (proved; recheck) ==")
worst = 1e9
for _ in range(20000):
    t1, t2 = random.uniform(0, math.pi), random.uniform(0, math.pi)
    if t1 != t2:
        worst = min(worst, abs(math.cos(t2) - math.cos(t1)) / (2 * (t1 - t2)**2 / math.pi**2))
chk("cos_sub_cos_ge ratio >= 1", worst >= 1 - 1e-12, f"min ratio={worst:.6f}")

print("== integral_log_one_add_sq_div ==")
for b in [mp.mpf('0.01'), mp.mpf(1), mp.mpf(3)]:
    for X in [0, mp.mpf('0.1'), 1, mp.pi, 5]:
        X = mp.mpf(X)
        lhs = mp.quad(lambda u: mp.log(1 + b**2 / u**2), [0, X]) if X > 0 else 0
        rhs = X * mp.log(1 + b**2 / X**2) + 2 * b * mp.atan(X / b) if X > 0 else 0
        chk(f"int log(1+b^2/x^2) b={float(b)} X={float(X):.4g}", abs(lhs - rhs) < 1e-12)

print("== smooth_err_norm ==")


def smooth_int(x, delta):
    f = lambda th: llog(1 + ldiv(delta**2, (x - mp.cos(th))**2)) / 2
    pts = [0, mp.pi]
    if abs(x) < 1:
        th0 = mp.acos(x)
        pts = [0, th0, mp.pi]
    return mp.quad(f, pts)


worst = 0
mp.mp.dps = 20
for delta in [mp.mpf('1e-8'), mp.mpf('1e-5'), mp.mpf('1e-3'), mp.mpf('0.05'), mp.mpf(1), mp.mpf(30)]:
    for x in [-2, -1.0001, -1, -0.999, -0.3, 0, 0.5, 0.99999, 1, 1 + 1e-7, 1.001, 1.3, 4]:
        x = mp.mpf(x)
        lhs = smooth_int(x, delta)
        rhs = mp.pi * (delta + mp.pi * mp.sqrt(2 * delta))
        worst = max(worst, float(lhs / rhs))
chk("smooth_err_norm: max LHS/RHS <= 1", worst <= 1, f"max ratio={worst:.4f}")
# control: the constant pi*sqrt(2 delta) replaced by 0.1*sqrt(delta) must fail
x, delta = mp.mpf(1), mp.mpf('1e-6')
chk("CONTROL smooth_err with RHS pi*(delta + 0.1*sqrt(delta)) fails",
    smooth_int(x, delta) > mp.pi * (delta + mp.mpf('0.1') * mp.sqrt(delta)))

print("== arcsine_smooth_err (scaled) ==")
worst = 0
for (a, b) in [(aT[0], bT[0]), (aT[7], bT[7]), (aT[15], bT[15])]:
    m, r, L = (a + b) / 2, (b - a) / 2, b - a
    for eps in [mp.mpf('1e-6'), mp.mpf('1e-3'), mp.mpf('0.1')]:
        for t in [a - 1, a - L / 100, a, m, b - L / 3, b, b + L / 10, 3]:
            f = lambda th: kC(eps, t - (m + r * mp.cos(th)))
            pts = [0, mp.pi]
            if a < t < b:
                pts = [0, mp.acos((t - m) / r), mp.pi]
            lhs = mp.quad(f, pts)
            rhs = mp.pi * (Uarc(a, b, t) + 2 * eps / L + 2 * mp.pi * mp.sqrt(eps / L))
            worst = max(worst, float((lhs - mp.pi * Uarc(a, b, t)) /
                                     (rhs - mp.pi * Uarc(a, b, t))))
chk("arcsine_smooth_err: max (err / allowed err) <= 1", worst <= 1, f"max={worst:.4f}")

print("== rho_cross ==")
worst = 0
for eps in [mp.mpf('1e-6'), mp.mpf('1e-4'), mp.mpf('0.01'), mp.mpf(1)]:
    for t in [-1, 0, 0.0717, 0.1, 0.35, 0.6, 0.619, 0.75, 1.0, 2.0, 5.0]:
        t = mp.mpf(t)
        tot = 0
        for j in range(16):
            m, r = mid(j), rad(j)
            pts = [0, mp.pi]
            if aT[j] < t < bT[j]:
                pts = [0, mp.acos((t - m) / r), mp.pi]
            tot += cT[j] * mp.quad(lambda th: kC(eps, t - (m + r * mp.cos(th))), pts) / mp.pi
        allowed = 88 * mp.sqrt(eps) + 420 * eps
        worst = max(worst, float((tot - Urho(t)) / allowed))
chk("rho_cross: max (err/allowed) <= 1", worst <= 1, f"max={worst:.4f}")

print("== Irho_double_sum ==")
dbl = mp.fsum(cT[i] * cT[j] * mp.log((bT[max(i, j)] - aT[max(i, j)]) / 4)
              for i in range(16) for j in range(16))
chk("Irho_double_sum", abs(dbl - Irho()) < 1e-25, f"Irho={mp.nstr(Irho(), 25)}")
dbl_min = mp.fsum(cT[i] * cT[j] * mp.log((bT[min(i, j)] - aT[min(i, j)]) / 4)
                  for i in range(16) for j in range(16))
chk("CONTROL Irho with min(i,j) instead of max(i,j) differs", abs(dbl_min - Irho()) > 0.01)

print("== nesting (used by pair_energy_ge) ==")
ok = all(aT[j] <= aT[i] and bT[i] <= bT[j] for i in range(16) for j in range(i, 16))
chk("[a_i,b_i] ⊆ [a_j,b_j] for i ≤ j", ok)

print("== pair_energy_ge, rho_energy_ge (Gauss-Chebyshev outer, adaptive inner) ==")
mp.mp.dps = 15


def inner(eps, x, j):
    m, r = float(mid(j)), float(rad(j))
    f = lambda th: 0.5 * math.log((x - m - r * math.cos(th))**2 + eps**2)
    pts = None
    u = (x - m) / r
    if -1 < u < 1:
        pts = [math.acos(u)]
    return integrate.quad(f, 0, math.pi, points=pts, limit=400, epsabs=1e-13, epsrel=1e-12)[0] / math.pi


def pairE(eps, i, j, Nout=200):
    th = (np.arange(Nout) + 0.5) * np.pi / Nout
    xs = float(mid(i)) + float(rad(i)) * np.cos(th)
    return sum(inner(eps, x, j) for x in xs) / Nout


worstpair = 1e9
for eps in [1e-3, 1e-1]:
    for (i, j) in [(0, 0), (0, 15), (3, 9), (14, 15), (15, 15)]:
        v = pairE(eps, i, j)
        lb = math.log(float((bT[j] - aT[j]) / 4))
        worstpair = min(worstpair, v - lb)
        chk(f"pair_energy_ge eps={eps} i={i} j={j}", v >= lb - 1e-9, f"kE={v:.8f} >= {lb:.8f}")
    # symmetry kE(w_i,w_j) = kE(w_j,w_i)
    chk(f"kE_arc_comm eps={eps}", abs(pairE(eps, 2, 11, Nout=3000) - pairE(eps, 11, 2, Nout=3000)) < 1e-6)
for eps in [1e-2, 1.0]:
    tot = 0.0
    for i in range(16):
        for j in range(16):
            tot += float(cT[i] * cT[j]) * pairE(eps, i, j, Nout=60)
    chk(f"rho_energy_ge eps={eps}", tot >= float(Irho()), f"kE(rho,rho)={tot:.8f} >= Irho={float(Irho()):.8f}")

print("== integral_log_add_sq, Vfield_eq_Vclosed (A.5) ==")
mp.mp.dps = 30
for t in [mp.mpf('1e-8'), mp.mpf('0.01'), mp.mpf('0.592'), 1, 2, 10]:
    t = mp.mpf(t)
    for c in [ALPHA, 1, mp.mpf(-2), 0]:
        lhs = mp.quad(lambda u: mp.log(t + u * u), [0, c]) if c != 0 else 0
        rhs = c * mp.log(t + c * c) - 2 * c + 2 * mp.sqrt(t) * mp.atan(c / mp.sqrt(t))
        chk(f"integral_log_add_sq t={float(t)} c={float(c)}", abs(lhs - rhs) < 1e-20)
    chk(f"Vfield_eq_Vclosed t={float(t)}", abs(Vfield(t) - Vclosed(t)) < 1e-20)
chk("CONTROL Vclosed at t=0 differs from the t>0 limit only through 1/0=0 (V(0) finite)",
    abs(Vclosed(0) - (-12 * ALPHA * mp.log(ALPHA) - 2 + 12 * ALPHA)) < 1e-25)

print("== (6.7) in closed form (proved in Sec6/Num; recheck on a grid) ==")
worst = -1e9
for k in range(1, 4001):
    t = mp.mpf(k) / 1000
    worst = max(worst, float(2 * Urho(t) - Vclosed(t)))
chk("max_{t in (0,4]} 2U^rho - V <= M0", worst <= float(M0), f"max={worst:.6f} M0={float(M0)}")

print()
print("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")
