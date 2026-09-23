#!/usr/bin/env python3
"""Known-answer control for the ONE remaining sorry, Zeta5.RealBound.eq_6_14, which is stated
for EVERY n > 0 (K = 40n, N = 3n, h = 37n) under Delta_K(zeta(5)) > 0.  If it failed at any
small n, the development would rest on a false statement.

Irho, M0 and lam are parsed from the LEAN SOURCE (Zeta5/RealBound.lean), not copied from the
paper.  The values of log Delta_K(zeta(5)) come from the referee audit of the preprint
(docs/zeta5-audit.pdf, Section "The direct computations": Delta_K computed exactly in Q[X] by
four independent implementations and evaluated at zeta(5) with thousands of digits).  They are
recorded in cert/c3/delta_K_values.json, with log F_K = log S_K + log Delta_K as in the audit's
table of exact determinant data.

Usage, from the repository root:
    python3 cert/c3/eq_6_14_control.py                 # uses cert/c3/delta_K_values.json
    python3 cert/c3/eq_6_14_control.py <delta.json>    # any other data file of the same format
where <delta.json> is a JSON list of objects with keys K, N, h, positive, log_Delta.
Recorded output: cert/c3/eq_6_14_control.out.
"""
import json, os, re, sys
from mpmath import mp, mpf, log

mp.dps = 50
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
src = open(os.path.join(ROOT, "Zeta5", "RealBound.lean"), encoding="utf-8").read()


def table(name):
    blk = re.search(rf"def {name} : ℕ → ℝ\n(.*?)\| _ => 0", src, re.S).group(1)
    return {int(i): mpf(int(a)) / 10**int(e)
            for i, a, e in re.findall(r"\| (\d+) => (\d+) / 10 \^ (\d+)", blk)}


aT, bT, cT = table("aT"), table("bT"), table("cT")
cS = lambda m: sum(cT[i] for i in range(m))
Irho = sum((cS(j + 1)**2 - cS(j)**2) * log((bT[j] - aT[j]) / 4) for j in range(16))
M0 = mpf(-1329) / 200
assert "def M0 : ℝ := -1329 / 200" in src
lam = mpf(37) / 40
print(f"Irho (from the Lean definition) = {mp.nstr(Irho, 25)}   audit (A.2): -2.1265934451470504033")
print(f"lam*M0 - Irho = {mp.nstr(lam*M0 - Irho, 20)}   audit: -4.0200315549")

data = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "cert", "c3", "delta_K_values.json")
summ = json.load(open(data))
for row in summ:
    K, N, h = row["K"], row["N"], row["h"]; n = K // 40
    assert (N, h) == (3 * n, 37 * n)
    rhs = 2*h*(h + 6*N - K)*log(K) + (lam*M0 - Irho)*K**2 + 18*h*log(K) + 160*h
    lhs = mpf(row["log_Delta"])
    print(f"n={n} K={K:4d}: Delta_K(zeta5)>0: {row['positive']}   log Delta = {float(lhs):12.3f}   "
          f"RHS(6.14) = {float(rhs):12.3f}   holds: {lhs <= rhs}   slack = {float(rhs - lhs):.1f}")
# the asymptotic direction: the K^2 coefficient of RHS is 2*lam*(lam+6*alpha-1)*log K + (lam*M0-Irho)
