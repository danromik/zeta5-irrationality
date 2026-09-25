# Fidelity check: Table 1 (PDF text) vs Lean aT/bT/cT, and numerical values of I(rho), M0, lam, Ubar, Cstar.
import re, math
from mpmath import mp, mpf, log, sqrt
mp.dps = 40
# Usage (from the repository root):
#   pdftotext -layout -f 17 -l 25 <preprint.pdf> pp17-25.txt
#   python3 cert/final/fidelity/constants.py pp17-25.txt
# The preprint is not included in this repository (README, 'Reference').
import os, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
txt = open(sys.argv[1] if len(sys.argv) > 1 else "pp17-25.txt").read()
i = txt.index("Table 1:")
rows = []
for line in txt[i:].splitlines()[2:18]:
    j, a, b, c = map(int, line.split())
    rows.append((a, b, c))
lean = open(ROOT + "/Zeta5/RealBound.lean").read()
def leanfun(name):
    m = re.search(r"def %s : ℕ → ℝ\n(.*?)\n  \| _ => 0" % name, lean, re.S)
    return [int(x) for x in re.findall(r"\| \d+ => (\d+) / 10 \^ 12", m.group(1))]
A, B, C = leanfun("aT"), leanfun("bT"), leanfun("cT")
assert [r[0] for r in rows] == A and [r[1] for r in rows] == B and [r[2] for r in rows] == C, "TABLE MISMATCH"
print("Table 1: PDF text == Lean aT,bT,cT (16 rows) OK")
a = [mpf(x) / 10**12 for x in A]; b = [mpf(x) / 10**12 for x in B]; c = [mpf(x) / 10**12 for x in C]
S = [mpf(0)]
for x in c: S.append(S[-1] + x)
print("sum c =", S[-1], " (37/40 =", mpf(37)/40, ")")
Irho = sum((S[j+1]**2 - S[j]**2) * log((b[j]-a[j])/4) for j in range(16))
print("Irho (A.2) =", Irho)
# independent: double sum over pairs with nesting: I(w_j,w_k) = log(L_max/4)
Idbl = sum(c[j]*c[k]*log((b[max(j,k)]-a[max(j,k)])/4) for j in range(16) for k in range(16))
print("Irho via double sum c_j c_k log(L_max(j,k)/4) =", Idbl)
lam = mpf(37)/40; alpha = mpf(3)/40; M0 = mpf(-1329)/200
Cstar = -2*lam + 12*alpha*lam*(1-log(alpha)) + 3*lam**2 - 2*lam**2*log(2*lam)
Ubar = mpf(-2733991)/2000000
print("M0 =", M0, " lam*M0 - Irho =", lam*M0 - Irho)
print("Cstar =", Cstar, " lam*M0 - Irho + Cstar =", lam*M0 - Irho + Cstar, " Ubar =", Ubar, " <= Ubar:", lam*M0 - Irho + Cstar <= Ubar)
print("Ubar < -136699/100000:", Ubar < mpf(-136699)/100000)
