"""Shared data and closed forms for the Sec6 leaf checks (Zeta5/Sec6/*.lean).

Everything here is transcribed from the Lean definitions in Zeta5/Sec6/Defs.lean and
Zeta5/RealBound.lean (Table 1)."""
import mpmath as mp

mp.mp.dps = 30

A = [3906748086, 2312248264, 1402286665, 881725356, 578197906, 396324613, 283911191,
     212206188, 165097686, 133347132, 111522114, 96349355, 85815639, 78667711, 74129565,
     71741310]
B = [8992695531, 15340997855, 25730180724, 41909578246, 65851089563, 99481037884,
     144325727458, 201105762729, 269345996903, 347089554156, 430806704415, 515561896511,
     595448778546, 664241383483, 716160577112, 746637295669]
C = [10515596180, 29471737793, 42934365099, 58204231966, 69037621310, 78873099189,
     84856120711, 88396082127, 88303382125, 85472321255, 78899184238, 70353471918,
     58838976615, 44421321106, 30462865791, 5959622577]
aT = [mp.mpf(x) / 10**12 for x in A]
bT = [mp.mpf(x) / 10**12 for x in B]
cT = [mp.mpf(x) / 10**12 for x in C]
LAM = mp.mpf(37) / 40
ALPHA = mp.mpf(3) / 40
M0 = mp.mpf(-1329) / 200


def mid(j):
    return (aT[j] + bT[j]) / 2


def rad(j):
    return (bT[j] - aT[j]) / 2


def Uarc(a, b, t):
    """(A.1) closed form, Lean's `Uarc` (sqrt of a negative number is 0)."""
    if a <= t <= b:
        return mp.log((b - a) / 4)
    p = (t - a) * (t - b)
    s = mp.sqrt(p) if p > 0 else 0
    return mp.log((abs(t - (a + b) / 2) + s) / 2)


def Urho(t):
    return mp.fsum(cT[j] * Uarc(aT[j], bT[j], t) for j in range(16))


def Psi(x):
    if abs(x) <= 1:
        return -mp.log(2)
    return mp.log((abs(x) + mp.sqrt(x * x - 1)) / 2)


def kC(eps, x):
    return mp.log(x * x + eps * eps) / 2


def cS(m):
    return mp.fsum(cT[:m])


def Irho():
    return mp.fsum((cS(m + 1) ** 2 - cS(m) ** 2) * mp.log((bT[m] - aT[m]) / 4)
                   for m in range(16))


def Vfield(t):
    """(6.1) by quadrature."""
    f = lambda u: mp.log(t + u * u)
    return 2 * mp.pi * mp.sqrt(t) + mp.quad(f, [0, 1]) - 6 * mp.quad(f, [0, ALPHA])


def Vclosed(t):
    """(A.5), Lean's `Vclosed` (with 1/0 = 0)."""
    s = mp.sqrt(t)
    inv = (1 / s) if s != 0 else 0
    ainv = (ALPHA / s) if s != 0 else 0
    return (mp.log(1 + t) - 6 * ALPHA * mp.log(t + ALPHA ** 2) - 2 + 12 * ALPHA
            + 2 * s * (mp.pi + mp.atan(inv) - 6 * mp.atan(ainv)))


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    return ok
