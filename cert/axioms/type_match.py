#!/usr/bin/env python3
"""cert/axioms/type_match.py -- compare the stored TYPE of each removed axiom (dump of bfd4249)
with the stored type of the theorem that replaces it (dump of the axioms branch HEAD):
serialisation digest, Expr.hash, universe parameters.  usage: type_match.py old.tsv new.tsv"""
import sys, hashlib
def load(p):
    d = {}
    for line in open(p, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        if len(f) == 9: d[f[0]] = f
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
pairs = [('Zeta5.Axioms.hermite_pole_integral', 'Zeta5.Hermite.pole_integral'),
         ('Zeta5.Axioms.pnt_prime_riemann_sum', 'Zeta5.PNT.prime_riemann_sum')]
ok = True
for old, new in pairs:
    x, y = a[old], b[new]
    same = (x[3] == y[3] and x[4] == y[4] and x[6] == y[6])
    ok &= same
    print(f"{old} [{x[1]}, {x[2]}]  vs  {new} [{y[1]}, {y[2]}]")
    print(f"   lparams {x[3]} / {y[3]}; Expr.hash {x[4]} / {y[4]}")
    print(f"   type serialisation sha256 {hashlib.sha256(x[6].encode()).hexdigest()[:16]} / "
          f"{hashlib.sha256(y[6].encode()).hexdigest()[:16]}  ({len(x[6])} / {len(y[6])} chars)")
    print(f"   IDENTICAL TYPE: {same}")
print("ALL IDENTICAL" if ok else "*** MISMATCH ***")
