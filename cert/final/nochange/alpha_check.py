#!/usr/bin/env python3
"""For constants whose serialised type/value differ between two DumpDecls dumps, check whether
they differ ONLY in binder names (alpha-equivalence): binder names of lam/forall/let nodes are
blanked, binder info and everything else kept. usage: alpha_check.py main.tsv head.tsv"""
import re, sys
def load(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        x = l.rstrip('\n').split('\t'); d[x[0]] = x
    return d
def norm(s):
    return ';'.join(re.sub(r'^([LPE]).*?:(Lean\.BinderInfo\.\w+:|(?:true|false):)', r'\1_:\2', n)
                    for n in s.split(';'))
a, b = load(sys.argv[1]), load(sys.argv[2])
bad = 0; cnt = 0
for n in sorted(set(a) & set(b)):
    x, y = a[n], b[n]
    if x[6] != y[6] or x[7] != y[7]:
        cnt += 1
        ok = norm(x[6]) == norm(y[6]) and norm(x[7]) == norm(y[7]) and x[1] == y[1] and x[3] == y[3] and x[8] == y[8]
        print(('ALPHA-EQUIVALENT ' if ok else 'GENUINELY DIFFERENT ') + x[1] + ' ' + n)
        bad += (not ok)
print(f"{cnt} constants with differing serialisation; {bad} not alpha-equivalent")
