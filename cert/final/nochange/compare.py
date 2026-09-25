#!/usr/bin/env python3
"""cert/final/nochange/compare.py — compare two DumpDecls.lean dumps (main vs eq614 HEAD).

usage: python3 compare.py main.tsv head.tsv

Each dump line: name kind module lparams typeHash32 valHash32 typeSer valSer extra.
The serialisations are replaced by SHA-256 digests. Reports:
  * constants of main missing on HEAD;
  * constants present in both whose kind / universe params / type / value / extra differ;
  * constants present in both whose defining module changed;
  * constants added on HEAD (counted per module; non-auxiliary top-level names listed).
Theorem proofs are not compared (valSer is '-' for theorems).
"""
import hashlib, sys, collections

AUX_MARKERS = ('._proof_', '.proof_', '.match_', '._sunfold', '._unfold', '.eq_', '._cstage',
               '._closed', '._lambda', '._aux', '._simp', '.congr_simp', '.eq_def',
               '._auxLemma', '._nativeDecide', '.sizeOf_spec', '._override', '.induct')

def load(path):
    d = {}
    with open(path, encoding='utf-8') as f:
        for line in f:
            line = line.rstrip('\n')
            if not line:
                continue
            p = line.split('\t')
            assert len(p) == 9, (path, len(p), line[:200])
            name, kind, mod, lps, th, vh, tser, vser, extra = p
            d[name] = dict(kind=kind, mod=mod, lps=lps, th=th, vh=vh,
                           tsha=hashlib.sha256(tser.encode()).hexdigest(),
                           vsha=('-' if vser == '-' else hashlib.sha256(vser.encode()).hexdigest()),
                           extra=extra, tlen=len(tser), vlen=len(vser))
    return d

def main():
    a, b = load(sys.argv[1]), load(sys.argv[2])
    print(f"main: {len(a)} constants in Zeta5 modules; HEAD: {len(b)}")
    removed = sorted(set(a) - set(b))
    added = sorted(set(b) - set(a))
    common = sorted(set(a) & set(b))
    print(f"removed (on main, not on HEAD): {len(removed)}")
    for n in removed:
        print(f"  REMOVED {a[n]['kind']:6} {n}  [{a[n]['mod']}]")
    changed, moved = [], []
    for n in common:
        x, y = a[n], b[n]
        diffs = [k for k in ('kind', 'lps', 'th', 'tsha', 'vh', 'vsha', 'extra') if x[k] != y[k]]
        if diffs:
            changed.append((n, diffs))
        if x['mod'] != y['mod']:
            moved.append((n, x['mod'], y['mod']))
    print(f"common: {len(common)}; changed kind/lparams/type/value/extra: {len(changed)}")
    for n, ds in changed:
        print(f"  CHANGED {a[n]['kind']:6} {n}  fields={ds}  [{a[n]['mod']} -> {b[n]['mod']}]")
        for k in ds:
            if k == 'extra':
                print(f"      main extra: {a[n]['extra']}\n      head extra: {b[n]['extra']}")
    print(f"common but defining module changed: {len(moved)}")
    for n, m1, m2 in moved:
        print(f"  MOVED   {a[n]['kind']:6} {n}  {m1} -> {m2}")
    kinds = collections.Counter(b[n]['kind'] for n in added)
    mods = collections.Counter(b[n]['mod'] for n in added)
    print(f"added on HEAD: {len(added)}  by kind: {dict(sorted(kinds.items()))}")
    oldmods = set(x['mod'] for x in a.values())
    print("added, by module (* = module that also existed on main):")
    for m, c in sorted(mods.items()):
        print(f"  {'*' if m in oldmods else ' '} {m}: {c}")
    print("added constants in modules that existed on main:")
    for n in added:
        if b[n]['mod'] in oldmods:
            print(f"  ADDED   {b[n]['kind']:6} {n}  [{b[n]['mod']}]")
    print("added axioms / opaques / unsafe or partial defs on HEAD:")
    for n in added:
        e = b[n]
        if e['kind'] in ('axiom', 'opaque', 'quot') or 'safety=unsafe' in e['extra'] or 'safety=partial' in e['extra'] or 'unsafe=true' in e['extra']:
            print(f"  {e['kind']} {n} [{e['mod']}] {e['extra']}")
    print("all axioms on HEAD (Zeta5 modules):")
    for n in sorted(b):
        if b[n]['kind'] == 'axiom':
            same = n in a and a[n]['tsha'] == b[n]['tsha']
            print(f"  {n} [{b[n]['mod']}] identical-to-main={same}")

if __name__ == '__main__':
    main()
