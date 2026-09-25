#!/usr/bin/env python3
"""cert/final/source_scan.py -- forbidden-construct scan of every .lean source of the library
(Zeta5.lean and Zeta5/**.lean), after stripping comments (nested /- -/, --) and string
literals, so that words inside doc-strings do not count and code hidden after a comment
marker cannot escape.  Usage: python3 cert/final/source_scan.py  (from the repository root)."""
import re, pathlib, sys
root = pathlib.Path('.')
files = [root/'Zeta5.lean'] + sorted((root/'Zeta5').rglob('*.lean'))

def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth:
            if src.startswith('/-', i): depth += 1; i += 2; continue
            if src.startswith('-/', i): depth -= 1; i += 2; continue
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('/-', i): depth = 1; i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('"' + ' ' * (j - i - 1) + '"'); i = j + 1; continue
        if src[i] == "'" and i + 2 < n and src[i+2] == "'":   # char literal 'x'
            out.append("' '"); i += 3; continue
        out.append(src[i]); i += 1
    return ''.join(out)

PAT = {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'sorryAx': r'sorryAx',
 'native_decide': r'native_decide', 'implemented_by': r'implemented_by', 'extern': r'\bextern\b',
 'unsafe': r'\bunsafe\b', 'partial def': r'\bpartial\b', 'opaque': r'\bopaque\b',
 'axiom': r'\baxiom\b', 'constant': r'^\s*constant\b',
 'skipKernelTC': r'skipKernelTC', 'ofReduceBool/Nat': r'ofReduce(Bool|Nat)', 'reduceBool': r'reduceBool',
 'Decidable.decide trust': r'trustCompiler|Lean\.trustCompiler',
 'set_option': r'\bset_option\b', 'macro': r'\bmacro(_rules)?\b', 'elab': r'\belab(_rules)?\b',
 'syntax': r'\bsyntax\b', 'notation': r'\b(notation|infixl?r?|prefix|postfix)\b',
 'attribute': r'\battribute\b', 'run_cmd/tac/elab': r'\brun_(cmd|tac|elab|meta)\b', '#eval': r'#eval',
 'initialize': r'\b(builtin_)?initialize\b', 'open private': r'open\s+private',
 'export': r'^\s*export\b', 'csimp': r'csimp', 'instance': r'\binstance\b',
 'debug options': r'\bdebug\.', 'Lean.Elab/Meta import': r'^\s*import\s+Lean\b',
 'unsafeCast/ptrEq': r'unsafeCast|ptrEq|unsafeBaseIO|unsafeIO',
 'import': r'^\s*import\b',
}
hits = {k: [] for k in PAT}
nlines = 0
for f in files:
    s = strip(f.read_text())
    for ln, line in enumerate(s.split('\n'), 1):
        nlines += 1
        for k, p in PAT.items():
            if re.search(p, line):
                hits[k].append(f"{f}:{ln}: {line.strip()[:160]}")
print(f"files scanned: {len(files)}; lines: {nlines}")
for k, v in hits.items():
    if k in ('import',):
        continue
    print(f"== {k}: {len(v)}")
    for h in v: print("    " + h)
imps = sorted({h.split(': ',1)[1] for h in hits['import']})
print("== distinct imports:")
for i in imps: print("    " + i)
