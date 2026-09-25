#!/usr/bin/env python3
"""cert/axioms/code_diff.py -- for every PRE-EXISTING .lean file changed between bfd4249 and
ca05d77, strip comments and strings with the stripper of cert/final/source_scan.py and print the
remaining (code) lines that differ.  Run from the repository root."""
import subprocess, difflib
src = open('cert/final/source_scan.py').read()
ns = {}; exec(src[src.index("def strip"):src.index("PAT = {")], ns); strip = ns['strip']
old, new = 'bfd4249', 'ca05d77'
names = subprocess.run(['git', 'diff', '--name-only', f'{old}..{new}', '--', '*.lean'],
                       capture_output=True, text=True).stdout.split()
existed = [f for f in names if subprocess.run(['git', 'cat-file', '-e', f'{old}:{f}']).returncode == 0]
print(f"changed .lean files: {names}\n  of which pre-existing: {existed}")
for f in existed:
    get = lambda r: strip(subprocess.run(['git', 'show', f'{r}:{f}'], capture_output=True, text=True).stdout)
    norm = lambda s: [l.rstrip() for l in s.split('\n') if l.strip()]
    d = [l for l in difflib.unified_diff(norm(get(old)), norm(get(new)), lineterm='', n=0)
         if l[:1] in '+-' and not l.startswith(('+++', '---'))]
    print(f"== {f}: {len(d)} changed code lines after stripping comments")
    for l in d: print("    " + l.strip()[:200])
