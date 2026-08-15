#!/usr/bin/env python3
# [LJ-1.308] DD4 axis check: is src/L/Condensation.lagda.md inside the AC
# closure, the GCH closure, both or neither?  Method: transitive import walk
# from each declared root, over git-tracked masters under src/.
import re, os, subprocess, tomllib

led = tomllib.load(open('dev/ledger.toml', 'rb'))


def find(key):
    stack = [led]
    while stack:
        o = stack.pop()
        if isinstance(o, dict):
            if key in o and isinstance(o[key], str) and o[key]:
                return o[key]
            stack.extend(o.values())
        elif isinstance(o, list):
            stack.extend(o)
    return None


ac_root = find('ac_root')
gch_root = find('gch_root')
print(f'ac_root  = {ac_root!r}')
print(f'gch_root = {gch_root!r}')

files = subprocess.run(['git', 'ls-files', 'src'], capture_output=True,
                       text=True).stdout.split()
masters = [f for f in files if f.endswith('.lagda.md')]


def mod_of(path):
    return path[len('src/'):-len('.lagda.md')].replace('/', '.')


by_mod = {mod_of(p): p for p in masters}

IMP = re.compile(r'^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.\'-]+)')
deps = {}
for p in masters:
    ds = set()
    for line in open(p):
        m = IMP.match(line)
        if m and m.group(1) in by_mod:
            ds.add(m.group(1))
    deps[mod_of(p)] = ds


def closure(root_path):
    if not root_path or root_path not in by_mod.values():
        return None
    start = mod_of(root_path)
    seen, stack = set(), [start]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(deps.get(m, ()))
    return seen


for name, root in (('AC', ac_root), ('GCH', gch_root)):
    c = closure(root)
    if c is None:
        print(f'{name}: root {root!r} not a tracked master')
        continue
    print(f'{name} closure: {len(c)} masters; '
          f'L.Condensation in it: {"L.Condensation" in c}')

acc = closure(ac_root) or set()
gcc = closure(gch_root) or set()
print(f'shared masters: {len(acc & gcc)}')
print(f'L.Condensation: AC={"L.Condensation" in acc} '
      f'GCH={"L.Condensation" in gcc}')
for cons in ('L.Condensation.LowerAgree', 'L.Condensation.UpperAgree',
             'L.Condensation.TwelveAgree', 'L.Coding.EnvSupply',
             'L.BoundedSubset'):
    print(f'{cons}: AC={cons in acc} GCH={cons in gcc}')
