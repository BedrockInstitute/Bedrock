#!/usr/bin/env python3
# [LJ-1.308] Independent re-derivation of [LJ-1.306]'s "0 of 4,738 changed".
# METHOD (deliberately different from the manifest verbatim-run search):
#   1. Build the EXPECTED copy text by concatenating the chapter spans in
#      manifest order.
#   2. Align it against the port's post-scaffold region with difflib, which
#      is a whole-sequence diff and not a per-block run search.
#   3. Report every insertion, deletion and replacement.
#   4. Independently, mark every port line covered by a verbatim block run,
#      and count the uncovered non-blank lines.
import json, difflib, re, sys

PORT = 'agents/tasks/LJ-1-306/GenAgree.agda'
CHAP = 'src/L/Condensation.lagda.md'
SHAPE = 'src/L/Coding/Shape.lagda.md'
MANI = 'agents/tasks/LJ-1-306/manifest.json'

port = open(PORT).read().split('\n')
chap = open(CHAP).read().split('\n')
shape = open(SHAPE).read().split('\n')
mani = json.load(open(MANI))


def nb(lines):
    return sum(1 for l in lines if l.strip())


# ---------- 1. span arithmetic ----------
span_lines = 0
span_nb = 0
expected = []
for a, b, name in mani:
    seg = chap[a - 1:b]
    span_lines += len(seg)
    span_nb += nb(seg)
    expected.extend(seg)
print(f'manifest blocks           : {len(mani)}')
print(f'chapter span lines        : {span_lines}')
print(f'chapter span non-blank    : {span_nb}')

# ---------- 2. verbatim run search, my own ----------
port_text = '\n'.join(port)
covered = [False] * len(port)
missing = []
for a, b, name in mani:
    seg = chap[a - 1:b]
    # find the exact contiguous run in the port
    found = -1
    n = len(seg)
    for i in range(len(port) - n + 1):
        if port[i:i + n] == seg:
            found = i
            break
    if found < 0:
        missing.append((a, b, name))
    else:
        for j in range(found, found + n):
            covered[j] = True
print(f'blocks NOT found verbatim : {len(missing)}')
for m in missing:
    print('   MISSING', m)

# ---------- 3. whole-sequence diff ----------
sm = difflib.SequenceMatcher(a=expected, b=port, autojunk=False)
ops = sm.get_opcodes()
ins = dele = repl = 0
ins_nb = del_nb = repl_nb_a = repl_nb_b = 0
repl_detail = []
for tag, i1, i2, j1, j2 in ops:
    if tag == 'insert':
        ins += j2 - j1
        ins_nb += nb(port[j1:j2])
    elif tag == 'delete':
        dele += i2 - i1
        del_nb += nb(expected[i1:i2])
    elif tag == 'replace':
        repl += 1
        repl_nb_a += nb(expected[i1:i2])
        repl_nb_b += nb(port[j1:j2])
        repl_detail.append((i1, i2, j1, j2))
print(f'diff: inserted port lines {ins} ({ins_nb} non-blank)')
print(f'diff: deleted expected    {dele} ({del_nb} non-blank)')
print(f'diff: replace hunks       {repl} '
      f'(expected nb {repl_nb_a} -> port nb {repl_nb_b})')
for (i1, i2, j1, j2) in repl_detail[:40]:
    print(f'  REPLACE expected[{i1}:{i2}] -> port[{j1 + 1}:{j2 + 1}]')
    for l in expected[i1:i2][:6]:
        print('    - ' + l[:110])
    for l in port[j1:j2][:6]:
        print('    + ' + l[:110])

# ---------- 4. uncovered port lines ----------
unc = [(i + 1, port[i]) for i in range(len(port)) if not covered[i]]
unc_nb = [(i, l) for i, l in unc if l.strip()]
print(f'port total lines          : {len(port)}')
print(f'port non-blank            : {nb(port)}')
print(f'port lines uncovered      : {len(unc)}')
print(f'port NON-BLANK uncovered  : {len(unc_nb)}')

# classify uncovered non-blank lines
comment = [x for x in unc_nb if x[1].lstrip().startswith('--')]
code = [x for x in unc_nb if not x[1].lstrip().startswith('--')]
print(f'  of which comment lines  : {len(comment)}')
print(f'  of which CODE lines     : {len(code)}')
with open('agents/tasks/LJ-1-308/uncovered.txt', 'w') as f:
    for i, l in unc_nb:
        f.write(f'{i}\t{l}\n')
print('uncovered non-blank lines written to agents/tasks/LJ-1-308/uncovered.txt')
