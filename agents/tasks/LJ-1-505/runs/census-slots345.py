import re
src=open('src/L/Condensation/TwelveAgree.lagda.md').read().split('\n')
body=src[131:332]
fields=[]; cur=None
for i,l in enumerate(body):
    m=re.match(r"^    ([A-Za-z][A-Za-z0-9'₀₁₂\-]*) : ",l)
    if m:
        if cur: fields.append(cur)
        cur=[m.group(1),131+i+1,[l]]
    elif cur is not None: cur[2].append(l)
if cur: fields.append(cur)
risk={3:[],4:[],5:[]}
for name,ln,ls in fields:
    blob=re.sub(r'\s+',' ',' '.join(ls))
    depths=sorted({m.group(1).count('∷') for m in re.finditer(r"\(((?:[A-Za-z][A-Za-z0-9']* ∷ )+)γ'\)",blob)})
    if not depths: continue
    args=sorted({m.group(1).count('(suc') for m in re.finditer(r"((?:\(suc )+)zero\)+",blob)})
    for d in depths:
        for k in args:
            if k-d in (3,4,5):
                risk[k-d].append((name,ln,'suc^%d over depth %d'%(k,d),depths))
for s in (3,4,5):
    print("=== slot %d : %d candidate references under ANY prefix depth"%(s,len(risk[s])))
    for r in risk[s]: print("   ",r)
