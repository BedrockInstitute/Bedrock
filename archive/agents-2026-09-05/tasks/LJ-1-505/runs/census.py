import re
src=open('src/L/Condensation/TwelveAgree.lagda.md').read().split('\n')
body=src[131:332]
fields=[]; cur=None
for i,l in enumerate(body):
    m=re.match(r"^    ([A-Za-z][A-Za-z0-9'₀₁₂\-]*) : ",l)
    if m:
        if cur: fields.append(cur)
        cur=[m.group(1),131+i+1,[l]]
    elif cur is not None:
        cur[2].append(l)
if cur: fields.append(cur)
print("fields parsed:",len(fields))
hits={}
for name,ln,ls in fields:
    blob=re.sub(r'\s+',' ',' '.join(ls))
    depths=set()
    for m in re.finditer(r"\(((?:[A-Za-z][A-Za-z0-9']* ∷ )+)γ'\)",blob):
        depths.add(m.group(1).count('∷'))
    for m in re.finditer(r"lookup ((?:\(suc )+)zero\)+ γ'",blob):
        k=m.group(1).count('(suc')
        hits.setdefault(k,set()).add(('LOOKUP',name,ln))
    if "lookup zero γ'" in blob:
        hits.setdefault(0,set()).add(('LOOKUP',name,ln))
    if depths:
        d=max(depths)
        for m in re.finditer(r"((?:\(suc )+)zero\)+",blob):
            k=m.group(1).count('(suc')
            if k-d>=0:
                hits.setdefault(k-d,set()).add(('FORMULA-ARG',name,ln,'suc^%d over depth %d'%(k,d)))
for k in sorted(hits):
    if k<=5:
        print("=== gamma' slot %d : %d references"%(k,len(hits[k])))
        for h in sorted(hits[k],key=lambda x:x[2]): print("   ",h)
for k in sorted(hits):
    if k>5: print("slot %d (K/N region): %d refs"%(k,len(hits[k])))
