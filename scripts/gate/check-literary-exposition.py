#!/usr/bin/env python3
"""Check fence-local trilingual exposition in literate Agda chapters.

The gate is intentionally structural: ratios are reported, never required.  With
``--check`` any structural error makes the command fail; without it this is a
read-only inventory report and exits successfully.
"""
from __future__ import annotations
import argparse, json, pathlib, re, sys
HERE=pathlib.Path(__file__).resolve(); ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'scripts/site'))
from i18n_markers import LANGS, _is_english_narrative, _markdown_blocks, marker
from reading_routes import strip_metadata

FENCE_OPEN=re.compile(r'^```agda(?:\s.*)?$')
FENCE_CLOSE=re.compile(r'^```\s*$')
HTML=re.compile(r'<!--.*?-->',re.S); INLINE=re.compile(r'`[^`]*`|\$[^$]*\$')
LINE_COMMENT=re.compile(r'(?:^|\s)--(?:\s|$|-)')
BLOCK_OPEN=re.compile(r'\{-(?!#)')
HEADING=re.compile(r'^\s*#{1,6}\s+',re.M)

def visible_chars(text:str)->int:
    text=HTML.sub('',text); text=INLINE.sub('',text)
    text=re.sub(r'^\s{0,3}(?:#{1,6}|[-*+]>?|\d+[.)])\s*','',text,flags=re.M)
    text=re.sub(r'[\s*_~\[\]()<>|#]','',text)
    return len(text)

def explanation_chars(lines:list[str])->int:
    kept=[line for line in lines if not HEADING.match(line)]
    return visible_chars('\n'.join(kept))

def _shared_prose(lines:list[str])->list[tuple[bool,str]]:
    hits=[]
    for kind,block in _markdown_blocks(lines):
        if kind!='prose': continue
        text='\n'.join(block)
        if visible_chars(text): hits.append((_is_english_narrative(block),text))
    return hits

def analyze_text(text:str,name:str='<memory>')->dict:
    # Route JSON is neutral only when it matches the repository's validated marker.
    clean=strip_metadata(text)
    errors=[]; fences=[]; groups=[]; shared=[]
    cur_group=None; group_start=None; cur_lang=None; shared_buf=[]; in_fence=False; fence_lines=[]; fence_start=0
    last_narrative=None; in_block_comment=False
    def flush_shared():
        nonlocal shared_buf
        if shared_buf: shared.extend(_shared_prose(shared_buf)); shared_buf=[]
    def close_group(line_no):
        nonlocal cur_group,group_start,last_narrative
        if cur_group is None:
            errors.append({'line':line_no,'rule':'marker','message':'stray language-group close'})
            return
        narrative=any(visible_chars('\n'.join(v))>0 for v in cur_group.values())
        if narrative:
            missing=[x for x in LANGS if x not in cur_group or visible_chars('\n'.join(cur_group[x]))==0]
            if missing: errors.append({'line':group_start,'rule':'trilingual-group','message':'narrative group lacks nonempty language block: '+', '.join(missing)})
            elif all(explanation_chars(cur_group[x])>0 for x in LANGS):
                last_narrative={x:explanation_chars(cur_group[x]) for x in LANGS}
        groups.append(cur_group); cur_group=None; group_start=None
    for n,line in enumerate(clean.splitlines(),1):
        if in_fence:
            if FENCE_CLOSE.match(line):
                nonempty=sum(bool(x.strip()) for x in fence_lines)
                if not 1<=nonempty<=5: errors.append({'line':fence_start,'rule':'fence-size','message':f'Agda fence has {nonempty} nonempty lines; expected 1..5'})
                if last_narrative is None: errors.append({'line':fence_start,'rule':'preceding-exposition','message':'Agda fence has no preceding complete en/zh/ja narrative group'})
                fences.append({'line':fence_start,'total_lines':len(fence_lines),'nonempty_lines':nonempty,'preceding_exposition_chars':last_narrative})
                in_fence=False; fence_lines=[]; in_block_comment=False; last_narrative=None
            else:
                fence_lines.append(line)
                # STYLE-agda explicitly permits this machine-readable import
                # directive. It is not explanatory prose and must survive weaving.
                checked_line=re.sub(r'\s+-- lint-agda: keep\b.*$','',line)
                if in_block_comment or BLOCK_OPEN.search(checked_line) or LINE_COMMENT.search(checked_line):
                    errors.append({'line':n,'rule':'prose-in-code','message':'commentary cannot be hidden inside an Agda fence'})
                if BLOCK_OPEN.search(line) and '-}' not in line[line.find('{-')+2:]: in_block_comment=True
                if in_block_comment and '-}' in line: in_block_comment=False
            continue
        if FENCE_OPEN.match(line):
            flush_shared(); in_fence=True; fence_start=n; fence_lines=[]; continue
        code=marker(line)
        if code:
            flush_shared()
            if code=='/': close_group(n); cur_lang=None
            else:
                if cur_group is None: cur_group={}; group_start=n
                cur_lang=code; cur_group.setdefault(code,[])
            continue
        if cur_group is not None:
            cur_group[cur_lang].append(line)
        else: shared_buf.append(line)
    flush_shared()
    if in_fence: errors.append({'line':fence_start,'rule':'fence','message':'unterminated Agda fence'})
    if cur_group is not None: errors.append({'line':group_start,'rule':'marker','message':'unterminated language group'})
    for english,block in shared:
        errors.append({'line':None,'rule':'shared-prose','message':('English narrative' if english else 'narrative')+' appears outside a language group','excerpt':block[:100]})
    explicit={x:0 for x in LANGS}
    for g in groups:
        for x in LANGS:
            if x in g: explicit[x]+=visible_chars('\n'.join(g[x]))
    # Re-scan because fence records intentionally store only counts, not source text.
    bodies=re.findall(r'^```agda[^\n]*\n(.*?)^```[ \t]*$',clean,re.M|re.S)
    codechars=sum(len(line) for body in bodies for line in body.splitlines())
    return {'file':name,'fence_count':len(fences),'fences':fences,'explicit_prose_chars':explicit,'code_chars':codechars,'explicit_prose_to_code_ratio':{x:round(explicit[x]/codechars,4) if codechars else None for x in LANGS},'errors':errors}

def analyze_path(path:pathlib.Path)->dict:
    return analyze_text(path.read_text(encoding='utf-8'),str(path))

def main(argv=None):
    ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); ap.add_argument('--json',action='store_true'); ap.add_argument('files',nargs='*',type=pathlib.Path); a=ap.parse_args(argv)
    files=a.files or sorted((ROOT/'src').rglob('*.lagda.md')); reports=[analyze_path(p) for p in files]
    errors=sum(len(r['errors']) for r in reports); code=sum(r['code_chars'] for r in reports); prose={x:sum(r['explicit_prose_chars'][x] for r in reports) for x in LANGS}
    summary={'files':len(reports),'fences':sum(r['fence_count'] for r in reports),'errors':errors,'code_chars':code,'explicit_prose_chars':prose,'explicit_prose_to_code_ratio':{x:round(prose[x]/code,4) if code else None for x in LANGS}}
    if a.json: print(json.dumps({'summary':summary,'files':reports},ensure_ascii=False,indent=2))
    else:
        for r in reports:
            for e in r['errors']: print(f"{r['file']}:{e['line'] or '?'}: [{e['rule']}] {e['message']}")
        print('literary-exposition: '+json.dumps(summary,ensure_ascii=False))
    return 1 if a.check and errors else 0
if __name__=='__main__': raise SystemExit(main())
