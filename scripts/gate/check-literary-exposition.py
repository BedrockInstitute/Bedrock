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
from chapter_structure import boilerplate_ranges, chapter_parts, parameterized
from submodule_structure import module_header_line

from literary_lint import *
from literary_lint import analyze_text as analyze_document

def analyze_text(text, name='<memory>'):
    module = ''
    internal = ()
    if name != '<memory>':
        path = pathlib.Path(name).resolve()
        if path.is_relative_to(ROOT / 'src'):
            module = str(path.relative_to(ROOT / 'src'))[:-9].replace('/', '.')
            internal = {str(p.relative_to(ROOT/'src'))[:-9].replace('/', '.')
                        for p in (ROOT/'src').rglob('*.lagda.md')}
    return analyze_document(text, name, module=module, internal=internal,
                            visible_import_chapters={'Origin'})

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
