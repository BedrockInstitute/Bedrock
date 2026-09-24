#!/usr/bin/env python3
"""Mechanically normalize chapter openings; preserve every nonblank code line.

Run once for the 2026-09 chapter-opening migration. Reject ambiguous input rather
than silently moving a local import or changing a module interface.
"""
from collections import Counter
from pathlib import Path
import re
import sys
import json
import subprocess
from outcrop.core.chapter_structure import FENCE, chapter_parts, opening_errors, parameterized, fence

root = Path('src')
paths = sorted(root.rglob('*.lagda.md'))
internal = {str(p.relative_to(root))[:-9].replace('/', '.') for p in paths}
catalog = {entry['id']: entry['title'] for entry in json.loads(Path('dev/reading-catalog.json').read_text())['chapters']}


def code_lines(text):
    return Counter(line for f in FENCE.finditer(text) for line in f['code'].splitlines() if line.strip())


for path in paths:
    module = str(path.relative_to(root))[:-9].replace('/', '.')
    original = path.read_text()
    if not opening_errors(original, module, internal):
        continue
    options, declaration, needed, project = chapter_parts(original, module, internal)
    selected = [options, *needed, declaration, *project]
    # Remove physical code lines, not the intervening literary explanation.
    ranges = [(s.start, s.end) for s in selected]
    def clean_fence(match):
        offset = match.start('code')
        kept = []
        for line in match['code'].splitlines(keepends=True):
            if not any(start <= offset < end for start, end in ranges):
                kept.append(line)
            offset += len(line)
        code = ''.join(kept).strip('\n')
        return '```agda\n' + code + '\n```' if code.strip() else ''
    body = FENCE.sub(clean_fence, original)
    titles = {}
    for lang in ('en', 'zh', 'ja'):
        pattern = r'(<!--' + lang + r'-->\n)# ([^\n]+)\n'
        found = re.search(pattern, body)
        if not found:
            titles[lang] = catalog[module][lang]
            continue
        titles[lang] = found[2]
        body = body[:found.start()] + found[1] + body[found.end():]
    body = re.sub(r'(?:<!--(?:en|zh|ja)-->\s*)+<!--/-->\s*', '', body)
    body = re.sub(r'\n{3,}', '\n\n', body).strip()
    has_parameters = parameterized(declaration, module)
    parameter_prose = ''
    if has_parameters:
        # Reuse the chapter's existing parameter introduction when available.
        old = subprocess.check_output(['git', 'show', f'HEAD:{path}'], text=True)
        _, old_declaration, _, _ = chapter_parts(old, module, internal)
        groups = list(re.finditer(r'<!--en-->\n.*?<!--/-->', original[:declaration.start], re.S))
        if not groups:
            groups = list(re.finditer(r'<!--en-->\n.*?<!--/-->', old[:old_declaration.start], re.S))
        if groups:
            candidate = groups[-1][0]
            if (candidate in body and all('<!--'+lang+'-->' in candidate for lang in ('zh','ja'))
                    and re.search(r'ℓ|ZFStructure|pr-inj|universe|level', candidate)
                    and not re.search(r'^#', candidate, re.M)):
                parameter_prose = candidate + '\n\n'
                body = body.replace(candidate, '', 1).strip()
        if not parameter_prose:
            if 'LEM' in declaration.text:
                level = 'ℓ-suc ℓ' if 'ℓ-suc' in declaration.text else 'ℓ'
                paragraphs = [f'Fix a universe level `ℓ`{{.Agda}} and assume `lem : LEM ({level})`{{.Agda}}. This hypothesis supplies a decision for each proposition at that level; it remains an explicit parameter of the constructions below.', f'固定宇宙层级 `ℓ`{{.Agda}}，并假设 `lem : LEM ({level})`{{.Agda}}。这个假设为相应层级的每个命题提供判定，并始终作为下文构造的显式参数。', f'宇宙レベル `ℓ`{{.Agda}} を固定し、`lem : LEM ({level})`{{.Agda}} を仮定する。この仮定は該当するレベルの各命題に判定を与え、以下の構成の明示的なパラメータとして保たれる。']
            elif 'ZFStructure' in declaration.text:
                paragraphs = ['Fix a structure `𝒮 : ZFStructure ℓ`{.Agda}. Its carrier and its equality and membership relations give the interpretation in which the constructions below take place.', '固定结构 `𝒮 : ZFStructure ℓ`{.Agda}。下文的构造以其载体、等词与隶属关系为解释。', '構造 `𝒮 : ZFStructure ℓ`{.Agda} を固定する。以下の構成は、その台と等号・所属関係による解釈のもとで行う。']
            else:
                level = 'ℓₚ' if 'ℓₚ' in declaration.text else 'ℓ'
                paragraphs = [f'Fix a universe level `{level}`{{.Agda}}. Keeping the level as a parameter lets the constructions be instantiated at each required size without identifying distinct universes.', f'固定宇宙层级 `{level}`{{.Agda}}。保留这个层级参数，使构造可以在所需的各个大小处实例化，而不必把不同的宇宙视为同一个。', f'宇宙レベル `{level}`{{.Agda}} を固定する。このレベルをパラメータとして保つことで、異なる宇宙を同一視せずに、必要な大きさで構成を具体化できる。']
            parameter_prose = ''.join(f'<!--{lang}-->\n{paragraph}\n' for lang, paragraph in zip(('en','zh','ja'), paragraphs)) + '<!--/-->\n\n'
    header = fence([options] if has_parameters else [options, declaration])
    title = ''.join(f'<!--{lang}-->\n# {titles[lang]}\n' for lang in titles) + '<!--/-->\n\n'
    imports = ('```agda\n' + '\n'.join(s.text for s in project) + '\n```\n\n') if project else ''
    parameter_setup = fence(needed) + parameter_prose + fence([declaration]) if has_parameters else ''
    result = header + title + parameter_setup + imports + body + '\n'
    assert code_lines(original) == code_lines(result), path
    assert not opening_errors(result, module, internal), (path, opening_errors(result, module, internal))
    path.write_text(result)
print(f'Migrated {len(paths)} chapters; nonblank code-line multisets unchanged.')
