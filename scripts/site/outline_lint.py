"""Language-parallel chapter outline validation, independent of source paths."""
import re
from i18n_markers import LANGS, parse

HEADING = re.compile(r'^(#{1,6})\s+(.+)$', re.M)
FENCE = re.compile(r'^```[^\n]*\n.*?^```\s*$', re.M | re.S)
METADATA = re.compile(r'<!--\s*bedrock-routes\b.*?-->', re.S)


def outline_errors(text):
    errors, count = [], 0
    try:
        segments = parse(METADATA.sub('', text))
    except ValueError as error:
        return [str(error)], 0
    for index, (kind, payload) in enumerate(segments):
        if kind == 'shared':
            if HEADING.search(FENCE.sub('', '\n'.join(payload))):
                errors.append('heading outside a language group')
            continue
        headings = {lang: list(HEADING.finditer('\n'.join(payload.get(lang, []))))
                    for lang in LANGS}
        if not any(headings.values()):
            continue
        count += len(headings['en'])
        levels = {lang: [m[1] for m in headings[lang]] for lang in LANGS}
        if not (levels['en'] == levels['zh'] == levels['ja']) or not levels['en']:
            errors.append('headings must have matching en/zh/ja levels')
            continue
        for lang in LANGS:
            block = '\n'.join(payload[lang])
            for match in headings[lang]:
                rest = block[match.end():].strip()
                if not rest:
                    for next_kind, next_payload in segments[index + 1:]:
                        if next_kind == 'shared' and not '\n'.join(next_payload).strip():
                            continue
                        if next_kind == 'shared' and match[1] == '#':
                            shared = '\n'.join(next_payload).strip()
                            if re.fullmatch(r'```agda\n(?:open )?import\s+.*\n```', shared, re.S):
                                continue
                        if next_kind != 'group' or not all(key in next_payload for key in LANGS):
                            break
                        rest = '\n'.join(next_payload[lang]).strip()
                        break
                if not rest or re.match(r'^(#|```|~~~|<|\||[-*] |\d+\. )', rest):
                    errors.append(f'{lang}: heading needs an opening paragraph: {match[2]}')
    return errors, count
