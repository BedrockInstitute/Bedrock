"""Shared statement vocabulary and source-level statement/QED validation."""
import re

STATEMENT_LABELS = frozenset((
    'Definition', 'Construction', 'Fact', 'Lemma', 'Theorem', 'Corollary',
    '定义', '构造', '事实', '引理', '定理', '推论', '定義', '構成', '事実', '補題', '系'))
PROOF_LABELS = frozenset(('Proof', '证明', '証明'))
CONSTRUCTION_LABELS = frozenset(('Construction', '构造', '構成'))
LABEL_RE = re.compile(r'^\s*\*\*(' + '|'.join(sorted(STATEMENT_LABELS | PROOF_LABELS))
                      + r')(?:\s*\d+)?(?:[.。])?\*\*')
NAME = r'`([^`\s]+)`\{\.Agda\}'
NAMES_RE = re.compile(r'^ \((' + NAME + r'(?: ' + NAME + r')*)\)(?: |$)')
MARKER_RE = re.compile(r'^\s*<!--(en|zh|ja|/)-->\s*$')


def route_lines(text, language):
    """Select a route with fallback while retaining original source offsets."""
    group, current, offset, fence = None, None, 0, False
    for line in text.splitlines(keepends=True):
        marker = None if fence else MARKER_RE.match(line)
        if line.lstrip().startswith(('```', '~~~')):
            fence = not fence
        if marker:
            code = marker[1]
            if code == '/':
                if group:
                    yield from group.get(language, group.get('en', next(iter(group.values()))))
                group, current = None, None
            else:
                if group is None:
                    group = {}
                current = group.setdefault(code, [])
        elif group is None:
            yield offset, line
        else:
            current.append((offset, line))
        offset += len(line)


def statement_issues(text):
    """Each statement owns code and one directly adjacent QED, at every fold depth.

    A Proof continues its statement, or starts a standalone proof. A second
    statement never silently closes the first. A fold creates a nested scope,
    not an exemption; its statements must close before its closing tag.
    """
    issues = set()
    for language in ('en', 'zh', 'ja'):
        scopes = [None]
        fence = None
        code = False
        has_code = False
        last = None

        def report(position, message):
            issues.add((position, message))

        def unfinished(entry):
            if entry:
                report(entry['start'], 'statement/proof must contain Agda code and end with its own standalone ∎')

        for offset, line in route_lines(text, language):
            stripped = line.strip()
            if fence:
                if re.fullmatch(re.escape(fence) + r'\s*', stripped):
                    if code and has_code:
                        for entry in scopes:
                            if entry:
                                entry['code'] += 1
                                if entry['proof'] is not None:
                                    entry['proof_code'] += 1
                    last = 'agda' if code and has_code else 'other'
                    fence = None
                elif stripped:
                    has_code = True
                continue
            opening = re.match(r'^(`{3,}|~{3,})(\w*)\s*$', stripped)
            if opening:
                fence, kind = opening.groups()
                code = kind == 'agda'
                has_code = False
                continue
            if not stripped or re.fullmatch(r'<!--.*-->', stripped):
                continue
            label = LABEL_RE.match(line)
            if label:
                name = label[1]
                if name in PROOF_LABELS:
                    if scopes[-1] is None:
                        scopes[-1] = dict(start=offset, code=0, proof=None, proof_code=0)
                    elif scopes[-1]['proof'] is not None:
                        report(offset, 'one statement must not contain parallel Proof labels')
                    scopes[-1]['proof'] = offset
                else:
                    unfinished(scopes[-1])
                    scopes[-1] = dict(start=offset, code=0, proof=None, proof_code=0)
                last = 'prose'
                continue
            if stripped == '∎':
                entry = scopes[-1]
                if entry is None:
                    report(offset, 'standalone ∎ must close a statement/proof in the same fold')
                elif not entry['code']:
                    report(entry['start'], 'statement/proof must enclose at least one Agda code block')
                if entry and entry['proof'] is not None and not entry['proof_code']:
                    report(entry['proof'], 'Proof must enclose at least one Agda code block before ∎')
                if last != 'agda':
                    report(offset, 'standalone ∎ must immediately follow an Agda code block, inside its fold')
                scopes[-1] = None
                last = 'qed'
                continue
            if re.match(r'^#{1,6}\s', stripped):
                unfinished(scopes[-1])
                scopes[-1] = None
            for tag in re.finditer(r'<(/?)details\b[^>]*>', line):
                if tag[1]:
                    if len(scopes) > 1:
                        unfinished(scopes.pop())
                else:
                    scopes.append(None)
            last = 'other'
        for entry in scopes:
            unfinished(entry)
    return sorted(issues)


def named_group_issues(text):
    """Multiple names use one Construction header and matching bullet entries."""
    issues = set()
    for language in ('en', 'zh', 'ja'):
        lines = list(route_lines(text, language))
        fenced = False
        for index, (offset, line) in enumerate(lines):
            if line.lstrip().startswith(('```', '~~~')):
                fenced = not fenced
            label = None if fenced else LABEL_RE.match(line)
            if not label or label[1] in PROOF_LABELS:
                continue
            names = NAMES_RE.match(line[label.end():].rstrip('\n'))
            if not names:
                continue  # The label-format check supplies the precise diagnostic.
            declared = re.findall(NAME, names[1])
            if len(declared) < 2:
                continue
            if label[1] not in CONSTRUCTION_LABELS:
                issues.add((offset, 'multiple names require one Construction header and a bullet per name'))
            following = [value.strip() for _, value in lines[index + 1:] if value.strip()]
            for number, name in enumerate(declared):
                expected = '- `' + name + '`{.Agda} '
                if number >= len(following) or not following[number].startswith(expected):
                    issues.add((offset, 'grouped Construction requires ordered bullets, each starting with its declared Agda name'))
                    break
    return sorted(issues)
