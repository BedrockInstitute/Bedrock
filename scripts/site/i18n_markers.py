"""Canonical implementation of Bedrock's i18n marker grammar (see dev/STYLE-i18n.md).

Single source of truth shared by the weaver (weave-i18n.py), the site renderer
(render-site.py), and the marker validator, so the three can never drift. The grammar:

    <!--en-->  English prose.
    <!--zh-->  中文文稿。
    <!--ja-->  日本語の文章。
    <!--/-->

`<!--en-->` / `<!--zh-->` / `<!--ja-->` switch the current prose language; `<!--/-->`
closes the group; prose outside any group is shared (copied to every language); markers
never appear inside a code fence (``` / ~~~), where code is language-neutral.
"""

import re

LANGS = ["en", "zh", "ja"]
FALLBACK = "en"  # language used when a group lacks the requested one

MARKER_RE = re.compile(r"^\s*<!--\s*(en|zh|ja|/)\s*-->\s*$")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
# A comment that looks like a marker but carries an unknown code (e.g. <!--fr-->).
SUSPECT_RE = re.compile(r"^\s*<!--\s*([A-Za-z]{1,8}|/)\s*-->\s*$")
CODE_TOKEN_RE = re.compile(r"^\x00CODE\d+\x00$")
CJK_RE = re.compile(r"[\u3400-\u9fff\u3040-\u30ff]")
LATIN_WORD_RE = re.compile(r"(?<![\w])(?:[A-Za-z]{2,})(?![\w])")
ENGLISH_FUNCTION_WORDS = frozenset("""
    a an and are as at be because by can each for from has have if in into is it its
    may of on or that the their then these this those through to under using was we
    were when where which with
""".split())

FALLBACK_LABEL = {"zh": "英文原文", "ja": "英語原文"}


def marker(line):
    """Return the marker code ('en'/'zh'/'ja'/'/') for a marker line, else None."""
    m = MARKER_RE.match(line)
    return m.group(1) if m else None


def parse(text):
    """Parse a master into an ordered list of segments.

    Each segment is ('shared', [lines]) or ('group', {lang: [lines]}). Raises ValueError
    on a structural marker error (message prefixed with a 1-based line number where known).
    Lines inside a ``` / ~~~ fence are never interpreted as markers."""
    segments = []
    shared = []
    group = None          # dict lang -> [lines] while inside a group
    cur_lang = None
    in_fence = False

    def flush_shared():
        if shared:
            segments.append(("shared", shared[:]))
            shared.clear()

    for n, line in enumerate(text.split("\n"), 1):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            (group[cur_lang] if group else shared).append(line)
            continue
        code = None if in_fence else marker(line)
        if code is None:
            (group[cur_lang] if group else shared).append(line)
            continue
        if code == "/":
            if group is None:
                raise ValueError(f"{n}: stray <!--/--> with no open language group")
            segments.append(("group", group))
            group, cur_lang = None, None
        else:
            if group is None:
                flush_shared()
                group = {}
            cur_lang = code
            group.setdefault(cur_lang, [])
    if group is not None:
        raise ValueError("unterminated language group at end of file (missing <!--/-->)")
    flush_shared()
    return segments


def weave(text, lang):
    """Weave `text` for `lang`: shared lines plus, per group, the `lang` sub-block (falling
    back to English, then the first present language). Collapses runs of blank lines."""
    out = []
    for kind, payload in parse(text):
        if kind == "shared":
            out.extend(payload)
        else:
            chosen = payload.get(lang)
            if chosen is None:
                chosen = payload.get(FALLBACK)
            if chosen is None:
                chosen = next((payload[k] for k in LANGS if k in payload), [])
            out.extend(chosen)
    woven = re.sub(r"\n{3,}", "\n\n", "\n".join(out)).strip("\n")
    return woven + "\n" if woven else ""


def _markdown_blocks(lines):
    """Split prose into blocks while keeping fenced code and Markdown tables intact."""
    blocks = []
    i = 0
    while i < len(lines):
        if not lines[i].strip():
            i += 1
            continue
        line = lines[i]
        if FENCE_RE.match(line):
            fence = FENCE_RE.match(line).group(1)
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].lstrip().startswith(fence):
                    i += 1
                    break
                i += 1
            blocks.append(("protected", block))
            continue
        if CODE_TOKEN_RE.match(line.strip()):
            blocks.append(("protected", [line]))
            i += 1
            continue
        if line.lstrip().startswith("$$"):
            block = [line]
            i += 1
            stripped = line.strip()
            if not (len(stripped) > 4 and stripped.endswith("$$")):
                while i < len(lines):
                    block.append(lines[i])
                    i += 1
                    if block[-1].rstrip().endswith("$$"):
                        break
            blocks.append(("protected", block))
            continue
        if (line.lstrip().startswith("|") and i + 1 < len(lines)
                and re.match(r"^\s*\|?\s*:?-+", lines[i + 1])):
            block = [line, lines[i + 1]]
            i += 2
            while i < len(lines) and lines[i].lstrip().startswith("|"):
                block.append(lines[i])
                i += 1
            blocks.append(("prose", block))
            continue
        block = [line]
        i += 1
        while i < len(lines) and lines[i].strip():
            if FENCE_RE.match(lines[i]) or CODE_TOKEN_RE.match(lines[i].strip()):
                break
            block.append(lines[i])
            i += 1
        blocks.append(("prose", block))
    return blocks


def _is_english_narrative(lines):
    """Recognize an English prose/table block without classifying notation as English."""
    text = "\n".join(lines)
    text = re.sub(r"`[^`]*`", "", text)
    text = re.sub(r"\$[^$]*\$", "", text)
    text = re.sub(r"<[^>]+>", "", text)
    words = LATIN_WORD_RE.findall(text)
    if len(words) < 2:
        return False
    function_words = sum(word.lower() in ENGLISH_FUNCTION_WORDS for word in words)
    cjk_count = len(CJK_RE.findall(text))
    latin_count = sum(ch.isascii() and ch.isalpha() for ch in text)
    if cjk_count:
        # A translated paragraph often retains several identifiers.  Conversely, an
        # English paragraph may contain one translated term in quotation marks.  The
        # latter still has English syntax and overwhelmingly Latin running text.
        return (len(words) >= 5 and function_words >= 2
                and latin_count > 2 * cjk_count)
    if any(line.lstrip().startswith("|") for line in lines):
        return True
    # Function words or sentence punctuation distinguish prose from a bare list of
    # identifiers and technical names such as "Mostowski collapse".
    return function_words >= 1 or bool(re.search(r"[.!?。！？](?:[\s\"')\]]|$)", text))


def _fold_english(lines, lang):
    """Wrap English narrative blocks for a non-English edition; leave code/math shared."""
    if lang == "en":
        return lines
    out = []
    label = FALLBACK_LABEL.get(lang, "English original")
    for kind, block in _markdown_blocks(lines):
        if kind == "prose" and _is_english_narrative(block):
            out.extend([f'<details class="localized-fallback" lang="en">',
                        f'<summary lang="{lang}">{label}</summary>',
                        "", *block, "", "</details>"])
        else:
            out.extend(block)
        out.append("")
    if out:
        out.pop()
    return out


def weave_for_site(text, lang):
    """Weave a page and fold untranslated English narrative in non-English editions.

    Selection follows the canonical marker grammar. English chosen as a missing-language
    fallback, shared English prose, and English-only blocks accidentally embedded in a
    localized branch are folded. Shared code and mathematical notation remain visible.
    """
    out = []
    for kind, payload in parse(text):
        if kind == "shared":
            chosen = payload
        else:
            chosen = payload.get(lang)
            if chosen is None:
                chosen = payload.get(FALLBACK)
            if chosen is None:
                chosen = next((payload[k] for k in LANGS if k in payload), [])
        out.extend(_fold_english(chosen, lang))
    woven = re.sub(r"\n{3,}", "\n\n", "\n".join(out)).strip("\n")
    return woven + "\n" if woven else ""


def group_languages(text):
    """Set of languages that appear in at least one group of `text` (for coverage/banners)."""
    langs = set()
    for kind, payload in parse(text):
        if kind == "group":
            langs.update(payload)
    return langs


def lint_markers(text):
    """Return a sorted list of (lineno, message) marker-integrity problems."""
    problems = []
    try:
        parse(text)
    except ValueError as e:
        msg = str(e)
        ln, _, rest = msg.partition(": ")
        problems.append((int(ln) if ln.isdigit() else 0, rest or msg))
    in_fence = False
    in_group = False
    for n, line in enumerate(text.split("\n"), 1):
        if FENCE_RE.match(line):
            if not in_fence and in_group and re.match(r"^\s*```agda\s*$", line):
                problems.append((n, "Agda code fence inside a language group; code must be shared"))
            in_fence = not in_fence
            continue
        if not in_fence and marker(line):
            in_group = marker(line) != "/"
        if in_fence and marker(line):
            problems.append((n, "language marker inside a code fence (markers are prose-only)"))
        if not in_fence and marker(line) is None and SUSPECT_RE.match(line):
            tok = SUSPECT_RE.match(line).group(1)
            problems.append((n, f"comment <!--{tok}--> looks like a marker but '{tok}' "
                                f"is not a known language code (en/zh/ja) or '/'"))
    return sorted(set(problems))
