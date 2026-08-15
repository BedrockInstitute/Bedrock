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
    for n, line in enumerate(text.split("\n"), 1):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if in_fence and marker(line):
            problems.append((n, "language marker inside a code fence (markers are prose-only)"))
        if not in_fence and marker(line) is None and SUSPECT_RE.match(line):
            tok = SUSPECT_RE.match(line).group(1)
            problems.append((n, f"comment <!--{tok}--> looks like a marker but '{tok}' "
                                f"is not a known language code (en/zh/ja) or '/'"))
    return sorted(set(problems))
