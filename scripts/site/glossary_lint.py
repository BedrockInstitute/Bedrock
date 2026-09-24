"""Glossary spelling and translation-presence contracts over supplied text."""
import re
import json
import tomllib
from i18n_markers import parse
from prose_lint import build_protected, EXCLUDE_BASENAMES, ROUTE_METADATA_RE
CJK_LANGS = ("zh", "ja")
PROSE_LANGS = ("en", "zh", "ja")

MARKER_RE = re.compile(r"^\s*<!--\s*(en|zh|ja|/)\s*-->\s*$")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
IGNORE_RE = re.compile(r"<!--\s*glossary-ignore(?::([^>]*?))?\s*-->")


# ---- glossary data -----------------------------------------------------------

def load_glossary(path):
    """Parse dev/glossary.toml into (term, zh, ja, avoid, presence) rows.

    `avoid` is a list of known wrong renderings (each optionally `en:`/`zh:`/`ja:`-tagged);
    `presence` is the safety-net opt-in bool. Array order is preserved (tomllib keeps it).
    The `category` and `notes` fields are human-only and ignored here."""
    with open(path, "rb") as fh:
        data = tomllib.load(fh)
    return [(t["en"], t["zh"], t["ja"], t.get("avoid", []), bool(t.get("presence", False)))
            for t in data.get("term", [])]


def build_checks(rows):
    """Expand rows into Avoid-check tuples: (forbidden, lang, term, canonical_rendering)."""
    checks = []
    for term, zh, ja, avoid, _presence in rows:
        canon = {"en": term, "zh": zh, "ja": ja}
        for item in avoid:
            item = item.strip()
            if not item:
                continue
            if ":" in item:
                tag, _, forb = item.partition(":")
                tag, forb = tag.strip(), forb.strip()
                langs = [tag] if tag in PROSE_LANGS else list(CJK_LANGS)
            else:
                forb, langs = item, list(CJK_LANGS)
            for lang in langs:
                if forb:
                    checks.append((forb, lang, term, canon[lang]))
    return checks


def build_presence(rows):
    """Presence-check terms (opt-in via the `presence` flag): (term, zh, ja)."""
    return [(term, zh, ja) for term, zh, ja, _avoid, presence in rows if presence]


# ---- per-line language scope -------------------------------------------------

def master_line_langs(text):
    """Per-line language for a master: 'zh'/'ja'/'en'/'shared'/'code'/'marker'."""
    out = []
    in_fence = False
    in_group = False
    cur = None
    for line in text.split("\n"):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            out.append("code")
            continue
        if in_fence:
            out.append("code")
            continue
        m = MARKER_RE.match(line)
        if m:
            code = m.group(1)
            if code == "/":
                in_group, cur = False, None
            else:
                in_group, cur = True, code
            out.append("marker")
            continue
        out.append(cur if (in_group and cur in CJK_LANGS) else ("en" if in_group else "shared"))
    return out


def parse_ignores(text):
    """(set of fully-suppressed line numbers, {lineno: {term, ...}} for scoped ignores)."""
    suppress_all = set()
    suppress_term = {}
    for ln, line in enumerate(text.split("\n"), 1):
        for m in IGNORE_RE.finditer(line):
            scope = m.group(1)
            if scope and scope.strip():
                terms = {t for t in re.split(r"[,\s]+", scope.strip()) if t}
                suppress_term.setdefault(ln, set()).update(terms)
            else:
                suppress_all.add(ln)
    return suppress_all, suppress_term


# ---- file check --------------------------------------------------------------

def check_text(text, checks, scope="master"):
    lines = text.split("\n")
    if scope in PROSE_LANGS:
        line_lang = [scope] * len(lines)
    else:  # master
        line_lang = master_line_langs(text)

    prot = build_protected(text)
    suppress_all, suppress_term = parse_ignores(text)

    violations = []
    for forb, lang, term, canon in checks:
        matches = _en_word_re(forb).finditer(text) if lang == "en" else re.finditer(re.escape(forb), text)
        for m in matches:
            idx = m.start()
            if prot[idx]:
                continue
            ln = text.count("\n", 0, idx) + 1
            if ln - 1 >= len(line_lang) or line_lang[ln - 1] != lang:
                continue
            if ln in suppress_all or term in suppress_term.get(ln, ()):
                continue
            violations.append(
                (ln, idx, f"{forb!r} is an off-glossary rendering of \"{term}\"; "
                          f"use {canon} ({lang})"))
    return violations


def master_presence_violations(path, text, terms):
    """Check only explicitly translated groups; English fallback is not translation."""
    hits = []
    try:
        segments = parse(text)
    except ValueError:
        return []  # Marker validity has its own gate and precise source locations.
    for index, (kind, payload) in enumerate(segments, 1):
        if kind != "group" or "en" not in payload:
            continue
        english = "\n".join(payload["en"])
        for lang in CJK_LANGS:
            if lang not in payload:
                continue
            for _, message in presence_violations(path, lang, english,
                                                  "\n".join(payload[lang]), terms):
                hits.append((path, f"language group {index}: {message}"))
    return hits


def route_metadata_violations(text, checks):
    """The invisible annotation contains visible, language-tagged website copy."""
    def translations(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key in PROSE_LANGS and isinstance(item, str):
                    yield key, item
                else:
                    yield from translations(item)
        elif isinstance(value, list):
            for item in value:
                yield from translations(item)

    hits = []
    for match in ROUTE_METADATA_RE.finditer(text):
        try:
            metadata = json.loads(re.search(r"\{.*\}", match[0], re.S)[0])
        except (ValueError, TypeError):
            continue  # reading_routes validates the JSON/schema separately.
        for language, prose in translations(metadata):
            protected = build_protected(prose)
            for forbidden, lang, term, canonical in checks:
                if language != lang:
                    continue
                pattern = _en_word_re(forbidden) if lang == "en" else re.compile(re.escape(forbidden))
                if _has_unprotected(prose, protected, pattern.finditer):
                    hits.append(f"route metadata: {forbidden!r} must use {canonical} ({lang}; {term})")
    return hits


# ---- presence safety net -----------------------------------------------------
# When an English term appears in a doc's English source but the canonical rendering is
# absent from the parallel translation, the translator likely used an off-glossary rendering
# the Avoid list does not enumerate. Opt-in per term (the Presence column), and only on
# standalone parallel docs and each explicitly translated group of a literate master.

def _read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def _en_word_re(term):
    """Match the English term as a word (ASCII-letter boundaries; ok next to CJK/punct)."""
    return re.compile(r"(?<![A-Za-z])" + re.escape(term) + r"(?![A-Za-z])", re.IGNORECASE)


def _has_unprotected(text, prot, finditer):
    return any(not prot[m.start()] for m in finditer(text))


def _present(text, prot, needle):
    i = text.find(needle)
    while i != -1:
        if not prot[i]:
            return True
        i = text.find(needle, i + 1)
    return False


def presence_violations(target_path, lang, en_text, target_text, presence_terms):
    en_prot = build_protected(en_text)
    t_prot = build_protected(target_text)
    suppress_all, suppress_term = parse_ignores(target_text)
    suppressed_terms = set().union(*suppress_term.values()) if suppress_term else set()
    out = []
    for term, zh, ja in presence_terms:
        canon = zh if lang == "zh" else ja
        if not canon:
            continue
        if suppress_all or term in suppressed_terms:
            continue
        if not _has_unprotected(en_text, en_prot, _en_word_re(term).finditer):
            continue
        if _present(target_text, t_prot, canon):
            continue
        out.append((target_path, f"\"{term}\" appears in the English source but its canonical "
                                 f"{lang} rendering {canon} is absent here; verify the "
                                 f"translation (the Avoid list may not cover the rendering used)"))
    return out



__all__ = [name for name in globals() if not name.startswith("__")]
