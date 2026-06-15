#!/usr/bin/env python3
"""Glossary checker for Bedrock: flags off-glossary term renderings in the CJK docs.

The canonical glossary is the Markdown table in dev/GLOSSARY.md (which is both the human
reference and this checker's data, so the two can never drift). Each row gives a term's
canonical Chinese and Japanese rendering plus an `Avoid` list of known wrong renderings.
This script scans the trilingual docs and reports any avoided rendering, pointing at the
canonical one.

Language scoping: a `zh:`-tagged avoid term is only flagged in Chinese context, a `ja:`-tagged
one only in Japanese context, and an untagged term in both. Chinese context is `docs/zh/**`
and the `<!--zh-->` prose of `src/**.lagda.md` masters; Japanese context is `docs/ja/**` and
`<!--ja-->` prose. English docs and shared/neutral prose are not checked.

Report-only (like the em-dash rule): there is no --fix, because the correct rendering is a
translation judgement, not a mechanical substitution. Code spans, fenced blocks, link
destinations and URLs are protected (shared with lint-prose.py). Put `<!-- glossary-ignore -->`
on a line to suppress it, or `<!-- glossary-ignore: charter -->` to suppress one term.

Usage:
  check-glossary.py [--check] [--staged] [FILE ...]
  default mode is --check; with no FILE and no --staged, scans git-tracked *.md/*.lagda.md.
Exit status: 0 clean, 1 violations, 2 usage error.
"""

import importlib.util
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
GLOSSARY = "dev/GLOSSARY.md"


def _load(modname, filename):
    """Load a sibling script as a module (lint-prose.py's hyphen blocks a plain import)."""
    spec = importlib.util.spec_from_file_location(modname, os.path.join(HERE, filename))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_lp = _load("lint_prose", "lint-prose.py")
build_protected = _lp.build_protected          # reuse the exact protected-region mask
EXCLUDE_BASENAMES = _lp.EXCLUDE_BASENAMES       # reuse the LICENSE/NOTICE exclusions

CJK_LANGS = ("zh", "ja")
COL = {"zh": 1, "ja": 2}                         # table column index of each canonical rendering

MARKER_RE = re.compile(r"^\s*<!--\s*(en|zh|ja|/)\s*-->\s*$")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
IGNORE_RE = re.compile(r"<!--\s*glossary-ignore(?::([^>]*?))?\s*-->")


# ---- glossary table ----------------------------------------------------------

def _cell(c):
    """A table cell, with any inline-code backticks stripped.

    CJK renderings are wrapped in `…` in the table so the prose linter leaves their
    half-width `:`/`;` separators alone; the backticks are not part of the value."""
    return c.strip().strip("`").strip()


def _cells(line):
    """Cells of a Markdown table row (leading-`|` lines only), else None."""
    s = line.strip()
    if not s.startswith("|"):
        return None
    return [_cell(c) for c in s.strip("|").split("|")]


def _is_sep(cells):
    """True for a |---|:--:|---| separator row."""
    return bool(cells) and all(c and set(c) <= set("-: ") for c in cells)


def load_glossary(path):
    """Parse dev/GLOSSARY.md's tables into (term, zh, ja, avoid, presence) rows.

    Supports several tables (one per category section): a header row is recognised as the
    row immediately followed by a |---| separator, and both are skipped. `presence` is the
    truthiness of the optional Presence column (the safety-net opt-in)."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    rows = []
    for i, line in enumerate(lines):
        cells = _cells(line)
        if cells is None or _is_sep(cells):
            continue
        nxt = _cells(lines[i + 1]) if i + 1 < len(lines) else None
        if _is_sep(nxt):
            continue  # this is a header row (its next row is the separator)
        if len(cells) >= 4:
            presence = len(cells) > 4 and cells[4].lower() in ("yes", "y", "true", "x", "✓")
            rows.append((cells[0], cells[1], cells[2], cells[3], presence))
    return rows


def build_checks(rows):
    """Expand rows into Avoid-check tuples: (forbidden, lang, term, canonical_rendering)."""
    checks = []
    for row in rows:
        term, zh, ja, avoid = row[0], row[1], row[2], row[3]
        canon = {"zh": zh, "ja": ja}
        for item in avoid.split(";"):
            item = item.strip()
            if not item:
                continue
            if ":" in item:
                tag, _, forb = item.partition(":")
                tag, forb = tag.strip(), forb.strip()
                langs = [tag] if tag in CJK_LANGS else list(CJK_LANGS)
            else:
                forb, langs = item, list(CJK_LANGS)
            for lang in langs:
                if forb:
                    checks.append((forb, lang, term, canon[lang]))
    return checks


def build_presence(rows):
    """Presence-check terms (opt-in via the Presence column): (term, zh, ja)."""
    return [(row[0], row[1], row[2]) for row in rows if len(row) > 4 and row[4]]


# ---- per-line language scope -------------------------------------------------

def scope_of(path):
    """'zh' / 'ja' for a docs/<lang>/ file, 'master' for a src .lagda.md, else 'en'."""
    parts = os.path.normpath(path).split(os.sep)
    if "docs" in parts:
        i = parts.index("docs")
        if i + 1 < len(parts) and parts[i + 1] in CJK_LANGS:
            return parts[i + 1]
        return "en"
    if path.endswith(".lagda.md"):
        return "master"
    return "en"


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

def check_file(path, checks):
    scope = scope_of(path)
    if scope == "en":
        return []  # English / developer docs carry no CJK renderings to enforce
    try:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
    except (OSError, UnicodeDecodeError):
        return []

    lines = text.split("\n")
    if scope in CJK_LANGS:
        line_lang = [scope] * len(lines)
    else:  # master
        line_lang = master_line_langs(text)

    prot = build_protected(text)
    suppress_all, suppress_term = parse_ignores(text)

    violations = []
    for forb, lang, term, canon in checks:
        for m in re.finditer(re.escape(forb), text):
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


# ---- presence safety net -----------------------------------------------------
# When an English term appears in a doc's English source but the canonical rendering is
# absent from the parallel translation, the translator likely used an off-glossary rendering
# the Avoid list does not enumerate. Opt-in per term (the Presence column), and only on
# standalone parallel docs (docs/en/X vs docs/zh|ja/X, plus the root README), never masters.

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


def discover_presence_targets():
    """(target_path, lang, en_source_path) for each translated parallel doc with an en source."""
    targets = []
    for f in git_lines(["ls-files", "*.md"]):
        parts = os.path.normpath(f).split(os.sep)
        if "docs" not in parts:
            continue
        i = parts.index("docs")
        if i + 1 >= len(parts) or parts[i + 1] not in CJK_LANGS:
            continue
        lang = parts[i + 1]
        rel = os.path.join(*parts[i + 2:]) if len(parts) > i + 2 else ""
        en = os.path.join("docs", "en", rel)
        if not os.path.exists(en):
            if os.path.basename(rel) == "README.md" and os.path.exists("README.md"):
                en = "README.md"
            else:
                continue
        targets.append((f, lang, en))
    return targets


# ---- driver ------------------------------------------------------------------

def git_lines(args):
    try:
        out = subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return [l for l in out.splitlines() if l]


def target_files(explicit, staged):
    if explicit:
        files = explicit
    elif staged:
        files = git_lines(["diff", "--cached", "--name-only", "--diff-filter=ACM"])
    else:
        files = git_lines(["ls-files", "*.md", "*.lagda.md"])
    gloss = os.path.normpath(GLOSSARY)
    return [f for f in files
            if (f.endswith(".md") or f.endswith(".lagda.md"))
            and os.path.normpath(f) != gloss
            and os.path.basename(f).lower() not in EXCLUDE_BASENAMES]


def main(argv):
    staged = False
    paths = []
    for a in argv:
        if a == "--check":
            pass
        elif a == "--staged":
            staged = True
        elif a.startswith("-"):
            sys.stderr.write(f"unknown option: {a}\n")
            return 2
        else:
            paths.append(a)

    if not os.path.exists(GLOSSARY):
        sys.stderr.write(f"glossary not found: {GLOSSARY}\n")
        return 2
    rows = load_glossary(GLOSSARY)
    checks = build_checks(rows)
    presence_terms = build_presence(rows)

    total = 0
    # Avoid check: known off-glossary renderings, on the requested file list.
    for path in target_files(paths, staged):
        violations = check_file(path, checks)
        for ln, _idx, msg in sorted(violations):
            print(f"{path}:{ln}: {msg}")
            total += 1

    # Presence check: opt-in safety net across parallel doc pairs (always the full tree, since
    # it compares a translation against its English source, which may not be in a staged subset).
    if presence_terms:
        hits = []
        for tgt, lang, en in discover_presence_targets():
            try:
                hits.extend(presence_violations(tgt, lang, _read(en), _read(tgt), presence_terms))
            except (OSError, UnicodeDecodeError):
                continue
        for path, msg in sorted(hits):
            print(f"{path}:1: {msg}")
            total += 1

    if total:
        print(f"\n{total} glossary violation(s). Fix the rendering or, if it is a genuine "
              f"exception, add <!-- glossary-ignore --> on the line. See dev/GLOSSARY.md.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
