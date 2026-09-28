#!/usr/bin/env python3
"""Glossary checker for Bedrock: flags off-glossary renderings in multilingual prose.

The canonical glossary data is site/glossary.toml (read here via tomllib); the prose that
explains the checks and how to maintain entries is site/GLOSSARY.md. Each entry gives a term's
canonical English, Chinese and Japanese renderings plus an optional `avoid` list of known wrong
renderings. This script scans the trilingual docs and reports any avoided rendering, pointing
at the canonical one.

Language scoping: a `zh:`-tagged avoid term is only flagged in Chinese context, a `ja:`-tagged
one only in Japanese context, and an untagged term in both. Chinese context is `docs/zh/**`
and the `<!--zh-->` prose of `src/**.lagda.md` masters; Japanese context is `docs/ja/**` and
`<!--ja-->` prose. An `en:`-tagged alias is checked in English prose. Shared/neutral prose is not checked.

Report-only (like the em-dash rule): there is no --fix, because the correct rendering is a
translation judgement, not a mechanical substitution. Code spans, fenced blocks, link
destinations and URLs are protected (shared with lint-prose.py). Put `<!-- glossary-ignore -->`
on a line to suppress it, or `<!-- glossary-ignore: charter -->` to suppress one term.

Usage:
  check-glossary.py [--check] [--staged] [FILE ...]
  default mode is --check; with no FILE and no --staged, scans tracked and unignored new *.md/*.lagda.md.
  The archive (archive/) is never scanned: it is outside every gate
  (archived D20; the live home of that rule is DD13).
Exit status: 0 clean, 1 violations, 2 usage error.
"""

import os
import subprocess
import sys
from pathlib import Path


if sys.version_info < (3, 11):
    sys.exit("check-glossary.py needs Python 3.11+ (tomllib); run `make venv` and use .venv/bin/python")

HERE = os.path.dirname(os.path.abspath(__file__))
GLOSSARY = "site/glossary.toml"      # canonical term data (this checker's input)
GLOSSARY_DOC = "site/GLOSSARY.md"    # human prose explaining the glossary (excluded from scans)


from outcrop.core.glossary_lint import (
    CJK_LANGS, _read, build_checks, build_presence, check_text,
    load_glossary, master_presence_violations, presence_violations, route_metadata_violations,
)
from outcrop.core.prose_lint import EXCLUDE_BASENAMES
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


def check_file(path, checks):
    try:
        text = Path(path).read_text(encoding='utf-8')
    except (OSError, UnicodeDecodeError):
        return []
    return check_text(text, checks, scope_of(path))

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
        files = sorted(set(git_lines(["ls-files", "--cached", "--others", "--exclude-standard", "*.md", "*.lagda.md"])))
    excluded = {os.path.normpath(GLOSSARY), os.path.normpath(GLOSSARY_DOC)}
    return [f for f in files
            if (f.endswith(".md") or f.endswith(".lagda.md"))
            and os.path.normpath(f) not in excluded
            and os.path.basename(f).lower() not in EXCLUDE_BASENAMES
            and not f.startswith("archive/")]   # outside every gate (archived D20, live DD13)


def main(argv):
    staged = False
    extras_only = False
    paths = []
    for a in argv:
        if a == "--check":
            pass
        elif a == "--staged":
            staged = True
        elif a == "--extras-only":
            extras_only = True
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
        if not os.path.isfile(path):
            continue
        master = Path(path).resolve().is_relative_to(Path('src').resolve()) and path.endswith('.lagda.md')
        violations = [] if extras_only and master else check_file(path, checks)
        for ln, _idx, msg in sorted(violations):
            print(f"{path}:{ln}: {msg}")
            total += 1
        if path.endswith(".lagda.md"):
            for _, message in ([] if extras_only and master else master_presence_violations(path, _read(path), presence_terms)):
                print(f"{path}: {message}")
                total += 1
            for message in route_metadata_violations(_read(path), checks):
                print(f"{path}: {message}")
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
              f"exception, add <!-- glossary-ignore --> on the line. See site/GLOSSARY.md.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
