#!/usr/bin/env python3
"""Validate reader-facing glossary introductions and explicit references."""

import os
import importlib.util
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "site"))
from term_registry import LANGS, TERM_MARK_RE, load_entries, localized_forms, reader_terms, schema_errors
from i18n_markers import weave
from reading_routes import build_reading_data

LANG_MARK = re.compile(r"^\s*<!--\s*(en|zh|ja|/)\s*-->\s*$")
FENCE = re.compile(r"^\s*(```|~~~)")

_lint_spec = importlib.util.spec_from_file_location(
    "term_lint_prose", Path(__file__).with_name("lint-prose.py"))
_lint_prose = importlib.util.module_from_spec(_lint_spec)
_lint_spec.loader.exec_module(_lint_prose)
build_protected = _lint_prose.build_protected


def module_name(path, src="src"):
    return os.path.relpath(path, src)[:-len(".lagda.md")].replace(os.sep, ".")


def markers(path):
    """Yield (line, language, kind, id, label) outside Agda fences."""
    language = None
    in_fence = False
    with open(path, encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if FENCE.match(line):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            language_mark = LANG_MARK.match(line)
            if language_mark:
                language = None if language_mark.group(1) == "/" else language_mark.group(1)
                continue
            for match in TERM_MARK_RE.finditer(line):
                label, kind, term_id = match.groups()
                yield line_number, language, kind, term_id, label


def term_pattern(entry, language):
    forms = sorted((re.escape(form) for form in localized_forms(entry, language)), key=len, reverse=True)
    joined = "|".join(forms)
    return re.compile((r"(?<![A-Za-z])(?:" + joined + r")(?![A-Za-z])") if language == "en"
                      else joined, re.I if language == "en" else 0)


def ancestors(graph, module):
    found, pending = set(), list(graph.get(module, ()))
    while pending:
        dependency = pending.pop()
        if dependency in found:
            continue
        found.add(dependency)
        pending.extend(graph.get(dependency, ()))
    return found


def check(src="src", glossary="dev/glossary.toml"):
    entries = load_entries(glossary)
    errors = schema_errors(entries)
    terms = reader_terms(entries)
    by_id = {entry["id"]: entry for entry in terms}
    introductions = {(entry["id"], lang): [] for entry in terms for lang in LANGS}

    for path in sorted(Path(src).rglob("*.lagda.md")):
        module = module_name(str(path), src)
        for line, language, kind, term_id, label in markers(path):
            if term_id not in by_id:
                errors.append(f"{path}:{line}: unknown reader term id {term_id!r}")
                continue
            if language not in LANGS:
                errors.append(f"{path}:{line}: term markers must be inside an en/zh/ja group")
                continue
            entry = by_id[term_id]
            audited = localized_forms(entry, language)
            if ((language == "en" and label.casefold() not in {form.casefold() for form in audited})
                    or (language != "en" and label not in audited)):
                errors.append(f"{path}:{line}: {label!r} is not an audited {language} form of {term_id}")
            if kind == "intro":
                introductions[(term_id, language)].append((module, str(path), line))

    for entry in terms:
        for language in LANGS:
            found = introductions[(entry["id"], language)]
            if len(found) != 1:
                errors.append(f"term {entry['id']!r}: expected one {language} introduction, found {len(found)}")
                continue
            module, path, line = found[0]
            if module != entry["introduced_in"]:
                errors.append(f"{path}:{line}: {entry['id']} must be introduced in {entry['introduced_in']}, not {module}")

    # A chapter may use an automatically linked term only after its introduction
    # chapter is ready in the actual prerequisite DAG. The reading catalog order
    # is deliberately not used as a proxy for pedagogical precedence.
    try:
        reading = build_reading_data(src)
        graph = {node["id"]: node["prerequisites"] for node in reading["nodes"]}
        previews = {node["id"] for node in reading["nodes"] if node.get("preview")}
    except (OSError, ValueError):
        graph = None  # route validation reports its own more precise failure
    if graph is not None:
        for path in sorted(Path(src).rglob("*.lagda.md")):
            module = module_name(str(path), src)
            if module not in graph or module in previews:
                continue
            raw = path.read_text(encoding="utf-8")
            ready = ancestors(graph, module)
            for language in LANGS:
                text = weave(raw, language)
                protected = build_protected(text)
                for entry in terms:
                    if entry.get("matching", "explicit") != "auto":
                        continue
                    occurrences = [match for match in term_pattern(entry, language).finditer(text)
                                   if not protected[match.start()]]
                    if not occurrences:
                        continue
                    intro_module = entry["introduced_in"]
                    if module == intro_module:
                        intro = next((match for match in TERM_MARK_RE.finditer(text)
                                      if match.group(2) == "intro" and match.group(3) == entry["id"]), None)
                        if intro and occurrences[0].start() < intro.start(1):
                            errors.append(f"{path}: {entry['id']} is used in {language} before its formal introduction")
                    elif intro_module not in ready:
                        errors.append(f"{path}: {entry['id']} is used in {language}, but {intro_module} is not a prerequisite")
    return errors


def main(argv):
    if argv:
        sys.stderr.write("usage: check-term-introductions.py\n")
        return 2
    errors = check()
    if errors:
        print("\n".join(errors))
        print(f"\n{len(errors)} term-introduction violation(s).", file=sys.stderr)
        return 1
    print(f"term introductions: clean ({len(reader_terms(load_entries()))} reader terms)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
