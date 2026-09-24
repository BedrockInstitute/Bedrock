"""Strict term introduction and prerequisite rules over an explicit corpus."""
import re
from term_registry import LANGS, TERM_MARK_RE, localized_forms, reader_terms, schema_errors
from i18n_markers import weave
from prose_lint import build_protected
LANG_MARK = re.compile(r"^\s*<!--\s*(en|zh|ja|/)\s*-->\s*$")
FENCE = re.compile(r"^\s*(```|~~~)")

def markers(text):
    """Yield (line, language, kind, id, label) outside Agda fences."""
    language = None
    in_fence = False
    for line_number, line in enumerate(text.splitlines(), 1):
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


def prerequisite_occurrences(text, entry, language, module):
    """Bare uses require prior introduction; explicit references are lookups.

    A lookup may point forward within the same chapter, not just to another
    chapter. Its label and unique introduction are still validated by check().
    """
    protected = build_protected(text)
    for reference in TERM_MARK_RE.finditer(text):
        # Attributes and concept IDs are metadata, not additional uses of the label.
        protected[reference.end(1):reference.end()] = [True] * (reference.end() - reference.end(1))
        other_concept = reference.group(3) != entry['id']
        explicit_lookup = reference.group(2) == 'ref'
        if other_concept or explicit_lookup:
            protected[reference.start():reference.end()] = [True] * len(reference[0])
    return [match for match in term_pattern(entry, language).finditer(text)
            if not protected[match.start()]]


def check_terms(sources, entries, reading):
    errors = schema_errors(entries)
    terms = reader_terms(entries)
    by_id = {entry["id"]: entry for entry in terms}
    introductions = {(entry["id"], lang): [] for entry in terms for lang in LANGS}

    for module, text in sorted(sources.items()):
        path = module
        for line, language, kind, term_id, label in markers(text):
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
    graph = {node['id']: node['prerequisites'] for node in reading['nodes']}
    previews = {node['id'] for node in reading['nodes'] if node.get('preview')}
    if graph is not None:
        for module, raw in sorted(sources.items()):
            path = module
            if module not in graph or module in previews:
                continue
            ready = ancestors(graph, module)
            for language in LANGS:
                text = weave(raw, language)
                for entry in terms:
                    if entry.get("matching", "explicit") != "auto":
                        continue
                    occurrences = prerequisite_occurrences(text, entry, language, module)
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
