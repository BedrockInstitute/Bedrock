#!/usr/bin/env python3
"""Reader-facing terminology metadata shared by the site and glossary gates."""

import re
import tomllib

LANGS = ("en", "zh", "ja")
TERM_MARK_RE = re.compile(
    r"\[([^\]\n]+)\]\{\.term-(intro|ref)\s+#([a-z][a-z0-9-]*)\}"
)
TERM_ID_RE = re.compile(r"[a-z][a-z0-9-]*")


def load_entries(path="dev/glossary.toml"):
    with open(path, "rb") as source:
        return tomllib.load(source).get("term", [])


def reader_terms(entries):
    return [entry for entry in entries if entry.get("audience") == "reader"]


def schema_errors(entries):
    """Validate only the optional reader-facing extension of glossary entries."""
    errors = []
    ids = {}
    for index, entry in enumerate(entries, 1):
        term_id = entry.get("id")
        audience = entry.get("audience")
        if audience is not None and audience not in ("reader", "editorial"):
            errors.append(f"term {entry.get('en', index)!r}: audience must be reader or editorial")
        if term_id is not None and not TERM_ID_RE.fullmatch(str(term_id)):
            errors.append(f"term {index}: invalid stable id {term_id!r}")
        if term_id:
            ids.setdefault(term_id, []).append(entry.get("en", f"term {index}"))
        if audience != "reader":
            continue
        for field in ("id", "en", "zh", "ja", "introduced_in", "matching",
                      "recap_en", "recap_zh", "recap_ja"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                errors.append(f"term {entry.get('en', index)!r}: reader term requires {field}")
        matching = entry.get("matching")
        if matching not in ("auto", "explicit"):
            errors.append(f"term {entry.get('en', index)!r}: matching must be auto or explicit")
        for lang in LANGS:
            forms = entry.get(f"forms_{lang}", [])
            if not isinstance(forms, list) or any(not isinstance(form, str) or not form for form in forms):
                errors.append(f"term {entry.get('en', index)!r}: forms_{lang} must be a string list")
    for term_id, labels in ids.items():
        if len(labels) > 1:
            errors.append(f"duplicate stable term id {term_id!r}: {', '.join(labels)}")
    for lang in LANGS:
        automatic = {}
        for entry in reader_terms(entries):
            if entry.get("matching", "explicit") != "auto":
                continue
            for form in localized_forms(entry, lang):
                key = form.casefold() if lang == "en" else form
                if key in automatic and automatic[key] != entry["id"]:
                    errors.append(f"ambiguous automatic {lang} form {form!r}: "
                                  f"{automatic[key]} and {entry['id']}")
                automatic[key] = entry["id"]
    return errors


def localized_forms(entry, lang):
    """Canonical rendering followed by explicitly audited grammatical forms."""
    return list(dict.fromkeys([entry[lang], *entry.get(f"forms_{lang}", [])]))
