"""Input discovery helpers. Callers provide paths and source conventions."""
import os
import re
from pathlib import Path
from html_contract import *
from term_registry import TERM_MARK_RE


class SourceCorpus:
    """Explicit document inputs; compiler output may supplement plain masters."""
    def __init__(self, config, *, source_dir=None, highlighted_dir=None):
        self.source_dir = Path(source_dir) if source_dir else config.path(config.sources)
        self.sources = {str(path.relative_to(self.source_dir))[:-len(config.source_extension)].replace(os.sep, '.'): path
                        for path in sorted(self.source_dir.rglob('*' + config.source_extension))}
        self.documents = {module: (path, True) for module, path in self.sources.items()}
        highlighted = highlighted_dir or (config.path(config.highlighted) if config.highlighted else None)
        if highlighted:
            self.documents = {}
            for path in sorted(Path(highlighted).glob('*')):
                if path.suffix in ('.md', '.html'):
                    self.documents[path.stem] = (path, path.suffix == '.md')
            missing = set(self.sources) - self.documents.keys()
            if missing:
                raise ValueError('compiler input missing project chapters: ' + ', '.join(sorted(missing)))

    def read(self, module):
        path, literate = self.documents[module]
        return path.read_text(encoding='utf-8'), literate

    def closure(self, selected):
        visited, pending = set(), list(selected)
        while pending:
            module = pending.pop()
            if module in visited:
                continue
            visited.add(module)
            text, _ = self.read(module)
            linked = set(re.findall(r'href="([^"#]+)\.html(?:#[^"]*)?"', text))
            pending.extend((linked & self.documents.keys()) - visited)
        return visited
def source_file(html_dir, module):
    """agda --html emits <Module>.md for literate sources (prose + <pre class=Agda> code) and
    <Module>.html for library modules (bare highlighted code, no <pre>). Returns (path,
    is_literate)."""
    md = os.path.join(html_dir, module + ".md")
    if os.path.exists(md):
        return md, True
    return os.path.join(html_dir, module + ".html"), False


def referenced_type_modules(path, rendered):
    """Rendered modules whose sidecars a selected-page preview can fetch."""
    with open(path, encoding="utf-8") as source:
        html = source.read()
    referenced = set(re.findall(r'href="([^"#]+)\.html(?:#[^"]*)?"', html))
    return referenced.intersection(rendered)


def referenced_module_closure(selected, html_dir, rendered):
    """All highlighted pages reachable from a selected preview.

    Definition modals fetch the target HTML page, not only its hover sidecar.
    Follow links transitively so a fast ``--module`` preview has the same
    unbounded modal navigation as a complete site build.
    """
    closure = set(selected)
    pending = list(selected)
    while pending:
        module = pending.pop()
        path, _ = source_file(html_dir, module)
        for dependency in referenced_type_modules(path, rendered) - closure:
            closure.add(dependency)
            pending.append(dependency)
    return closure


def sort_reader_terms(terms, reading_data, src, extension=".lagda.md"):
    """Order terms by their first marked introduction in the reading order."""
    chapter_order = {node["id"]: node["order"] for node in reading_data["nodes"]}
    positions = {}
    for entry in terms:
        path = os.path.join(src, entry["introduced_in"].replace(".", os.sep) + extension)
        try:
            text = Path(path).read_text(encoding='utf-8')
        except OSError:
            text = ""
        match = next((m for m in TERM_MARK_RE.finditer(text)
                      if m.group(2) == "intro" and m.group(3) == entry["id"]), None)
        positions[entry["id"]] = (chapter_order.get(entry["introduced_in"], 10**9),
                                   match.start() if match else 10**9)
    return sorted(terms, key=lambda entry: positions[entry["id"]])
