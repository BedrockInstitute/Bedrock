"""Build multilingual route data for the teaching site.

The machine-readable catalog in ``dev/reading-catalog.json`` stores the
authoritative reading order, translated chapter labels, stages and routes.
Routes may overlap and do not claim independence. Direct prerequisites come
only from Agda fenced imports. ``Milestones`` is a preview and therefore has
no readiness prerequisites.

This module is also where a chapter's address is decided, once. Every node carries
``page`` and ``anchor``, and every consumer links through them rather than assembling
a filename of its own: the renderer, the reading-route explorer, the dependency map,
the search index, the glossary and the sitemap. A preview chapter has no page to
itself, because the reading guide embeds its whole body, so it is addressed as a panel
of the guide. Nothing else in the tree may hard-code that.
"""

from collections import Counter
import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from i18n_markers import LANGS, weave

FENCE = re.compile(r"^```agda\s*\n(.*?)^```\s*$", re.M | re.S)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)", re.M)
MARKER = re.compile(r"<!--\s*bedrock-routes\s*(\{.*?\})\s*-->", re.S)
HEADING = re.compile(r"^##\s+(.+?)\s*$", re.M)
PREVIEWS = frozenset({"Milestones"})
GUIDE_PAGE = "index.html"     # the reading guide, which embeds every preview chapter
GUIDE_PANEL = "milestones"    # the guide panel that shows them, and its element id


def own_page(module):
    """The page a module would be given if it had one of its own."""
    return f"{module}.html"


def twin_of(page):
    """The plain-Markdown twin of a page."""
    return page[:-len(".html")] + ".md"
CATALOG_PATH = Path(__file__).resolve().parents[2] / "dev" / "reading-catalog.json"
ROUTE_ID = re.compile(r"^[a-z][a-z0-9-]*$")


def strip_metadata(text):
    """Blank route metadata while preserving offsets and line numbers."""
    return MARKER.sub(lambda match: re.sub(r"[^\n]", " ", match.group(0)), text)


def imports(text):
    return [name for fence in FENCE.findall(text) for name in IMPORT.findall(fence)]


def _sources(src):
    root = Path(src)
    return {str(p.relative_to(root))[:-len(".lagda.md")].replace("/", "."): p.read_text()
            for p in sorted(root.rglob("*.lagda.md"))}


def _metadata(text):
    found = MARKER.findall(text)
    if len(found) != 1:
        raise ValueError(f"expected one bedrock-routes marker, found {len(found)}")
    try:
        return json.loads(found[0])
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid bedrock-routes JSON: {error}") from error


def plain_title(text):
    """Navigation labels are plain text, even when a heading uses inline code."""
    text = re.sub(r"`([^`]+)`(?:\{\.Agda\})?", r"\1", text)
    text = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
    return text.strip()


def _catalog(text):
    catalog = {}
    for lang in LANGS:
        stage, seen = None, set()
        prose = FENCE.sub("", weave(strip_metadata(text), lang))
        for line in prose.splitlines():
            heading = HEADING.fullmatch(line)
            if heading:
                stage = heading.group(1)
            entry = re.match(r"^- `([^`]+)`\{\.Agda\}[:：]\s*(.+?)\s*$", line)
            if not entry:
                continue
            module, description = entry.groups()
            if stage is None or module in seen:
                raise ValueError(f"missing stage or duplicate catalog description: {module}")
            seen.add(module)
            node = catalog.setdefault(module, {"title": {}, "stage": {}})
            node["title"][lang] = description
            node["stage"][lang] = stage
    if any(set(node["title"]) != set(LANGS) for node in catalog.values()):
        raise ValueError("catalog entries require matching language headings and entries")
    return catalog


def _load_catalog(path=CATALOG_PATH):
    with open(path, encoding="utf-8") as source:
        data = json.load(source)
    if not isinstance(data, dict) or data.get("version") != 1:
        raise ValueError("reading catalog must be a version 1 object")
    chapters = data.get("chapters")
    if not isinstance(chapters, list) or not chapters:
        raise ValueError("reading catalog chapters must be a non-empty list")
    catalog = {}
    for entry in chapters:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str):
            raise ValueError("reading catalog chapters require string ids")
        module = entry["id"]
        if module in catalog:
            raise ValueError(f"duplicate catalog chapter: {module}")
        for field in ("title", "stage", "description"):
            value = entry.get(field)
            if not isinstance(value, dict) or any(not isinstance(value.get(lang), str)
                                                  or not value[lang].strip() for lang in LANGS):
                raise ValueError(f"catalog chapter {module} requires translated {field}")
        catalog[module] = {field: dict(entry[field]) for field in ("title", "stage", "description")}
    return data, catalog


def _cycle(graph):
    active, done = set(), set()
    def visit(node, path):
        if node in active:
            return path[path.index(node):] + [node]
        if node in done:
            return None
        active.add(node); path.append(node)
        for dependency in graph.get(node, ()):
            found = visit(dependency, path)
            if found:
                return found
        path.pop(); active.remove(node); done.add(node)
        return None
    for node in graph:
        found = visit(node, [])
        if found:
            return found
    return None


def validate_metadata(metadata, chapter_ids, graph=None):
    """Raise ``ValueError`` for invalid schema, coverage, or dependency data."""
    errors, chapters = [], set(chapter_ids)
    if not isinstance(metadata, dict):
        raise ValueError("metadata must be an object")
    if metadata.get("version") != 1:
        errors.append("version must be 1")
    route_list = metadata.get("routes")
    if not isinstance(route_list, list) or not route_list:
        errors.append("routes must be a non-empty list"); route_list = []
    route_ids = [route.get("id") for route in route_list
                 if isinstance(route, dict) and isinstance(route.get("id"), str)]
    for route_id, count in Counter(route_ids).items():
        if count > 1:
            errors.append(f"duplicate route id: {route_id}")
    covered = set()
    for route in route_list:
        if not isinstance(route, dict):
            errors.append("every route must be an object"); continue
        route_id = route.get("id", "<missing>")
        if not isinstance(route_id, str) or not route_id:
            errors.append("every route requires a non-empty string id")
        elif not ROUTE_ID.fullmatch(route_id):
            errors.append(f"route id must be a stable lowercase slug: {route_id}")
        for field in ("title", "description"):
            value = route.get(field)
            if not isinstance(value, dict) or any(not isinstance(value.get(lang), str)
                                                  or not value[lang].strip()
                                                  for lang in LANGS):
                errors.append(f"route {route_id} requires non-empty {field}.en and {field}.zh and {field}.ja")
        members = route.get("chapters")
        if not isinstance(members, list):
            errors.append(f"route {route_id} chapters must be a list"); continue
        if not members:
            errors.append(f"route {route_id} chapters must not be empty")
            continue
        if any(not isinstance(name, str) or not name for name in members):
            errors.append(f"route {route_id} chapters must contain non-empty strings")
            continue
        errors.extend(f"route {route_id} repeats chapter: {name}"
                      for name, count in Counter(members).items() if count > 1)
        errors.extend(f"route {route_id} has unknown chapter: {name}"
                      for name in sorted(set(members) - chapters))
        covered.update(set(members) & chapters)
    errors.extend(f"chapter is not covered by a route: {name}"
                  for name in sorted(chapters - PREVIEWS - covered))
    if graph is not None:
        errors.extend(f"unknown graph node: {node}" for node in graph if node not in chapters)
        errors.extend(f"unknown prerequisite: {node} -> {dependency}"
                      for node, dependencies in graph.items() for dependency in dependencies
                      if dependency not in chapters)
        found = _cycle(graph)
        if found:
            errors.append("prerequisite cycle: " + " -> ".join(found))
    if errors:
        raise ValueError("\n".join(errors))


def build_reading_data(src="src", catalog_path=CATALOG_PATH):
    """Return ``version``, route metadata, and dependency-backed catalog nodes."""
    sources = _sources(src)
    metadata, catalog = _load_catalog(catalog_path)
    chapters = set(sources)
    order = [entry["id"] for entry in metadata["chapters"]]
    if len(order) != len(set(order)) or set(order) != chapters:
        raise ValueError("reading catalog must cover every chapter exactly once")
    graph = {module: list(dict.fromkeys(d for d in imports(sources[module]) if d in chapters))
             for module in chapters}
    validate_metadata(metadata, chapters, graph)
    memberships = {module: [] for module in chapters}
    for route in metadata["routes"]:
        for module in route["chapters"]:
            memberships[module].append(route["id"])
    nodes = []
    for position, module in enumerate(order, 1):
        preview = module in PREVIEWS
        titles = dict(catalog[module]["title"])
        for lang in LANGS:
            heading = re.search(r"^# (.+)$", weave(sources[module], lang), re.M)
            if heading:
                titles[lang] = plain_title(heading.group(1))
        nodes.append({"id": module, "title": titles, "description": catalog[module]["description"], "order": position,
                      "stage": catalog[module]["stage"],
                      "prerequisites": [] if preview else graph[module],
                      "routes": memberships[module], "preview": preview,
                      "page": GUIDE_PAGE if preview else own_page(module),
                      "anchor": f"#{GUIDE_PANEL}" if preview else ""})
    return {"version": 1, "routes": metadata["routes"], "nodes": nodes}


def main(argv=None):
    parser = argparse.ArgumentParser(description="Build or validate Bedrock reading routes")
    parser.add_argument("--src", default="src")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        data = build_reading_data(args.src)
    except ValueError as error:
        print("reading-routes: ERROR: " + str(error).replace("\n", "; "))
        return 1
    if args.check:
        print(f"reading-routes: clean ({len(data['routes'])} routes; {len(data['nodes'])} chapters)")
    else:
        print(json.dumps(data, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
