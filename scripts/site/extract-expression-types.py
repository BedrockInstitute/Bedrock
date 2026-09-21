#!/usr/bin/env python3
"""Normalize bedrock-agda's type trace and verify hover coverage.

The compiler produces every type while checking, either in one combined
checking/HTML traversal or in independently buffered parallel module checks.
This script never starts Agda and never modifies source: it keeps the newest
trace run for each module, joins binding occurrences with Agda's HTML links,
rejects unresolved types, and writes the compact renderer input.
"""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
import re
import sys


AGDA_FENCE_RE = re.compile(r"(?ms)^```agda[^\n]*\n(.*?)^```[ \t]*$")
BOUND_LINK_RE = re.compile(
    r'<a\s+id="(\d+)"\s+href="([^"#]+)\.html#(\d+)"\s+'
    r'class="[^"]*\bBound\b[^"]*">([^<]*)</a>'
)
NAME_LINK_RE = re.compile(
    r'<a\s+id="(\d+)"\s+href="([^"#]+)\.html#(\d+)"\s+'
    r'class="[^"]+">([^<]*)</a>'
)
UNLINKED_BOUND_RE = re.compile(
    r'<a\s+id="(\d+)"\s+class="[^"]*\bBound\b[^"]*">([^<]*)</a>'
)
IMPRECISE_RE = re.compile(r"_[\w.']+_\d+|(?<![\w'])_\d+\b|\?\d+")
KIND_PRIORITY = {"name": 1, "binding": 2, "application": 3}


def module_name(path: Path, source_root: Path) -> str:
    return path.relative_to(source_root).as_posix()[:-len(".lagda.md")].replace("/", ".")


def source_paths(source_root: Path) -> dict[Path, tuple[str, Path]]:
    return {
        path.resolve(): (module_name(path, source_root), path)
        for path in sorted(source_root.glob("**/*.lagda.md"))
    }


def source_hash(path: Path) -> str:
    value = 14695981039346656037
    for byte in path.read_bytes():
        value = ((value ^ byte) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return format(value, "x")


def read_latest_trace(trace_path: Path, known_paths: set[Path]) -> dict[Path, list[dict]]:
    """Keep the last compiler run seen for each source path."""
    latest_run: dict[Path, str] = {}
    records: dict[Path, list[dict]] = {}
    errors = []
    hashes = {path: source_hash(path) for path in known_paths}
    with trace_path.open(encoding="utf-8") as trace:
        for line_number, line in enumerate(trace, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
                path = Path(record["path"]).resolve()
                run = str(record["run"])
                if record.get("version") != 1:
                    raise ValueError(f"unsupported trace version {record.get('version')!r}")
                if record.get("kind") not in KIND_PRIORITY:
                    continue
                if not isinstance(record.get("start"), int) or not isinstance(record.get("end"), int):
                    raise ValueError("start/end must be integers")
                if not isinstance(record.get("type"), str):
                    raise ValueError("type must be a string")
                if not isinstance(record.get("sourceHash"), str):
                    raise ValueError("sourceHash must be a string")
            except (KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
                errors.append(f"{trace_path}:{line_number}: {error}")
                continue
            if path not in known_paths:
                continue
            if record["sourceHash"] != hashes[path]:
                continue
            if latest_run.get(path) != run:
                latest_run[path] = run
                records[path] = []
            records[path].append(record)
    if errors:
        raise RuntimeError("invalid bedrock-agda trace:\n" + "\n".join(errors[:20]))
    return records


def code_intervals(source: str) -> list[tuple[int, int]]:
    return [(match.start(1) + 1, match.end(1) + 1) for match in AGDA_FENCE_RE.finditer(source)]


def inside_code(start: int, end: int, intervals: list[tuple[int, int]]) -> bool:
    return any(left <= start < end <= right for left, right in intervals)


def normalize_type(value: str) -> str:
    return " ".join(value.split())


def imprecise_type(value: str) -> bool:
    return bool(IMPRECISE_RE.search(value))


def prefer_record(old: dict | None, new: dict) -> dict:
    if old is None:
        return new
    old_type = normalize_type(old["type"])
    new_type = normalize_type(new["type"])
    old_score = (not imprecise_type(old_type), KIND_PRIORITY[old["kind"]])
    new_score = (not imprecise_type(new_type), KIND_PRIORITY[new["kind"]])
    return new if new_score >= old_score else old


def include_closing_parentheses(source: str, start: int, end: int) -> int:
    """Include closing parentheses which only finish this application range.

    Agda sometimes reports a parenthesised application both immediately before
    and immediately after its closing delimiter.  The former is an elaboration
    boundary, not a second source node.  Extending only while the recorded
    fragment has unmatched opening parentheses preserves genuinely larger
    applications and lets the normal range deduplication merge both reports.
    """
    fragment = source[start - 1:end - 1]
    balance = fragment.count("(") - fragment.count(")")
    while balance > 0 and end <= len(source) and source[end - 1] == ")":
        end += 1
        balance -= 1
    return end


def highlighted_source(html_dir: Path, module: str) -> str:
    for suffix in (".md", ".html"):
        candidate = html_dir / f"{module}{suffix}"
        if candidate.exists():
            return candidate.read_text(encoding="utf-8")
    raise RuntimeError(f"missing Agda HTML output for {module}")


def bound_metadata(highlighted: str, module: str):
    bound_targets = {
        int(position): (target_module, int(target))
        for position, target_module, target, _ in BOUND_LINK_RE.findall(highlighted)
    }
    targets = {
        int(position): (target_module, int(target))
        for position, target_module, target, _ in NAME_LINK_RE.findall(highlighted)
    }
    labels = {
        int(position): html.unescape(label)
        for position, _, _, label in NAME_LINK_RE.findall(highlighted)
    }
    labels.update({
        int(position): html.unescape(label)
        for position, _, _, label in BOUND_LINK_RE.findall(highlighted)
    })
    for position, label in UNLINKED_BOUND_RE.findall(highlighted):
        position = int(position)
        targets[position] = (module, position)
        labels[position] = html.unescape(label)
    return targets, labels, set(bound_targets)


def normalize(source_root: Path, html_dir: Path, trace_path: Path,
              selected: set[str] | None = None) -> tuple[dict[str, list[dict]], list[dict]]:
    paths = source_paths(source_root)
    latest = read_latest_trace(trace_path, set(paths))
    modules = {module for module, _ in paths.values()}
    if selected:
        unknown = selected - modules
        if unknown:
            raise RuntimeError(f"unknown module(s): {', '.join(sorted(unknown))}")

    result: dict[str, list[dict]] = {}
    compact: list[dict] = []
    expected_targets: dict[tuple[str, int], tuple[str, int, str]] = {}
    binding_types: dict[tuple[str, int], str] = {}
    metadata = {}
    unresolved = []

    for resolved, (module, path) in paths.items():
        if selected and module not in selected:
            continue
        source = path.read_text(encoding="utf-8")
        intervals = code_intervals(source)
        targets, labels, bound_occurrences = bound_metadata(
            highlighted_source(html_dir, module), module
        )
        metadata[module] = (source, intervals, targets, labels)
        for occurrence in bound_occurrences:
            target = targets[occurrence]
            label = labels.get(occurrence, "")
            if label != "_" and target[0] in modules:
                expected_targets.setdefault(target, (module, occurrence, label))

        path_records = latest.get(resolved, [])
        if not path_records:
            result[module] = []
            continue
        compact.extend(path_records)
        by_range: dict[tuple[int, int], dict] = {}
        for record in path_records:
            start, end = record["start"], record["end"]
            if record["kind"] == "binding" and start in labels:
                end = start + len(labels[start])
                record = {**record, "end": end}
            elif record["kind"] == "application":
                end = include_closing_parentheses(source, start, end)
                record = {**record, "end": end}
            if not (1 <= start < end <= len(source) + 1):
                continue
            if not inside_code(start, end, intervals):
                continue
            key = (start, end)
            by_range[key] = prefer_record(by_range.get(key), record)

        nodes = []
        for (start, end), record in sorted(by_range.items()):
            type_ = normalize_type(record["type"])
            fragment = " ".join(source[start - 1:end - 1].split())
            if not fragment or not type_:
                continue
            target = ((module, start) if record["kind"] == "binding"
                      else targets.get(start))
            if imprecise_type(type_):
                if record["kind"] in {"application", "binding"}:
                    unresolved.append(f"{module}:{start}-{end} {fragment}: {type_}")
                continue
            if record["kind"] == "application":
                nodes.append({
                    "start": start, "end": end, "kind": "application",
                    "source": fragment, "type": type_,
                })
                continue
            if target is None:
                continue
            binding_types[target] = type_
            if record["kind"] == "binding":
                nodes.append({
                    "start": start, "end": end, "kind": "binding",
                    "source": fragment, "type": type_,
                    "targetModule": target[0], "target": target[1],
                })
            elif record["kind"] == "name":
                nodes.append({
                    "start": start, "end": end, "kind": "definition",
                    "source": fragment, "type": type_,
                    "targetModule": target[0], "target": target[1],
                })
        result[module] = nodes

    # Agda's HTML links every bound occurrence to its binder.  One compiler
    # type for the binder therefore supplies all variable occurrences without
    # re-pretty-printing the same type at every use site.
    for module, (source, intervals, targets, labels) in metadata.items():
        nodes = result[module]
        occupied = {(node["start"], node["end"], node["kind"]) for node in nodes}
        for occurrence, target in targets.items():
            label = labels.get(occurrence, "")
            type_ = binding_types.get(target)
            end = occurrence + len(label)
            if (not label or label == "_" or type_ is None
                    or not inside_code(occurrence, end, intervals)
                    or (target == (module, occurrence))):
                continue
            key = (occurrence, end, "variable")
            if key in occupied:
                continue
            nodes.append({
                "start": occurrence, "end": end, "kind": "variable",
                "source": label, "type": type_,
                "targetModule": target[0], "target": target[1],
            })
            occupied.add(key)

    uncovered = [
        (*target, *details) for target, details in expected_targets.items()
        if target not in binding_types
    ]
    if uncovered:
        detail = "\n  ".join(
            f"{target_module}#{target} ({module}#{occurrence} {label})"
            for target_module, target, module, occurrence, label in uncovered[:20]
        )
        raise RuntimeError(
            f"bedrock-agda trace left {len(uncovered)} binding target(s) without a type:\n  {detail}"
        )
    if unresolved:
        raise RuntimeError(
            f"bedrock-agda emitted {len(unresolved)} unresolved type(s):\n  "
            + "\n  ".join(unresolved[:20])
        )

    next_id = 1
    for module in sorted(result):
        result[module].sort(key=lambda node: (node["start"], node["end"], node["kind"]))
        for node in result[module]:
            node["id"] = next_id
            next_id += 1
    return result, compact


def write_json_atomic(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def compact_trace(path: Path, records: list[dict]) -> None:
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8") as output:
        for record in records:
            output.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n")
    temporary.replace(path)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--src", default="src")
    parser.add_argument("--html-dir", default="_build/html")
    parser.add_argument("--trace", default="_build/bedrock-agda-types.jsonl")
    parser.add_argument("--out", default="_build/expression-types.json")
    parser.add_argument("--module", action="append", default=[])
    args = parser.parse_args(argv)

    source_root = Path(args.src).resolve()
    trace = Path(args.trace).resolve()
    if not trace.exists():
        raise RuntimeError(f"missing bedrock-agda trace: {trace}")
    data, compact = normalize(
        source_root, Path(args.html_dir).resolve(), trace,
        set(args.module) or None,
    )
    write_json_atomic(Path(args.out), data)
    if not args.module:
        compact_trace(trace, compact)
    total = sum(len(nodes) for nodes in data.values())
    applications = sum(node["kind"] == "application" for nodes in data.values() for node in nodes)
    print(
        f"normalized {applications} application node(s) and {total - applications} binding/name node(s) "
        f"from one Agda trace",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
