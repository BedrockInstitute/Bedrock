#!/usr/bin/env python3
"""PROBE, unwired (LJ-1.358). The citation TRUTH check, and the depth ritual.

THE QUESTION THIS PROBE ANSWERS. DD18's return clause says a report names
"what it actually read and what it took from each item, at `file:line`".
`[LJ-1.357]` measured that R3 verifies PRESENCE, never TRUTH: three mis-cited
lines passed it (its section 7.4). This probe measures whether the letter of
the return clause is mechanically checkable at all:

  for every `path:line` citation in a report's ARCHIVE USED / LITERATURE USED
  section, does the path exist, is the line inside the file, and does the
  quoted text on that citation line actually occur at (or near) that line?

WHAT IT CANNOT DO, stated up front: a citation that quotes nothing cannot be
truth-checked (unquoted citations are counted, not verified); a TRUE line
quoted without understanding passes (the "read the header" ritual quotes true
header lines); paraphrase fails the match and is counted NEAR MISS before BAD.

Also measured: the DEPTH RITUAL. For every TASKS-archived.md citation in
ARCHIVE USED sections, the highest line number cited. The 265-row index read
only at its first lines is the ritual `[LJ-1.356]` section 8 measured; this
gives the distribution rather than ten samples.

Usage:
  probe_358_truthcheck.py                # whole live corpus, summary
  probe_358_truthcheck.py --task LJ-1-356  # one task, every defect printed
"""

from __future__ import annotations

import re
import sys
import time
from collections import Counter
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
if _ROOT is None:
    raise FileNotFoundError(f"no repo root above {_HERE}")
sys.path.insert(0, str(_ROOT / "scripts"))
import agents_tree  # noqa: E402

ROOT = _ROOT

SECTION = {
    "ARCHIVE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "LITERATURE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
}

#: A citation: a repository-ish path followed by :line or :line-line.
CITE = re.compile(
    r"`?((?:archive|agents/tasks|dev|scripts|src)/[A-Za-z0-9./_+-]+?)`?"
    r"(?::(\d+)(?:-(\d+))?(?:,\d+)*)+")

#: A quoted span worth checking: 12+ chars inside double quotes (straight or
#: curly). Short spans match everywhere and verify nothing.
QUOTE = re.compile(r'["\u201c]([^"\u201d]{12,})["\u201d]')

WINDOW = 3  # lines of slack before a mismatch is called BAD rather than NEAR


def normalize(s: str) -> str:
    s = re.sub(r"[*`_]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def resolve(rel: str) -> Path | None:
    p = ROOT / rel
    if p.is_file():
        return p
    # A path spelled relative to the archive root ([LJ-1.357] 5.3 point 5:
    # "L/LevelFormula.lagda.md" for archive/src/2026-08-09-rud-route/L/...).
    cand = ROOT / "archive" / "src" / "2026-08-09-rud-route" / rel
    if cand.is_file():
        return cand
    return None


def cited_lines(text: str) -> list[int]:
    """All line numbers a report attaches to ONE path occurrence, merged."""
    out: list[int] = []
    for m in CITE.finditer(text):
        start = int(m.group(2))
        end = int(m.group(3) or m.group(2))
        out += list(range(start, end + 1))
    return out


def check_report(path: Path, verbose: bool) -> dict:
    text = path.read_text(encoding="utf-8")
    stats = Counter()
    defects: list[str] = []
    for name, rx in SECTION.items():
        sec = rx.search(text)
        if sec is None:
            stats[f"{name}: absent"] += 1
            continue
        bullets = re.findall(r"(?:^|\n)\s*-\s+(.*?)(?=\n\s*-\s|\Z)",
                              sec.group(1), re.S)
        for raw in bullets:
            raw = re.sub(r"\s+", " ", raw)
            # Each quote belongs to the NEAREST citation before it in the
            # bullet, never to every citation in the bullet.
            events = ([(m.start(), "cite", m) for m in CITE.finditer(raw)]
                      + [(m.start(), "quote", m) for m in QUOTE.finditer(raw)])
            events.sort(key=lambda e: e[0])
            pairs: list[tuple[re.Match, str]] = []
            current: re.Match | None = None
            for _, kind, m in events:
                if kind == "cite":
                    current = m
                elif current is not None:
                    pairs.append((current, normalize(m.group(1))))
            stats["bullets"] += 1
            for m, q in pairs:
                rel, start_s, end_s = m.group(1), m.group(2), m.group(3)
                start, end = int(start_s), int(end_s or start_s)
                stats["citations"] += 1
                # Frozen corpora never change, so a bad quote there was bad
                # the day it was written. Live files drift, and a stale true
                # citation is counted separately, never as a defect.
                bucket = "frozen" if rel.startswith("archive/") else "live"
                fp = resolve(rel)
                if fp is None:
                    stats["unresolved path"] += 1
                    if verbose:
                        defects.append(f"{name}: {rel}: path not found")
                    continue
                body_lines = fp.read_text(encoding="utf-8").splitlines()
                if start > len(body_lines):
                    stats["line beyond EOF"] += 1
                    if verbose:
                        defects.append(f"{name}: {rel}:{start}: beyond EOF "
                                       f"({len(body_lines)} lines)")
                    continue
                # Quotes in reports span physical lines and elide with ...,
                # so the target is the JOINED text of the range, and an
                # elided quote verifies when every fragment is present.
                def joined(a: int, b: int) -> str:
                    return normalize(" ".join(body_lines[a - 1:b]))
                # Reports also cite lines inline ("at `:7`"); those belong
                # to the same path when they sit in the same bullet.
                extra = [int(n) for n in
                         re.findall(r"`?:(\d{1,4})\b`?", raw)
                         if int(n) <= len(body_lines)]
                exact_ranges = [(start, end)] + [(n, n) for n in extra]
                exact = " \u00a7 ".join(joined(a, b) for a, b in exact_ranges)
                near = " \u00a7 ".join(joined(max(1, a - WINDOW), b + WINDOW)
                                      for a, b in exact_ranges)
                # A quoted single token is a TERM MENTION (the report saying
                # what a thing is called), not a citation of file content.
                # Only phrases are checked; mentions are counted and skipped.
                if not (len(q) >= 12 and " " in q):
                    stats["term mentions (skipped)"] += 1
                    continue
                for q in [q]:
                    frags = [f for f in re.split(r"\.\.\.|\u2026", q) if len(f) >= 6]
                    def hits(text: str) -> bool:
                        return bool(frags) and all(
                            f.casefold() in text.casefold() for f in frags)
                    if hits(exact):
                        stats[f"{bucket}: quote verified"] += 1
                    elif hits(near):
                        stats[f"{bucket}: NEAR MISS (line off)"] += 1
                        if verbose:
                            defects.append(f"{name}: {rel}:{start}-{end}: "
                                           f"quote found only in window")
                    elif any(hits(joined(i, min(i + 40, len(body_lines))))
                             for i in range(1, len(body_lines), 20)):
                        stats[f"{bucket}: WRONG LINE (quote elsewhere)"] += 1
                        if verbose:
                            defects.append(f"{name}: {rel}:{start}-{end}: quote "
                                           f"is elsewhere in the file")
                    else:
                        stats[f"{bucket}: BAD QUOTE (not in file)"] += 1
                        if verbose:
                            defects.append(f"{name}: {rel}:{start}-{end}: quoted "
                                           f"text not in file: {q[:70]!r}")
                # The depth ritual, on the one index worth measuring.
                if rel.endswith("TASKS-archived.md"):
                    stats[f"tasks-index max line {end}"] += 1
    return {"stats": stats, "defects": defects}


def main(argv: list[str]) -> int:
    verbose = "--task" in argv
    task = argv[argv.index("--task") + 1] if verbose else None
    t0 = time.time()
    reports = [p for p in agents_tree.reports(include_archive=False)]
    if task:
        reports = [p for p in reports if p.parent.name.lower() == task.lower()]
    total = Counter()
    per_task: list[tuple[str, Counter, list[str]]] = []
    for p in sorted(reports):
        r = check_report(p, verbose)
        total.update(r["stats"])
        per_task.append((p.parent.name, r["stats"], r["defects"]))

    print(f"corpus: {len(reports)} live reports, checked in {time.time() - t0:.1f}s")
    for k in sorted(total):
        print(f"  {k:34s} {total[k]}")

    # Depth ritual, summarized: how deep into the 265-row index do reports read?
    depth = {int(k.rsplit(" ", 1)[1]): v for k, v in total.items()
             if k.startswith("tasks-index max line")}
    if depth:
        cites = sum(depth.values())
        shallow = sum(v for k, v in depth.items() if k <= 20)
        deep = sum(v for k, v in depth.items() if k > 20)
        print(f"\nTASKS-archived.md citations: {cites}, all lines <= 20: "
              f"{shallow} ({100 * shallow // max(1, cites)} percent), "
              f"any line > 20: {deep}")

    # Coverage: how many path citations exist at all, and how many carry a
    # checkable phrase. The truth check only ever sees the quoted fraction.
    print(f"\ncoverage: {total['bullets']} bullets, {total['citations']} "
          f"quote-bearing citations, {total['term mentions (skipped)']} term mentions")

    if verbose or "--frozen" in argv:
        print()
        for name, _, defects in per_task:
            for d in defects:
                print(f"  {name}: {d}")
    else:
        flagged = [(n, s) for n, s, _ in per_task
                   if s["BAD QUOTE (not in file)"] or s["WRONG LINE (quote elsewhere)"]
                   or s["line beyond EOF"]]
        print(f"\nreports with a hard citation defect: {len(flagged)} of {len(reports)}")
        for n, s in flagged:
            print(f"  {n}: {dict(s)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
