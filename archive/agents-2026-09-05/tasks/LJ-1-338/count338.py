"""[LJ-1.338] The measuring instrument.

It does two jobs.

1. It counts non-blank lines on the ledger caliber, for any file span.
2. It aligns the probe's copied block against the chapter's span with
   `difflib.SequenceMatcher`, the method `[LJ-1.308]` used and
   `[LJ-1.336]` re-used, and it prints the delete and replace hunks.  A
   run search can report zero because it cannot see a change; an
   alignment cannot.

Run it from the repository root.
"""

import difflib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CHAPTER = ROOT / "src" / "L" / "Condensation.lagda.md"
TASK = ROOT / "agents" / "tasks" / "LJ-1-338"


def lines(path, first=None, last=None):
    text = path.read_text(encoding="utf-8").splitlines()
    if first is None:
        return text
    return text[first - 1:last]


def non_blank(rows):
    return [r for r in rows if r.strip()]


def code_only(rows):
    return [r for r in rows if r.strip() and not r.strip().startswith("--")]


def marker_span(path, marker):
    rows = lines(path)
    for i, r in enumerate(rows):
        if marker in r:
            return rows[i + 1:]
    raise SystemExit("marker not found in %s" % path)


def align(expected, got, name):
    matcher = difflib.SequenceMatcher(None, expected, got, autojunk=False)
    deletes = 0
    replaces = 0
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "delete":
            deletes += i2 - i1
            print("  DELETE %d expected lines at %d: %r" % (i2 - i1, i1, expected[i1:i2][:2]))
        elif tag == "replace":
            replaces += 1
            print("  REPLACE %d -> %d at %d: %r -> %r"
                  % (i2 - i1, j2 - j1, i1, expected[i1:i2][:2], got[j1:j2][:2]))
    print("%s: %d expected non-blank lines, %d delete, %d replace"
          % (name, len(expected), deletes, replaces))
    return deletes, replaces


def report(label, path, first=None, last=None, after_marker=None):
    if after_marker is not None:
        rows = marker_span(path, after_marker)
    else:
        rows = lines(path, first, last)
    print("%-46s non-blank %3d   code-only %3d"
          % (label, len(non_blank(rows)), len(code_only(rows))))
    return non_blank(rows)


def main():
    print("== SPANS ==")
    chapter_kvalue = report("chapter KValue :7264-7318", CHAPTER, 7264, 7318)
    report("chapter KValue opens :7259-7262", CHAPTER, 7259, 7262)
    report("chapter LeafAgree :7107-7243", CHAPTER, 7107, 7243)
    report("chapter LeafAgree telescope :7107-7190", CHAPTER, 7107, 7190)

    probe = TASK / "ProbeKValue338.agda"
    if probe.exists():
        print()
        print("== ProbeKValue338 ==")
        copied = report("  copied block, after the MARKER", probe,
                        after_marker="-- MARKER.")
        report("  whole file", probe)
        print()
        align(chapter_kvalue, copied, "  KValue copy")

    for name in ("ProbeLeaf338.agda", "ControlA338.agda", "ControlB338.agda"):
        f = TASK / name
        if f.exists():
            print()
            report("== %s, whole file" % name, f)


if __name__ == "__main__":
    sys.exit(main())
