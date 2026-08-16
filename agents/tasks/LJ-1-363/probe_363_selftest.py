#!/usr/bin/env python3
"""PROBE (LJ-1.363). The failure paths the live corpus never exercises.

The corpus run is green, so nothing in the tree drives the gate's red paths.
This probe writes synthetic brief-and-report pairs under /tmp (outside the
tree, so no gate ever reads them) and asserts each defect kind fires, and
that each tolerance class passes:

  PASS cases (compliance):
    P1  a quoted line that occurs at the cited line
    P2  a decline spelled relative to a root (the LJ-1-168 shape)
    P3  a deeper path answering a directory citation (the LJ-1-166 shape)
    P4  a table-row quote across cells with pipes kept (the LJ-1.107 shape)
    P5  a quote with ellipsis fragments

  FAIL cases (defects):
    F1  an unanswered brief-cited archive path
    F2  no ARCHIVE USED heading at all
    F3  a brief citing dev/literature/ and a return with no LITERATURE USED
    F4  a file named as read with no quote (the LJ-1-359 shape)
    F5  a quote that occurs only three lines off (the LJ-1.356 mis-cite)
    F6  a quote the file does not hold anywhere (the fabricated-quote shape)

Run: .venv/bin/python agents/tasks/LJ-1-363/probe_363_selftest.py
"""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next(p for p in _HERE.parents if (p / "AGENTS.md").is_file())
spec = importlib.util.spec_from_file_location(
    "check_dd18_survey", _ROOT / "scripts" / "gate" / "check-dd18-survey.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

FAILED = 0

BRIEF = """# brief
tier: test
## ARCHIVE (DD18)
- `{arch}` cited for the test.
- `dev/literature/digest.md` cited for the test.
## LITERATURE (DD18)
- `dev/literature/digest.md`.
"""

BODY = {
    "arch": "archive/dev/TASKS-archived.md",
    "tasks_line": "| L3.32-T81 | CSB literature survey | COMPLETE (keep ours) |",
    "digest_line": "The condensation hierarchy is stratified by the J hierarchy.",
}


def run_case(name: str, report_text: str, want_defects: list[str],
             brief_text: str | None = None) -> None:
    global FAILED
    with tempfile.TemporaryDirectory() as td:
        brief = Path(td) / "b.md"
        report = Path(td) / "r-report.md"
        brief.write_text(brief_text or BRIEF.format(**BODY), encoding="utf-8")
        report.write_text(report_text, encoding="utf-8")
        defects, _ = mod.b2_findings(brief, report, True)
    kinds = {d.split(":")[0] for d in defects}
    missing = [k for k in want_defects if k not in kinds]
    extra = [k for k in kinds if k not in want_defects]
    ok = not missing and not extra
    print(f"  {'PASS' if ok else 'FAIL'} {name}: kinds={sorted(kinds)}")
    if not ok:
        FAILED += 1
        if missing:
            print(f"       missing: {missing}")
        if extra:
            print(f"       extra: {extra}")


def main() -> int:
    # The two archive files the cases cite must be patchable; point the
    # checker's resolve at a scratch copy so the probe owns the content.
    tmp = Path(tempfile.mkdtemp())
    (tmp / "tasks.md").write_text("index header\n" + BODY["tasks_line"] + "\n", encoding="utf-8")
    (tmp / "digest.md").write_text(BODY["digest_line"] + "\n", encoding="utf-8")
    orig_resolve, orig_root = mod.resolve, mod.ROOT
    mod.resolve = (lambda rel: tmp / "tasks.md" if "TASKS" in rel
                   else tmp / "digest.md" if "digest" in rel else orig_resolve(rel))
    mod.ROOT = tmp  # audit_quotes keys files relative to the module's ROOT

    arch, line = BODY["arch"], BODY["tasks_line"]
    print("PASS cases:")
    run_case("P1 quote at the cited line", f"""# r
## ARCHIVE USED
- `{arch}:2`. Line read: "{line}"
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", [])
    run_case("P2 decline by relative spelling", f"""# r
## ARCHIVE USED
- TASKS-archived.md: NOT read, the index row this task needed does not exist.
## LITERATURE USED
- dev/literature/digest.md: not read, nothing in it bears on a checker.
""", [])
    dir_brief = ("# brief\ntier: test\n## ARCHIVE (DD18)\n"
                 "- `archive/src/2026-08-09-rud-route/` cited for the test.\n"
                 "## LITERATURE (DD18)\n- `dev/literature/digest.md`.\n")
    run_case("P3 deeper path answers a directory", f"""# r
## ARCHIVE USED
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89`. Line read:
  "module CSB (a b : S) (f : a to b)" and the deeper file answers the brief's
  directory citation.
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", [], dir_brief)
    run_case("P4 table-row quote with pipes", f"""# r
## ARCHIVE USED
- `{arch}:2`. Line read: "{line}"
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified by the J hierarchy."
""", [])
    run_case("P5 ellipsis quote", f"""# r
## ARCHIVE USED
- `{arch}:2`. Line read: "L3.32-T81 ... COMPLETE (keep ours)"
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy ... J hierarchy."
""", [])

    print("FAIL cases:")
    run_case("F1 unanswered citation", """# r
## ARCHIVE USED
- nothing under the four corpora was read.
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", ["unanswered"])
    run_case("F2 no ARCHIVE USED heading", """# r
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", ["no-heading", "unanswered"])
    run_case("F3 no LITERATURE USED heading", f"""# r
## ARCHIVE USED
- `{arch}:2`. Line read: "{line}"
""", ["no-lit-heading"])
    run_case("F4 read with no quote", f"""# r
## ARCHIVE USED
- `{arch}:2`. The T81 row, read and taken.
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", ["no-quote"])
    run_case("F5 quote three lines off", f"""# r
## ARCHIVE USED
- `{arch}:5`. Line read: "{line}"
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", ["quote"])
    run_case("F6 quote not in the file", f"""# r
## ARCHIVE USED
- `{arch}:2`. Line read: "a row the index has never held"
## LITERATURE USED
- `dev/literature/digest.md:1`: "The condensation hierarchy is stratified"
""", ["quote"])

    mod.resolve, mod.ROOT = orig_resolve, orig_root
    print(f"\n{'ALL CASES PASS' if not FAILED else str(FAILED) + ' CASE(S) FAILED'}")
    return 1 if FAILED else 0


if __name__ == "__main__":
    sys.exit(main())
