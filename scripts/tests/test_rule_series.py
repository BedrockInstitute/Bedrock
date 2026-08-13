#!/usr/bin/env python3
"""Regression tests for the series check in `scripts/check-rule-ids.py`.

WHY THIS FILE EXISTS. On 2026-08-13 `[LJ-1.139]` found ten bad pointers in nine
memo headers, and EIGHT of them RESOLVED. `check-rule-ids.py` was green through
all of them, because it asks whether a code resolves and never which series the
author meant. Two earlier audits had seen the pair and filed it as cosmetic.
`[LJ-1.140]` then measured 84 more sites in 15 live files, one of them two lines
of `dev/STYLE-agda.md` that told every agent a live naming rule was revoked.

**A checker that passes a defect is worse than no checker**, so these tests pin
the three things that must never silently invert:

1. The bare form FAILS. `PLAN D7` is the sentence that shipped the defect, and
   it must never clear.
2. Every accepted HOME form clears, including across a line wrap, because a
   rule that fires on reflow gets fought and then disabled.
3. The exemptions stay NARROW. The file-level declaration, the historical
   directories and the locator exemption each let real text through, so each
   one is tested for what it lets through AND for what it must still catch.

Run: `python3 scripts/tests/test_rule_series.py`
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_rule_ids", ROOT / "scripts" / "check-rule-ids.py"
)
cri = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cri)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


DECISIONS = cri.known_decisions()
TWINS = cri.dd_numbers(DECISIONS)
FAKE = ROOT / "dev" / "fake-live-document.md"   # never written; a label for paths


def findings(text: str, path: Path = FAKE) -> list[str]:
    return cri.series_findings(path, text, TWINS)


def flagged(text: str) -> bool:
    return any("reads as the live series" in f for f in findings(text))


def located(text: str) -> bool:
    return any("holds the `DD` table" in f for f in findings(text))


# ---------------------------------------------------------------------------
# 1. The twin set. This is what makes a citation ambiguous in the first place.
# ---------------------------------------------------------------------------
print("the twin set: which numbers BOTH series carry")

check("every number 1 to 27 has a DD row", all(str(n) in TWINS for n in range(1, 28)),
      f"missing {[n for n in range(1, 28) if str(n) not in TWINS]}")
check("28 and above have no DD twin",
      not any(str(n) in TWINS for n in range(28, 40)))
check("the archived D series still resolves", "D36" in DECISIONS and "D20" in DECISIONS)
check("a revoked DD code still resolves", "DD7" in DECISIONS)


# ---------------------------------------------------------------------------
# 2. THE DEFECT. `PLAN D7` is the exact sentence that shipped.
# ---------------------------------------------------------------------------
print("the bare form fails")

check("a bare code with a twin is flagged", flagged("names like `isL'`; PLAN D7."))
check("and the message names the twin",
      "DD7" in findings("names like `isL'`; PLAN D7.")[0])
check("a bare code with NO twin is not flagged", not flagged("the deletion test (D36)"))
check("a DD code is never read as a D reference", not flagged("DD7 is REVOKED outright"))
check("a LESSONS id is never read as a decision", not flagged("see D-10 for the wall rule"))
check("a hyphenated task code is not a decision", not flagged("recorded as `[L3.30-D1]`"))


# ---------------------------------------------------------------------------
# 3. Every accepted HOME form clears, and nothing else does.
# ---------------------------------------------------------------------------
print("the home forms")

for form in ("archived D7 is naming hygiene",
             "the struck D8 row of the archive",
             "fixed by archived PLAN D5, whose live statement is section 4",
             "so archived `D22` and lesson `D-22` differ",
             "ruled by D20 (archived), 2026-08-04",
             "ruled by D20, archived, 2026-08-04",
             "under D17's archived regime"):
    check(f"clears: {form[:44]}", not flagged(form))

check("a wrap clears: the marker ends the previous line",
      not flagged("the rule was set by archived\nD7 and it still binds"))
check("a wrap clears through an opening backtick",
      not flagged("so archived\n`D22` and lesson `D-22` differ"))
check("the wrap does not reach past ONE line",
      flagged("archived\nis the word, and\nD7 is the code"))

# THE CASE THAT KILLED THE WINDOW DESIGN. `dev/STYLE-agda.md:11` used the word
# `archived` 27 characters after the code, about its tension register. Any
# window wide enough to be useful cleared this line, and it was a real defect.
check("a distant `archived` about ANOTHER noun does not clear",
      flagged("(PLAN D11; tension T1's register is archived at `dev/memos/x.md`)"))
check("`archive` without the `d` does not clear",
      flagged("- **archive** (D20). No live master may import"))
check("naming the archive DIRECTORY does not clear",
      flagged("The archive (archive/) is outside every gate (D20)."))


# ---------------------------------------------------------------------------
# 4. The file-level declaration: narrow, visible, and it does not leak.
# ---------------------------------------------------------------------------
print("the file-level declaration")

DECL = cri.DECLARATION_TEXT
check("the declaration text the tool prints is a declaration the tool accepts",
      not flagged(DECL + "\n\nRetired under D17 and D20, 2026-08-06."))
check("without it the same rows are flagged",
      flagged("Retired under D17 and D20, 2026-08-06."))
check("the declaration survives a paragraph wrap",
      not flagged("**D-SERIES NOTE.** Every bare `D<n>` in this file is the\n"
                  "archived decision series, in\n"
                  "`archive/dev/DECISIONS-archived.md`.\n\nRetired under D20."))
check("a declaration missing its home does NOT clear the file",
      flagged("**D-SERIES NOTE.** These are the archived decision series.\n"
              "\nRetired under D20, 2026-08-06."))
check("prose that merely mentions the archived series does not clear the file",
      flagged("The whole D series is archived.\n\nRetired under D20, 2026-08-06."))


# ---------------------------------------------------------------------------
# 5. The locator rule: section 3 holds the DD table and no D row.
# ---------------------------------------------------------------------------
print("the locator rule")

check("a code sent to PLAN section 3 is flagged",
      located("blind to them (D20, `dev/PLAN.md` section 3)."))
check("the section sign form is flagged",
      located("ruled by D20 in PLAN §3, 2026-08-04"))
check("a DD code on the line exempts it",
      not located("archived D11; DD11 in PLAN §3 is a DIFFERENT rule"))
check("section 3 of ANOTHER document is not the locator defect",
      not located("its cold check at archival was 5.7 s (`[T234]` section 3), D20"))
check("a distant section 3 is not attached to the code",
      not located("D20 governs the archive, and the whole of this file, "
                  "which nobody reads twice, restates what PLAN section 3 said"))
check("the locator fires even where the home is written",
      located("archived D20 is stated in `dev/PLAN.md` section 3"))


# ---------------------------------------------------------------------------
# 6. THE SCOPE. What the default run reads, and what it deliberately does not.
# ---------------------------------------------------------------------------
print("the scope of the default run")

check("dev/JOURNAL.md is a dated record and is skipped", "JOURNAL.md" in cri.HISTORICAL)
check("dev/memos/ are dated analyses and are skipped", "memos" in cri.HISTORICAL_DIRS)
check("scripts/tests/ is skipped so a fixture stays verbatim",
      "tests" in cri.SERIES_SKIP_DIRS)

# THE SCOPE IS READ FROM THE TOOL, never assumed: a checker that silently
# stopped reading a directory would still print "clean". An earlier version of
# this file proved scope by APPENDING a defect to each file and restoring it in
# a `finally`. That is a real edit to a file another agent may be holding, and
# on 2026-08-13 one was. `series_target_paths` exists so the assertion costs no
# write at all.
scope = {str(p.relative_to(ROOT))
         for p in cri.series_target_paths(cri.default_targets())}

for target in ("dev/LESSONS.md", "dev/PLAN.md", "dev/ARCHIVE.md",
               "dev/STYLE-agda.md", "dev/literature/owner-notes-rud.md",
               "scripts/README.md", "scripts/check-tree.py", "scripts/ledger.py"):
    check(f"{target} is inside the default series scope", target in scope)

check("scripts/*.py reach the series scope and nothing else adds them",
      "scripts/ledger.py" in scope
      and "scripts/ledger.py" not in {str(p.relative_to(ROOT))
                                      for p in cri.default_targets()})
check("dev/JOURNAL.md is not in the series scope", "dev/JOURNAL.md" not in scope)
check("no memo is in the series scope",
      not any(s.startswith("dev/memos/") for s in scope))
check("no test fixture is in the series scope",
      not any(s.startswith("scripts/tests/") for s in scope))
check("agents/ is out even when the citation check opts in",
      not any(s.startswith("agents/") for s in
              {str(p.relative_to(ROOT))
               for p in cri.series_target_paths(cri.default_targets(briefs=True))}))
check("an explicit path list is NOT widened to scripts/",
      cri.series_target_paths([ROOT / "dev" / "PLAN.md"], widen=False)
      == [ROOT / "dev" / "PLAN.md"])

# dev/ARCHIVE.md carries the declaration, so its 70 dated rows are exempt. That
# is the exemption's blast radius, and it is measured on the real file.
arch = (ROOT / "dev" / "ARCHIVE.md").read_text(encoding="utf-8")
check("dev/ARCHIVE.md declares its series, so its own rows are exempt",
      not flagged(arch))
check("and stripping the declaration would flag them again",
      flagged(arch.replace("**D-SERIES NOTE.**", "Note.")))
check("the declaration does NOT exempt the locator rule in that file",
      located(arch + "\nRuling D20, `dev/PLAN.md` section 3.\n"))

import subprocess  # noqa: E402  (only the CLI tests need it)

PY = sys.executable
SCRIPT = str(ROOT / "scripts" / "check-rule-ids.py")


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([PY, SCRIPT, *args], cwd=ROOT, capture_output=True, text=True)


# THE PENDING HANDOVER, and this assertion is written to survive it.
# `[LJ-1.140]` repaired every live document EXCEPT `scripts/README.md`, whose
# four defective lines are handed to the orchestrator as finished text because
# `[LJ-1.141]` held that file on 2026-08-13. So the tree is allowed to be red
# THERE and nowhere else. When the handover lands the run goes clean and this
# still passes; if any OTHER file goes red, it fails.
r = run()
stray = [ln for ln in r.stdout.splitlines()
         if "DEFECT" in ln and "scripts/README.md" not in ln]
check("no live document outside the pending handover is red", not stray,
      "\n".join(stray[:6]))
check("the run exits non-zero while the handover is pending, or clean after it",
      r.returncode in (0, 1), f"got {r.returncode}")
check("an explicit clean file still reports clean",
      run("dev/PLAN.md").returncode == 0)

# A directory argument used to raise IsADirectoryError, because Path.exists()
# is true of a directory and read_text() is not. `check-rule-ids.py dev/` is
# the obvious thing to type.
rdir = run("dev/")
check("a directory argument is expanded, not crashed on",
      rdir.returncode in (0, 1) and "Traceback" not in rdir.stderr, rdir.stderr[-300:])
check("and it scans more than one file", "1 files" not in rdir.stdout, rdir.stdout)


# ---------------------------------------------------------------------------
# 7. THE TWO SITES THE TASK EXISTED FOR. Pinned by content, not by line.
# ---------------------------------------------------------------------------
print("the sites that shipped the defect")

style = (ROOT / "dev" / "STYLE-agda.md").read_text(encoding="utf-8")
check("dev/STYLE-agda.md no longer writes a bare decision code",
      not flagged(style))
check("and it still tells the reader the naming rule is live, not revoked",
      "DD7" in style and "revoked" in style.lower())

# scripts/README.md is the PENDING HANDOVER and its four lines are still bare.
# The assertion is on the CHECKER seeing them, not on the file being fixed, so
# this test says the same thing before and after the orchestrator applies the
# text: the defect there is visible rather than exempted.
readme = (ROOT / "scripts" / "README.md").read_text(encoding="utf-8")
check("scripts/README.md is read by the series check, fixed or not",
      "scripts/README.md" in scope)
check("while its locator defect stands, the CLI REPORTS it rather than exempting it",
      (not located(readme))
      or any("scripts/README.md" in ln and "holds the `DD` table" in ln
             for ln in r.stdout.splitlines()),
      "the file still misdirects a code and the run did not say so")


print("")
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_rule_series: all checks passed")
