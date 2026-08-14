#!/usr/bin/env python3
"""Fail any rule ID that does not name a real `dev/LESSONS.md` entry.

WHY THIS EXISTS. A proposal written on 2026-08-06 to stop the rule corpus from
drifting **itself shipped a rule ID that does not exist**
(`"D-19-is-not-quotable"`), and the adversarial reviewer found it. That is the
whole argument for this file: if the orchestrator writing a document ABOUT rule
hygiene invents an ID, then every other document does too, and a citation
nobody can resolve is worse than no citation, because it reads as authority.

The same class has a second face. The decision series is numbered without a
hyphen and the `dev/LESSONS.md` design series is numbered with one, so archived
`D22` and lesson `D-22` are two characters apart and mean unrelated things. A
brief that writes the hyphen when it means the decision points at a lesson
about gating that happens to exist. This checker knows the difference.

WHAT IT CHECKS. Every token in a scanned file that looks like a LESSONS ID
(`P-a`, `R-38`, `Rule 14`, `I-5`, `D-10`, `C-22`, `T-3`) must appear as a
heading in `dev/LESSONS.md`. Decision references without the hyphen are checked
against `dev/PLAN.md`'s decision table instead.

THE SERIES CHECK, added 2026-08-13 by `[LJ-1.140]`. Resolution is not enough
when TWO series share the numbers. The whole `D` series was archived on
2026-08-09 and the live series is `DD`, so a bare code in a live document
resolves against the archive, which is all the check above asks, and points a
reader at the `DD` row of the same number, which is a different rule. Archived
D7 is naming hygiene and DD7 is REVOKED, so two lines of `dev/STYLE-agda.md`
told every agent that a live naming rule was dead. **In a live document a bare
`D<n>` must write its HOME beside the code when a `DD<n>` row exists.** Write
`archived D7` or `struck D8`; the bare form is the defect.

WHAT IT DOES NOT DO. It cannot tell you a citation is APT, only that it
resolves. `[L3.32-T105]` established that citation is not application, and this
tool does not pretend otherwise: it removes one specific failure, the dangling
pointer, and claims nothing more. **The series check cannot tell which series
an author MEANT either.** It reads the word beside the code, never the
sentence. A citation labelled `archived D5` that argues DD5's content passes
green, and so does a live `DD` rule miscited as `D` and then labelled archived.
The check removes the SILENT retarget, where nothing beside the code warns the
reader at all, and it claims nothing more than that.

USAGE
    python3 scripts/check-rule-ids.py                 # dev/, AGENTS.md, scripts/
    python3 scripts/check-rule-ids.py <files...>
    python3 scripts/check-rule-ids.py --briefs        # also agents/tasks/
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agents_tree   # [LJ-1.142]: the briefs moved into agents/tasks/<TASK>/

ROOT = Path(__file__).resolve().parent.parent
LESSONS = ROOT / "dev" / "LESSONS.md"
PLAN = ROOT / "dev" / "PLAN.md"

# A LESSONS heading: `### P-h.` / `### R-38.` / `### Rule 14.` / `### C-23.`
#
# The shapes are NARROW on purpose. A first version accepted
# `[PRTIDC]-[a-z0-9]+` and flagged `T-function`, `I-ideal`, `D-bucket`,
# `C-prime` and `P-names`: ordinary English written with a capital, which is
# not rare in these documents. A checker that cries wolf on prose is a checker
# that gets disabled, so: the P series is a SINGLE lowercase letter, and every
# other series is DIGITS ONLY.
HEADING = re.compile(r"^###\s+((?:Rule\s+\d+)|(?:P-[a-z](?![a-z]))|(?:[RTIDC]-\d+))\b", re.M)
CITATION = re.compile(
    r"(?<![\w-])((?:Rule\s+\d+)|(?:P-[a-z](?![a-z\w-]))|(?:[RTIDC]-\d+))(?![\w-])")
# Decision references: one `D`, then digits, no hyphen.
PLAN_REF = re.compile(r"(?<![\w-])(D\d{1,2})(?![\w-])")
PLAN_ROW = re.compile(r"^\|\s*(D\d{1,2})\s*\|", re.M)
# The LIVE series since 2026-08-09 is `DD`. The whole `D` series was archived
# to archive/dev/DECISIONS-archived.md when the owner rebuilt the list on the
# two-tower bridge ruling, and `D` citations still RESOLVE against that file:
# hundreds of them sit in JOURNAL, the memos, the briefs and the git history,
# and they are true to what they meant when written. A number is never reused
# in either series. Note the lookbehind on PLAN_REF: it makes `DD5` fail to
# match as a `D` reference, which is what keeps the two series apart.
DD_REF = re.compile(r"(?<![\w-])(DD\d{1,2})(?![\w-])")
DD_ROW = re.compile(r"^\|\s*(DD\d{1,2})\s*\|", re.M)
ARCHIVED_DECISIONS = ROOT / "archive" / "dev" / "DECISIONS-archived.md"
# A DD code merged into another row, or revoked, still RESOLVES. PLAN names
# them in one paragraph and says so, for the same reason the D series does:
# a commit message or brief that cites a code is a record of what was true
# when it was written, and a checker that failed it would be arguing with the
# document it checks.
DD_CONSOLIDATED = re.compile(
    r"\*\*Consolidated and revoked codes\.\*\*(.*?)(?=\n\n)", re.S)
# Struck decisions still RESOLVE, and PLAN says so in as many words: their full
# original text is preserved in dev/JOURNAL.md "so a commit message citing a
# struck code still resolves", and numbers are never reused. A checker that
# failed those citations would be arguing with the document it checks.
PLAN_RETIRED = re.compile(
    r"\*\*Retired decisions\.\*\*(.*?)were struck", re.S)

# `dev/JOURNAL.md` is a dated historical record, not live guidance: an entry
# from July that cites a decision struck in August is CORRECT as history, and
# rewriting it would falsify the record. PLAN itself says the struck decisions'
# text is preserved there so an old citation still resolves.
HISTORICAL = {"JOURNAL.md"}

# Route memos under dev/memos/ are dated analyses, not live guidance: a memo
# written in July that reasons from a decision struck in August is correct as
# history. They are checked for LESSONS IDs, which are never renumbered, but
# not for decision currency.
HISTORICAL_DIRS = {"memos"}

# --------------------------------------------------------------------------
# THE SERIES CHECK: two series share the numbers, so resolving is not enough.
# --------------------------------------------------------------------------
# THE HOME, written beside the code. The forms accepted are deliberately few,
# so the failure message can print the whole set: the marker word is the word
# immediately before the code, or the first word after it. A WINDOW was tried
# first and refused. `dev/STYLE-agda.md:11` cited an archived code and then
# used the word `archived` 27 characters later, about a DIFFERENT noun, its
# tension register. Any window wide enough to accept a code followed by the
# archived-decisions path also accepted that line, and a false clear on a real
# defect is the failure this whole check exists to stop.
# The trailing character class lets the marker survive a quoted code, which is
# how these documents usually write one: ``archived `D7` `` must clear.
SERIES_HOME_BEFORE = re.compile(
    r"(?:archived|struck)\s+(?:PLAN\s+)?[`'\"(\[]?$", re.I)
SERIES_HOME_AFTER = re.compile(
    r"^[`'\"\)\]]*(?:'s|’s)?\s*[(\[,;:]?\s*(?:archived|struck)\b", re.I)
# A code that begins its line carries the previous line's tail as its context.
# Without this the rule punishes a reflow: `dev/` prose wraps at about 80
# columns, so "archived" and its code land on two lines often, and a checker
# that fires on line breaks teaches people to fight the formatter.
LINE_START = re.compile(r"^[\s`'\"(\[]*$")

# A file whose `D` codes are ALL the archived series may declare it ONCE
# instead of writing the home at every row. `dev/ARCHIVE.md` is the case that
# forced this: 70 of its rows are dated retirement records from the `D` era,
# each reading "Retired on this date under these two codes", and repeating the
# home 70 times would say one thing seventy times. It is a FIXED SENTENCE, so a
# machine finds it and a human still reads it; an invisible marker would warn
# the checker and not the reader, which is the wrong way round.
# Matched against the file with its whitespace collapsed, so the sentence may
# wrap across lines like any other paragraph.
SERIES_DECLARATION = re.compile(
    r"\*\*D-SERIES NOTE\.\*\* .{0,120}?archived decision series"
    r".{0,120}?DECISIONS-archived\.md", re.I)
DECLARATION_TEXT = (
    "**D-SERIES NOTE.** Every bare `D<n>` in this file is the archived "
    "decision series, in `archive/dev/DECISIONS-archived.md`. The live series "
    "is `DD` and the two do not correspond.")

# THE LOCATOR RULE. `dev/PLAN.md` section 3 holds the `DD` table and nothing
# else, so a citation that sends a `D<n>` there names a location that cannot
# hold it. This is the same defect wearing a second face, and it is the worst
# one found, because the reader is told exactly where to look and looks there.
#
# A line that names a `DD` code of its own is EXEMPT, and the exemption is the
# whole reason the rule is usable. The repaired sentences read "archived D11
# ...; DD11 in PLAN section 3 is a DIFFERENT rule", so the section-3 pointer
# belongs to the `DD` code beside it and the reader has already been told which
# series lives there. THE COST, stated rather than hidden: a line that cites
# one code correctly and misdirects a second one passes. The rule catches the
# bare misdirection, which is every instance found in this tree.
PLAN_HERE = re.compile(r"PLAN(?:\.md)?", re.I)
SECTION_3 = re.compile(r"(?:section\s+3|§\s?3)\b", re.I)
LOCATOR_SPAN = 70

# The tests under scripts/tests/ are NOT scanned for the series rules, and the
# reason is not laziness. `test_dev_docs.py` carries FIXTURES that reproduce
# `dev/PLAN.md` rows verbatim, decision codes and all, to pin what the checkers
# do to real document text; `:153` writes a bare decision code on purpose, to
# test that the hyphenated lesson pattern does not swallow it. Rewriting a
# fixture to satisfy a checker falsifies the test it belongs to.
SERIES_SKIP_DIRS = {"tests"}

# `agents/` is a FROZEN RECORD, and the same reason exempts it that exempts
# dev/JOURNAL.md: a brief says what an agent was told on a date and a report
# says what it found, so a citation there is true of its own moment and nobody
# rewrites it. `lint-prose.py` already drops the tree for this reason. Measured
# 2026-08-13: with the rest of the tree green, `--briefs` carried 487 findings
# and 485 of them were series findings inside `agents/`, on text that must not
# change. That is the noise that gets a gate switched off.
SERIES_SKIP_TREES = ("agents/",)

# The antecedent development has its OWN R and P numbering, and this repository
# legitimately cites it: P-i is imported from it whole. A citation qualified as
# the source project's is therefore correct and must not be resolved against
# dev/LESSONS.md. Marking it is also the point: an unqualified `R-9` reads as a
# local law and there is no local R-9, this repo's R series running 21 to 39.
FOREIGN = re.compile(r"source project's\s+$")


def lesson_headings() -> list[str]:
    return [m.group(1).replace("  ", " ") for m in HEADING.finditer(
        LESSONS.read_text(encoding="utf-8"))]


def known_lessons() -> set[str]:
    return set(lesson_headings())


def duplicate_codes(codes: list[str]) -> list[str]:
    """Codes carried by more than one element of `codes`, sorted.

    [LJ-1.194] extracted this from `duplicate_lessons` so every series shares
    ONE counting path: the `DD` rows of dev/PLAN.md section 3, the retired `D`
    rows of the archive, and all six LESSONS prefixes. A code is an address;
    two laws at one address is a defect at the source, whichever series.
    """
    seen: dict[str, int] = {}
    for c in codes:
        seen[c] = seen.get(c, 0) + 1
    return sorted(k for k, n in seen.items() if n > 1)


def duplicate_lessons() -> list[str]:
    """IDs carried by more than one heading in dev/LESSONS.md.

    [L3.32-T226] 2026-08-08: `C-23` numbered two different laws. Every citation
    in the tree resolved to the older one, so the newer law was uncitable and
    nothing noticed, because a citation check only asks whether an ID EXISTS. A
    duplicate ID passes that question twice. It is caught here instead: the ID
    is the address, so two laws at one address is a defect at the source.
    """
    return duplicate_codes(lesson_headings())


def duplicate_decisions(plan_text: str | None = None,
                        arch_text: str | None = None) -> list[str]:
    """A code that appears in more than ONE row of its series, as a finding.

    [LJ-1.194], the uniqueness half the citation check cannot see. On
    2026-08-14 the orchestrator minted a duplicate `DD27` when `DD27` had been
    ruled on 2026-08-10, and this checker reported CLEAN through the episode,
    because it verifies that a code RESOLVES and never that a code is UNIQUE.
    PLAN's own preamble says a number is never reused, in either series, so
    the rule existed and nothing enforced it.

    THE SERIES BOUNDARY IS THE FILE. The live `DD` rows live in dev/PLAN.md
    section 3 and the retired `D` rows in archive/dev/DECISIONS-archived.md, so
    `DD5` and the archived `D5` are DIFFERENT codes and both may exist.
    Uniqueness is judged WITHIN a series, never across one. The consolidated
    and revoked codes are preamble prose, never rows, so they cannot be
    reported: they still resolve on purpose, and a row that was never a row
    cannot be a duplicate row.

    The texts are parameters so a test can feed a synthetic duplicate without
    writing to the tree; `series_findings` takes its text for the same reason.
    """
    text = PLAN.read_text(encoding="utf-8") if plan_text is None else plan_text
    arch = (ARCHIVED_DECISIONS.read_text(encoding="utf-8")
            if arch_text is None else arch_text)
    dd = [m.group(1) for m in DD_ROW.finditer(text)]
    d = [m.group(1) for m in PLAN_ROW.finditer(arch)]
    out: list[str] = []
    for dup in duplicate_codes(dd):
        out.append(
            f"`{dup}` appears in {dd.count(dup)} rows of the `DD` series "
            f"(dev/PLAN.md section 3), and PLAN's preamble says a number is "
            f"never reused in either series. A `DD` row is the owner's (DD0): "
            f"report the duplicate, never fix it.")
    for dup in duplicate_codes(d):
        out.append(
            f"`{dup}` appears in {d.count(dup)} rows of the retired `D` series "
            f"(archive/dev/DECISIONS-archived.md), and PLAN's preamble says a "
            f"number is never reused in either series. The archive is a frozen "
            f"record: report the duplicate, never fix it.")
    return out


def known_decisions() -> set[str]:
    text = PLAN.read_text(encoding="utf-8")
    arch = ARCHIVED_DECISIONS.read_text(encoding="utf-8")
    live = {m.group(1) for m in PLAN_ROW.finditer(arch)}
    live |= {m.group(1) for m in DD_ROW.finditer(text)}
    struck: set[str] = set()
    m = PLAN_RETIRED.search(arch)
    if m:
        struck = set(re.findall(r"\bD\d{1,2}\b", m.group(1)))
    m = DD_CONSOLIDATED.search(text)
    if m:
        struck |= set(re.findall(r"\bDD\d{1,2}\b", m.group(1)))
    return live | struck


def dd_numbers(decisions: set[str]) -> set[str]:
    """The digits that BOTH series carry, which is where a citation retargets."""
    return {d[2:] for d in decisions if d.startswith("DD")}


def series_target_paths(targets: list[Path], widen: bool = True) -> list[Path]:
    """The files the series check reads, which is a WIDER set than the citation
    check reads, and both differences are deliberate.

    `dev/LESSONS.md` is dropped from the citation targets because it holds the
    headings that check resolves against; it cites decisions like any other
    live document, so the series rule binds it. `scripts/` is prose an agent
    reads before it edits a checker, and 27 of its lines cited a `D` code with
    a live `DD` twin.

    This is a FUNCTION rather than inline set-building so a test can assert the
    scope WITHOUT writing to the tree. The first version proved scope by
    appending a defect to each file and restoring it; that is a real edit to a
    file another agent may be holding, and on 2026-08-13 one was.
    """
    out = list(targets)
    if widen:
        out += sorted((ROOT / "scripts").glob("*.py"))
        out += [ROOT / "scripts" / "README.md"]
    return [p for p in out
            if p.exists() and p.name not in HISTORICAL
            and p.parent.name not in HISTORICAL_DIRS
            and p.parent.name not in SERIES_SKIP_DIRS
            and not str(p.relative_to(ROOT)).startswith(SERIES_SKIP_TREES)]


def default_targets(briefs: bool = False) -> list[Path]:
    """The citation check's default file set, named so a test can read it."""
    out = sorted((ROOT / "dev").rglob("*.md")) + [ROOT / "AGENTS.md"]
    if briefs:
        out += agents_tree.briefs()   # [LJ-1.142]: agents/tasks/<TASK>/
    return [p for p in out if p.exists()]


def series_findings(path: Path, text: str, twins: set[str]) -> list[str]:
    """A `D<n>` with a `DD<n>` twin, cited in a live document with no home."""
    rel = path.relative_to(ROOT)
    declared = bool(SERIES_DECLARATION.search(re.sub(r"\s+", " ", text)))
    out: list[str] = []
    prev = ""
    for i, line in enumerate(text.splitlines(), 1):
        dd_on_line = bool(DD_REF.search(line))
        for m in PLAN_REF.finditer(line):
            code, before, after = m.group(1), line[:m.start()], line[m.end():]
            if LINE_START.match(before):
                before = prev.rstrip() + " " + before
            homed = bool(SERIES_HOME_BEFORE.search(before)
                         or SERIES_HOME_AFTER.match(after))
            # The locator rule fires whatever the home says, because a home and
            # a wrong location are two different claims and the second is the
            # one the reader acts on.
            for s in ([] if dd_on_line else SECTION_3.finditer(line)):
                near = abs(s.start() - m.start()) <= LOCATOR_SPAN
                if near and PLAN_HERE.search(line[max(0, s.start() - 40):s.start()]):
                    out.append(
                        f"{rel}:{i}: `{code}` is sent to `dev/PLAN.md` section 3, "
                        f"which holds the `DD` table and no `D` row. The archived "
                        f"series is in archive/dev/DECISIONS-archived.md")
                    break
            if homed or declared or code[1:] not in twins:
                continue
            out.append(
                f"{rel}:{i}: `{code}` is bare and `DD{code[1:]}` exists, so it "
                f"reads as the live series. Write the home beside the code: "
                f"`archived {code}` or `struck {code}`")
        prev = line
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--briefs", action="store_true",
                    help="also scan agents/tasks/, which the default run skips")
    args = ap.parse_args()

    lessons, decisions = known_lessons(), known_decisions()
    if (dupes := duplicate_lessons()):
        for d in dupes:
            print(f"check-rule-ids: dev/LESSONS.md: `{d}` numbers more than one law. "
                  f"An ID is an address: a citation resolves to whichever heading is "
                  f"found first, and the other law cannot be cited at all. Renumber "
                  f"the one nothing cites yet.")
        return 1
    if (dupes := duplicate_decisions()):
        for f in dupes:
            print(f"  DEFECT: {f}")
        print(f"\ncheck-rule-ids: {len(dupes)} duplicate code(s). A number is "
              f"never reused, in either series, and a code in two rows reads "
              f"as one rule twice. A `DD` row is the owner's (DD0): report "
              f"the duplicate, never fix it.")
        return 1
    if not lessons:
        print("check-rule-ids: no headings found in dev/LESSONS.md; refusing to "
              "pass a check whose reference set is empty")
        return 1

    # A DIRECTORY argument used to crash with IsADirectoryError, because
    # `Path.exists()` is true of one and `read_text()` is not. Expand it
    # instead: `check-rule-ids.py dev/` is the obvious thing to type and it
    # should do the obvious thing.
    given = [p if p.is_absolute() else ROOT / p for p in args.paths]
    targets: list[Path] = []
    for p in given:
        if p.is_dir():
            targets += sorted(q for q in p.rglob("*")
                              if q.suffix in (".md", ".py") and q.is_file())
        elif p.is_file():
            targets.append(p)
    targets = targets or default_targets(args.briefs)

    series_targets = series_target_paths(targets, widen=not args.paths)

    targets = [p for p in targets if p.name != "LESSONS.md"]

    findings: list[str] = []
    for path in series_targets:
        findings += series_findings(
            path, path.read_text(encoding="utf-8"), dd_numbers(decisions))
    for path in targets:
        text = path.read_text(encoding="utf-8")
        for i, line in enumerate(text.splitlines(), 1):
            for m in CITATION.finditer(line):
                tok = re.sub(r"\s+", " ", m.group(1))
                if tok in lessons or FOREIGN.search(line[:m.start()]):
                    continue
                findings.append(
                    f"{path.relative_to(ROOT)}:{i}: `{tok}` is not a heading in "
                    f"dev/LESSONS.md")
            if path.name in HISTORICAL or path.parent.name in HISTORICAL_DIRS:
                continue
            for m in PLAN_REF.finditer(line):
                if m.group(1) not in decisions:
                    findings.append(
                        f"{path.relative_to(ROOT)}:{i}: `{m.group(1)}` is not a "
                        f"decision in archive/dev/DECISIONS-archived.md")
            for m in DD_REF.finditer(line):
                if m.group(1) not in decisions:
                    findings.append(
                        f"{path.relative_to(ROOT)}:{i}: `{m.group(1)}` is not a "
                        f"decision in dev/PLAN.md section 3")

    if not findings:
        print(f"check-rule-ids: clean ({len(targets)} files, "
              f"{len(lessons)} lessons, {len(decisions)} decisions)")
        return 0
    for f in findings:
        print(f"  DEFECT: {f}")
    print(f"\ncheck-rule-ids: {len(findings)} dangling reference(s). A citation "
          f"nobody can resolve reads as authority and is worse than none.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
