#!/usr/bin/env python3
"""Fail any rule ID that does not name a real `dev/LESSONS.md` entry.

WHY THIS EXISTS. A proposal written on 2026-08-06 to stop the rule corpus from
drifting **itself shipped a rule ID that does not exist**
(`"D-19-is-not-quotable"`), and the adversarial reviewer found it. That is the
whole argument for this file: if the orchestrator writing a document ABOUT rule
hygiene invents an ID, then every other document does too, and a citation
nobody can resolve is worse than no citation, because it reads as authority.

The same class has a second face. `dev/PLAN.md` numbers its decisions `D18`,
`D22`, `D30`, and `dev/LESSONS.md` numbers a design series `D-1`, `D-10`,
`D-19`. The two look almost identical and mean different things, so a brief
that says "D-22" when it means PLAN's D22 points at a lesson about gating that
happens to exist, and a brief that says "D17" when it means the lesson points
at nothing. This checker knows the difference.

WHAT IT CHECKS. Every token in a scanned file that looks like a LESSONS ID
(`P-a`, `R-38`, `Rule 14`, `I-5`, `D-10`, `C-22`, `T-3`) must appear as a
heading in `dev/LESSONS.md`. PLAN-style decision references (`D18`, no hyphen)
are checked against `dev/PLAN.md`'s decision table instead.

WHAT IT DOES NOT DO. It cannot tell you a citation is APT, only that it
resolves. `[L3.32-T105]` established that citation is not application, and this
tool does not pretend otherwise: it removes one specific failure, the dangling
pointer, and claims nothing more.

USAGE
    python3 scripts/check-rule-ids.py                 # dev/ and AGENTS.md
    python3 scripts/check-rule-ids.py <files...>
    python3 scripts/check-rule-ids.py --briefs        # also agents/briefs/
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

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
# PLAN decisions: `D18`, `D30`, no hyphen.
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


def duplicate_lessons() -> list[str]:
    """IDs carried by more than one heading in dev/LESSONS.md.

    [L3.32-T226] 2026-08-08: `C-23` numbered two different laws. Every citation
    in the tree resolved to the older one, so the newer law was uncitable and
    nothing noticed, because a citation check only asks whether an ID EXISTS. A
    duplicate ID passes that question twice. It is caught here instead: the ID
    is the address, so two laws at one address is a defect at the source.
    """
    seen: dict[str, int] = {}
    for h in lesson_headings():
        seen[h] = seen.get(h, 0) + 1
    return sorted(k for k, n in seen.items() if n > 1)


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


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--briefs", action="store_true",
                    help="also scan agents/briefs/, which the default run skips")
    args = ap.parse_args()

    lessons, decisions = known_lessons(), known_decisions()
    if (dupes := duplicate_lessons()):
        for d in dupes:
            print(f"check-rule-ids: dev/LESSONS.md: `{d}` numbers more than one law. "
                  f"An ID is an address: a citation resolves to whichever heading is "
                  f"found first, and the other law cannot be cited at all. Renumber "
                  f"the one nothing cites yet.")
        return 1
    if not lessons:
        print("check-rule-ids: no headings found in dev/LESSONS.md; refusing to "
              "pass a check whose reference set is empty")
        return 1

    targets = [p if p.is_absolute() else ROOT / p for p in args.paths]
    if not targets:
        targets = sorted((ROOT / "dev").rglob("*.md")) + [ROOT / "AGENTS.md"]
        if args.briefs:
            targets += sorted((ROOT / "agents" / "briefs").glob("*.md"))
    targets = [p for p in targets if p.exists() and p.name != "LESSONS.md"]

    findings: list[str] = []
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
