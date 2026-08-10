#!/usr/bin/env python3
"""Maintenance mechanism for the dev/ documents: size caps, routing, dates.

WHY THIS EXISTS. On 2026-08-06 every decay instance below was found by
accident, none by a gate: AGENTS.md had grown to 3,450 words, a PLAN table
cell held 12,634 words of episode content, an imported playbook sat in
LESSONS.md for five days without reaching a brief, a memo's central diagnosis
was refuted without the memo saying so, and PLAN section 0's "where the work
stands" date lagged the work it described. The same decay then recurred in the
section 11 goal rows: the `L3.32-F5` row held 1,119 words of episode content,
so `[T112]` added a character cap for a goal row, derived from what a register
row must actually say. AGENTS.md's own rule is that a rule that is not
machine-enforced must name an enforcement point, and a rule whose enforcement
point is "the orchestrator, periodically" is exactly what failed.

WHAT THIS CHECKER DOES, AND WHERE. The gate half (`--check`, wired into
`make check` as the `devdocs` target) is six cheap, pure-Python reads, each
true-positive-tuned against the tree on 2026-08-06:

  agents-size         AGENTS.md word count is capped (threshold in
                      this docstring). The file is auto-loaded into every
                      session, so its size is a context budget, not a style.
  plan-cell-size      every table cell in dev/PLAN.md is capped by word count,
                      and the section 11 goal rows additionally by character
                      count, so a cell can be a ruling plus a pointer but
                      never a document.
  lessons-imported-routing
                      a LESSONS entry whose heading marks it as imported must
                      be routed in dev/rules.toml (a bundle or a trigger).
                      Imported content arrives whole from outside, with no
                      local measurement that forces discovery, which is the
                      exact class that sat uncited for five days.
  plan-section0-date  the date in the `## 0.` heading must be no older than
                      the newest date in the section's own body. The heading
                      is the "as of" contract; a body that describes newer
                      work than the heading dates is the measured decay.
  memo-status-form    any dev/memos/ file carrying a `**STATUS:` blockquote
                      must state a verdict word, so a refutation, once
                      recorded, stays honest. Whether a refutation HAS
                      happened is a review judgement (dev/ORCHESTRATION.md
                      section 6), not a lexical fact.
  agents-enforcers    every `scripts/*.py` path named in AGENTS.md's rules
                      table must exist. The table's third column is the
                      enforcement-point contract; a named enforcer that
                      vanished would make the contract a wish.

The sweep half (`--sweep`) is informational, never a gate, and exits 0. It
lists LESSONS entries that are unrouted AND cited nowhere in the live corpus
or any brief (the "landed and nobody noticed" class: a new entry starts with
zero citations, so it surfaces here until it is routed or cited), and section
11 cells over the episode-scale line (more than a ruling plus a pointer,
which the JOURNAL taxonomy says belongs in dev/JOURNAL.md).

WHY SOME DECAY IS NOT HERE. Struck-decision references and antecedent-project
rule IDs are already enforced by `scripts/check-rule-ids.py`, which is in the
gate; duplicating them would split the canonical home. Whether a memo's
diagnosis was refuted, and whether AGENTS.md text duplicates a checker,
require reading and are named review steps, recorded below.

HOW A THRESHOLD IS RAISED. A cap that anyone may raise silently is not a cap.
The gate thresholds are constants below, and raising one is a ruling: only
the owner may do it, and the change must carry a numbered decision in
dev/PLAN.md section 3 (with the measured reason) plus an entry in
the threshold record. The report `_build/l3.32-t110-report.md`
carries every threshold's original argument.

Usage:
  check-dev-docs.py             run every gate subcheck (what make check runs)
  check-dev-docs.py --check NAME   run one gate subcheck
  check-dev-docs.py --list      list the gate subchecks
  check-dev-docs.py --sweep     on-demand informational sweep (exit 0)
Exit status: 0 clean, 1 defect found, 2 usage error.
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---- gate thresholds --------------------------------------------------------
# Raising one is a ruling, not an edit: see the procedure below.
# THE CADENCE, AND HOW A THRESHOLD IS RAISED. Both lived in dev/MAINTENANCE.md
# until 2026-08-06, when [L3.32-T115] measured that no brief had ever pointed an
# agent at that file: its enforcer is this script, so this docstring is its
# operative home and the prose copy was a second one that had already drifted
# (it said the green figure was 2,004 while the constant below said 1,784; the
# DOC was the correct one, which is worth remembering before assuming code
# outlives prose).
#
# CADENCE. The six subchecks run in `make check`, every commit, and are cheap
# pure-Python reads. The sweep is on-demand and informational, never gating.
#
# RAISING A THRESHOLD. A cap that anyone may raise silently is not a cap. To
# raise one: say what legitimate content does not fit, show the real row or file
# that needs the room, and record the new figure with that argument in the
# commit message. A threshold derived only from the last accident does not catch
# the next one, which is why these are argued from what a green artefact needs
# rather than from what the failure measured.
AGENTS_WORD_CAP = 2300   # raised from 2,200 by the owner 2026-08-10. WHAT DID
                         # NOT FIT: the controlled-style rule became AUDIENCE
                         # SPLIT that day (Chinese to the owner, ASD-STE100 to
                         # every other reader), so one rule block became two
                         # plus the boundary that a dispatched agent never
                         # writes Chinese. THE ROW THAT NEEDS THE ROOM: the
                         # "Always, write a controlled style" bullet in
                         # Boundaries. The file measured 2,199 against the
                         # 2,200 cap BEFORE that rule, so the headroom the cap
                         # was set with (it was 2,004 then) was already spent
                         # and no genuine new rule could land. The orchestrator
                         # first cut its own new text from 2,368 to 2,257; the
                         # residue is the irreducible cost of a second
                         # audience. The failed state was 3,450
PLAN_CELL_WORD_CAP = 1600  # largest cell is D28 at 572 words; the failed
                           # state was 12,634
PLAN_GOAL_ROW_CHAR_CAP = 1200  # the L3.32 target-form row is 1,001 chars, so
                               # 1,200 is that exemplar plus one legit edit;
                               # the failed state was 6,966 (L3.32-F5)

# ---- sweep-only lines -------------------------------------------------------
EPISODE_SCALE = 600   # largest ruling-class cell (D28) is 572; +5% margin

DATE = re.compile(r"\d{4}-\d{2}-\d{2}")
SECTION0 = re.compile(r"^## 0\. (.*)$", re.M)
PLAN_ROW = re.compile(r"^\| ([^|\n]*) \| (.*) \|\s*$", re.M)
MASTER_SECTION = re.compile(r"^## 11\.", re.M)
TASK_INDEX_SECTION = re.compile(r"^### Task index", re.M)
IMPORTED_MARK = re.compile(r"\bimported\s+(?:from|into)\b")
STATUS_HEADER = re.compile(r"\*\*STATUS:")
VERDICT = re.compile(r"\b(WRONG|REFUTED|SUPERSEDED|STANDING|PARTIAL|NOT BUILT)\b", re.I)
SCRIPT_REF = re.compile(r"scripts/[A-Za-z0-9_./-]+\.py")


def _load_sibling(modname: str, filename: str):
    """Load a sibling script as a module (the project's reuse pattern)."""
    spec = importlib.util.spec_from_file_location(
        modname, ROOT / "scripts" / filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_cri = _load_sibling("check_rule_ids", "check-rule-ids.py")
HEADING = _cri.HEADING  # the one canonical LESSONS-heading grammar


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def lessons_entries(text: str) -> list[tuple[str, str]]:
    """(id, full heading line) for every LESSONS entry."""
    out = []
    for line in text.splitlines():
        m = HEADING.search(line)
        if m:
            out.append((re.sub(r"\s+", " ", m.group(1)), line))
    return out


def routed_ids(rules_data: dict) -> set[str]:
    covered: set[str] = set()
    for b in rules_data.get("bundle", {}).values():
        covered |= set(b.get("ids", []))
    for ids in rules_data.get("triggers", {}).values():
        covered |= set(ids)
    return covered


def plan_rows(text: str) -> list[tuple[str, str]]:
    """(row id, cell body) for every table row. The body runs to the LAST pipe,
    so a `|` inside a cell never splits a row."""
    return [(m.group(1).strip(), m.group(2)) for m in PLAN_ROW.finditer(text)]


def goal_rows(plan_text: str) -> list[str]:
    """Whole-row text of every MASTER status table row (section 11, before the
    task index). These are the goal rows: a ruling, its authority, the current
    status, the gate and a pointer. The task index below the table has its own
    200-character cap, enforced by scripts/check-task-index.py.
    """
    m = MASTER_SECTION.search(plan_text)
    if not m:
        return []
    rest = plan_text[m.start():]
    end = TASK_INDEX_SECTION.search(rest)
    sec = rest[:end.start()] if end else rest
    return [ln for ln in sec.splitlines() if ln.startswith("| L")]


def section0_body(text: str) -> tuple[str | None, str]:
    """(heading date, body) for PLAN section 0. Heading date is None if the
    heading carries no YYYY-MM-DD."""
    m = SECTION0.search(text)
    if not m:
        return None, ""
    hd = DATE.search(m.group(1))
    nxt = re.search(r"^## [^0]", text[m.end():], re.M)
    body = text[m.end():m.end() + (nxt.start() if nxt else len(text) - m.end())]
    return (hd.group(0) if hd else None), body


def check_agents_size(agents_text: str) -> list[str]:
    n = len(agents_text.split())
    if n > AGENTS_WORD_CAP:
        return [f"AGENTS.md is {n:,} words, over the {AGENTS_WORD_CAP:,}-word cap. "
                f"The file loads into every session; slim it or raise the cap by "
                f"the recorded ruling procedure."]
    return []


def check_plan_cells(plan_text: str) -> list[str]:
    out = []
    for rid, body in plan_rows(plan_text):
        n = len(body.split())
        if n > PLAN_CELL_WORD_CAP:
            out.append(f"dev/PLAN.md row `{rid}` holds {n:,} words in one cell, "
                       f"over the {PLAN_CELL_WORD_CAP:,}-word cap. A cell is a "
                       f"ruling plus a pointer; episode content belongs in "
                       f"dev/JOURNAL.md.")
    for line in goal_rows(plan_text):
        length = len(line.rstrip())
        if length > PLAN_GOAL_ROW_CHAR_CAP:
            rid = line.split("|", 1)[1].split("|", 1)[0].strip()
            out.append(f"dev/PLAN.md goal row `{rid}` is {length:,} characters, "
                       f"over the {PLAN_GOAL_ROW_CHAR_CAP:,}-character cap. A "
                       f"goal row is a ruling plus a status pointer; episode "
                       f"content belongs in dev/JOURNAL.md.")
    return out


def check_imported_routing(lessons_text: str, rules_data: dict) -> list[str]:
    covered = routed_ids(rules_data)
    out = []
    for rid, heading in lessons_entries(lessons_text):
        # "imported from"/"imported into" marks an entry brought in whole from
        # outside. "imported names"/"imported operations" (R-34, R-38, C-21)
        # are code adjectives and are not the risk class; a first version
        # matched them and flagged C-21, which would have been a wolf.
        if not IMPORTED_MARK.search(heading.lower()):
            continue
        if rid not in covered:
            out.append(f"dev/LESSONS.md entry `{rid}` is marked imported and is "
                       f"not routed in dev/rules.toml (no bundle, no trigger). "
                       f"Imported content is the class that sat uncited for "
                       f"five days; route it or record why not.")
    return out


def check_section0_date(plan_text: str) -> list[str]:
    hd, body = section0_body(plan_text)
    if hd is None:
        if SECTION0.search(plan_text):
            msg = ("dev/PLAN.md section 0 heading carries no `(YYYY-MM-DD)` "
                   "date. The maintenance contract requires the 'where the "
                   "work stands' date in the heading.")
        else:
            msg = ("dev/PLAN.md has no `## 0.` section; the maintenance "
                   "contract requires the dated 'where the work stands' "
                   "section.")
        return [msg]
    body_dates = DATE.findall(body)
    newer = [d for d in body_dates if d > hd]
    if newer:
        return [f"dev/PLAN.md section 0 heading is dated {hd} but the section "
                f"describes work dated {max(newer)}. The 'as of' date must not "
                f"lag the work the section itself describes."]
    return []


def check_memo_status(memos_dir: Path) -> list[str]:
    out = []
    for p in sorted(memos_dir.glob("*.md")):
        lines = read(p).splitlines()
        start = next((i for i, l in enumerate(lines[:10]) if STATUS_HEADER.search(l)),
                     None)
        if start is None:
            continue  # no status header: form-when-present, see docstring
        block = [lines[start]]
        for l in lines[start + 1:]:
            if l.strip().startswith(">") or not l.strip():
                block.append(l)
            else:
                break
        if not VERDICT.search(" ".join(block)):
            out.append(f"dev/memos/{p.name}: the `**STATUS:` header does not "
                       f"state a verdict (STANDING, PARTIAL, SUPERSEDED, "
                       f"WRONG, REFUTED, NOT BUILT).")
    return out


def check_agents_enforcers(agents_text: str) -> list[str]:
    return [f"AGENTS.md names `{m.group(0)}`, which does not exist; the "
            f"enforcement-point table must name a real checker."
            for m in SCRIPT_REF.finditer(agents_text)
            if not (ROOT / m.group(0)).exists()]


GATE_CHECKS = {
    "agents-size": ("AGENTS.md", check_agents_size),
    "plan-cell-size": ("dev/PLAN.md", check_plan_cells),
    "lessons-imported-routing": ("dev/LESSONS.md", check_imported_routing),
    "plan-section0-date": ("dev/PLAN.md", check_section0_date),
    "memo-status-form": ("dev/memos/", check_memo_status),
    "agents-enforcers": ("AGENTS.md", check_agents_enforcers),
}


def run_gate(names: list[str]) -> int:
    agents_text = read(ROOT / "AGENTS.md")
    plan_text = read(ROOT / "dev" / "PLAN.md")
    lessons_text = read(ROOT / "dev" / "LESSONS.md")
    rules_data = tomllib.loads(read(ROOT / "dev" / "rules.toml"))
    findings: list[str] = []
    for name in names:
        target, fn = GATE_CHECKS[name]
        if name == "lessons-imported-routing":
            found = fn(lessons_text, rules_data)
        elif name == "memo-status-form":
            found = fn(ROOT / "dev" / "memos")
        else:
            found = fn(agents_text if target == "AGENTS.md" else plan_text)
        for f in found:
            findings.append(f"  DEFECT [{name}]: {f}")
    if not findings:
        print(f"check-dev-docs: clean ({len(names)} subcheck(s))")
        return 0
    print("\n".join(findings))
    print(f"\ncheck-dev-docs: {len(findings)} defect(s). The dev/ documents "
          f"decay; the gate exists so the decay is found here, not by accident.")
    return 1


def _cite_pattern(rid: str) -> str:
    """Match an ID as it is actually written, hyphen or not (`D-2` and `D2`
    are the same LESSONS entry in prose; PLAN decisions are the other D2)."""
    if rid.startswith("Rule "):
        return r"Rule\s+" + re.escape(rid.split()[1])
    if re.match(r"^[RTIDC]-\d+$", rid):
        return rid.replace("-", r"-?")
    return rid.replace("-", r"-")


def sweep_routing(lessons_text: str, rules_data: dict) -> list[str]:
    covered = routed_ids(rules_data)
    corpus = [ROOT / "AGENTS.md", ROOT / "CONTRIBUTING.md", ROOT / "README.md",
              ROOT / "Makefile", ROOT / "scripts" / "README.md"]
    corpus += sorted((ROOT / "dev").glob("*.md"))
    corpus += sorted((ROOT / "dev" / "memos").glob("*.md"))
    corpus += sorted((ROOT / "dev" / "literature").glob("*.md"))
    corpus += sorted((ROOT / "_build" / "briefs").glob("*.md"))
    corpus += sorted((ROOT / "_build").glob("*.md"))
    # The maintenance mechanism's own files are not independent awareness: a
    # sweep that listed an entry and then cited it in its own documentation
    # would clear entries by mentioning them. Everything else counts.
    own_files = {
                 ROOT / "_build" / "l3.32-t110-report.md"}
    corpus = [p for p in corpus if p.name != "LESSONS.md"
              and p not in own_files and p.exists()]
    texts = {p: read(p) for p in corpus}
    out = []
    for rid, _heading in lessons_entries(lessons_text):
        if rid in covered:
            continue
        pat = _cite_pattern(rid)
        if any(re.search(r"(?<![\w-])" + pat + r"(?![\w-])", t)
               for t in texts.values()):
            continue
        out.append(f"  {rid}: not routed in dev/rules.toml and cited nowhere "
                   f"in the corpus or any brief. This is the 'landed and "
                   f"nobody noticed' class; route it or record why not.")
    return out


def sweep_cells(plan_text: str) -> list[str]:
    m = re.search(r"^## 11\.", plan_text, re.M)
    if not m:
        return []
    sec = plan_text[m.start():]
    out = []
    for rid, body in plan_rows(sec):
        n = len(body.split())
        if n > EPISODE_SCALE:
            out.append(f"  {rid}: {n:,} words in the section 11 status cell, "
                       f"over the {EPISODE_SCALE}-word episode-scale line. "
                       f"Episode content belongs in dev/JOURNAL.md; a row "
                       f"should be a status and a pointer.")
    return out


def run_sweep() -> int:
    lessons_text = read(ROOT / "dev" / "LESSONS.md")
    plan_text = read(ROOT / "dev" / "PLAN.md")
    rules_data = tomllib.loads(read(ROOT / "dev" / "rules.toml"))
    unmentioned = sweep_routing(lessons_text, rules_data)
    cells = sweep_cells(plan_text)
    print("check-dev-docs sweep: unrouted AND uncited LESSONS entries")
    print("\n".join(unmentioned) if unmentioned else "  (none: every unrouted "
          "entry is cited somewhere in the corpus or a brief)")
    print()
    print("check-dev-docs sweep: section 11 cells over the episode-scale line")
    print("\n".join(cells) if cells else "  (none)")
    print()
    print(f"sweep: {len(unmentioned)} unmentioned entr(ies), "
          f"{len(cells)} episode-scale cell(s); informational, exit 0")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", nargs="?", const="all", metavar="NAME",
                    help="run one gate subcheck, or all (default)")
    ap.add_argument("--list", action="store_true", help="list the gate subchecks")
    ap.add_argument("--sweep", action="store_true",
                    help="on-demand informational sweep (exit 0)")
    args = ap.parse_args(argv[1:])

    if args.list:
        for name in GATE_CHECKS:
            print(name)
        return 0
    if args.sweep:
        return run_sweep()

    names = list(GATE_CHECKS) if args.check in (None, "all") else [args.check]
    bad = [n for n in names if n not in GATE_CHECKS]
    if bad:
        print(f"check-dev-docs: unknown subcheck(s): {', '.join(bad)}", file=sys.stderr)
        return 2
    return run_gate(names)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
