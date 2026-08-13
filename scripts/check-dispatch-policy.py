#!/usr/bin/env python3
"""Check that briefs agree with the dispatch policy in force (PLAN DD17).

THE SWITCH IS `scripts/dispatch_policy.py`. This checker holds no policy of its
own: it imports the switch and derives every expectation from it. Change the
switch and this checker changes with it.

WHAT IT ENFORCES, and each line is a real gate:

  1. THE SWITCH IS SINGLE AND READABLE. `dispatch_policy.py` imports, and
     `VERSION_IN_FORCE` names a version the module defines.
  2. NOBODY RESTATES THE TABLE. A governed document (`dev/**`, `AGENTS.md`,
     `scripts/README.md`) that names a head's model must also point at the
     switch. The model string is the table's most distinctive token, so its
     presence is good evidence that a table was copied.
  3. EVERY BRIEF CARRIES A LEGAL `tier:` TOKEN. The token is the first word of
     the `tier:` line, and it must be one the policy knows.
  4. A POST-EPOCH BRIEF NAMES THE VERSION IT WAS CHOSEN UNDER. `tier: pi
     (override)` leaves a trace an audit can follow; `tier: pi` does not.
  5. AN ADVERSARIAL REVIEW USES THE CRITIC'S HEAD, not the author's. The two
     policy versions swap the default row and the adversarial row precisely so
     that the critic is never the author, so this check is what makes the swap
     mean something.

WHAT IT CANNOT DO, AND THE LIST IS NOT SHORT.

  * IT CANNOT VERIFY WHICH HEAD ACTUALLY RAN. A brief is a statement of
    intent. An in-harness Opus dispatch never passes through
    `.claude/skills/codex-dispatch/dispatch.py`, so nothing mechanical
    observes it at all. A brief that says `tier: pi` and was run on Opus 5
    passes this checker green. Only the audit catches that.
  * IT CANNOT DATE A BRIEF RELIABLY. This checker reads mtime, so an edited
    old brief looks new and a copied new brief can look old. The REASON for
    the limit changed on 2026-08-13, when the briefs moved from `_build/` to
    `agents/tasks/` and became tracked: git can now date them, so the limit
    is this checker's implementation and no longer a fact about the tree.
  * IT CANNOT TELL AN ADVERSARIAL REVIEW FROM A BRIEF THAT DISCUSSES ONE. The
    classifier reads the GOAL section and the tier line for the word
    "adversarial". A review whose GOAL avoids the word is invisible to it.
  * IT CANNOT JUDGE WHETHER THE CHOICE WAS RIGHT. Citation is not
    application, the same limit `[L3.32-T105]` established for rule IDs.

THE EPOCH, AND WHY THERE IS ONE. Checks 4 and 5 bind only briefs written on or
after POLICY_EPOCH, which is the hour the policy was codified. This is
`check-agents-guard.py`'s self-anchoring pattern: a brief from before the rule
existed is not judged by it, so the gate can be green from its first run
instead of carrying 400 legacy failures nobody will fix. A pre-epoch brief with
a defect is REPORTED as a note and never fails the gate.

USAGE
    python3 scripts/check-dispatch-policy.py            # the gate
    python3 scripts/check-dispatch-policy.py --notes    # also print the notes

Exit status: 0 clean, 1 defect found, 2 environment failure.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))

try:
    import dispatch_policy as P
except Exception as exc:                                   # pragma: no cover
    print(f"check-dispatch-policy: cannot import the switch: {exc}",
          file=sys.stderr)
    raise SystemExit(2)

# [LJ-1.142] merged the briefs into `agents/tasks/<TASK>/`. The DIRECTORY no longer says
# which file is a brief, so the predicate lives in `agents_tree` and every reader shares it.
import agents_tree as T

# The hour the policy was codified, by [LJ-1.127]. Briefs older than this
# predate checks 4 and 5 and are noted, never failed.
POLICY_EPOCH = _dt.datetime(2026, 8, 13, 11, 0, 0)

# Documents that must not carry a second copy of the table.
GOVERNED = ["AGENTS.md", "scripts/README.md"]
GOVERNED_GLOBS = ["dev/**/*.md"]

# The pointer a governed document must carry when it discusses the policy.
POINTER = "scripts/dispatch_policy.py"

TIER_RE = re.compile(r"^tier:\s*(.*)$", re.M | re.I)
# The head token is the first word, with markdown emphasis and punctuation
# stripped. `tier: **opus, max effort.**` reads as `opus`.
TOKEN_RE = re.compile(r"^[*_`\s]*([A-Za-z0-9][A-Za-z0-9-]*)")
# The version a brief was chosen under, anywhere on the tier line.
VERSION_RE = re.compile(r"\b(normal|override)\b", re.I)


def tier_line(text: str) -> str | None:
    m = TIER_RE.search(text)
    return m.group(1).strip() if m else None


def head_token(line: str) -> str | None:
    m = TOKEN_RE.match(line)
    return m.group(1).lower() if m else None


def goal_section(text: str) -> str:
    """The GOAL section, or the first 1200 characters when there is none."""
    m = re.search(r"^#+\s*GOAL\b(.*?)(?=^#+\s|\Z)", text, re.M | re.S | re.I)
    return m.group(1) if m else text[:1200]


def is_adversarial(text: str) -> bool:
    """True when the brief's own GOAL or tier line calls it an adversarial review.

    NARROWER THAN `dispatch.py`'s `brief_kind`, deliberately, and the two do
    different jobs. `brief_kind` scans the first 1200 characters, so a brief
    that merely CITES DD25 classifies as a review and gets the review rule
    bundle, which is harmless. Failing a gate on the same evidence is not
    harmless, so this reads only the two places where the author states what
    the task IS.
    """
    line = tier_line(text) or ""
    return ("adversarial" in line.lower()
            or "adversarial" in goal_section(text).lower())


def check_switch() -> list[str]:
    try:
        P.in_force()
    except SystemExit as exc:
        return [str(exc)]
    return []


def governed_files() -> list[Path]:
    out = [ROOT / p for p in GOVERNED]
    for g in GOVERNED_GLOBS:
        out += sorted(ROOT.glob(g))
    return [p for p in out if p.is_file()]


def check_single_source() -> list[str]:
    """No governed document restates the table.

    THE TEST IS THE MODEL STRING. A document that names `deepseek-v4-pro` is
    quoting a head, and a head belongs to the switch. Naming the switch beside
    it is enough: the reader is then one command away from the live table
    instead of reading a copy that drifted.
    """
    errors = []
    for path in governed_files():
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        if P.MODEL in text and POINTER not in text:
            errors.append(
                f"{path.relative_to(ROOT)}: names the head model "
                f"`{P.MODEL}` but does not point at `{POINTER}`. The two "
                f"policy tables have ONE home, and a table restated in a "
                f"second file is a table that will drift.")
    return errors


def check_briefs(version: str) -> tuple[list[str], list[str]]:
    """(errors, notes) over every brief."""
    errors: list[str] = []
    notes: list[str] = []
    if not T.TASKS.is_dir():
        return [f"no task tree at {T.TASKS}"], notes
    # candidate_briefs(), NOT briefs(): this check looks for a MISSING `tier:` line, and the
    # content predicate finds a brief partly BY that line. See `agents_tree`'s docstring.
    found = T.candidate_briefs()
    if not found:
        # C-40: a checker that reads nothing prints green. A layout change that
        # emptied this list would otherwise pass silently, which is how a census
        # drops to zero unnoticed.
        return [f"no brief found under {T.TASKS}: the census is ZERO"], notes
    legal = set(P.LEGAL_TOKENS)
    adversarial_ok = P.expected_tier_tokens("adversarial", version)
    for path in found:
        rel = path.relative_to(ROOT)
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            errors.append(f"{rel}: unreadable ({exc})")
            continue
        recent = (_dt.datetime.fromtimestamp(path.stat().st_mtime)
                  >= POLICY_EPOCH)
        # The retired route's records are never FAILED. They predate the policy, and the brief
        # predicate reads about 27 bare-stem archived reports as briefs (`agents_tree`), every
        # one of them under `archive/`. Judging them would fail the gate on a frozen record.
        sink = errors if (recent and not T.is_archived(path)) else notes
        line = tier_line(text)
        if line is None:
            sink.append(f"{rel}: no `tier:` line (ORCHESTRATION section 1)")
            continue
        token = head_token(line)
        if token not in legal:
            # A wrong token is a wrong HEAD, and that is worth failing on
            # whatever the brief's age, because the legal set has never
            # changed: opus, pi, codex and the emergency fable.
            errors.append(
                f"{rel}: `tier: {line[:48]}` names head {token!r}, which is "
                f"not one of {', '.join(sorted(legal))}")
            continue
        if recent and not VERSION_RE.search(line):
            errors.append(
                f"{rel}: `tier: {line[:48]}` does not name the policy version "
                f"it was chosen under. Write `tier: {token} ({version})`, so "
                f"a wrong choice leaves a trace an audit can find.")
        if is_adversarial(text) and token not in adversarial_ok:
            sink.append(
                f"{rel}: is an adversarial review and carries head {token!r}, "
                f"but under `{version}` the critic's head is "
                f"{P.tier_token('adversarial', version)!r} "
                f"(or {', '.join(sorted(adversarial_ok - {P.tier_token('adversarial', version)}))}). "
                f"{P.INVARIANT}")
    return errors, notes


def check_dispatch_reads_switch() -> list[str]:
    """`dispatch.py` must take its default harness FROM the switch.

    NOT A HARD GATE WHEN THE FILE IS ABSENT. `.claude/` is never committed, so
    a fresh clone has no dispatcher and a failure there would be a failure
    about nothing.
    """
    d = ROOT / ".claude" / "skills" / "codex-dispatch" / "dispatch.py"
    if not d.is_file():
        return []
    text = d.read_text(encoding="utf-8", errors="replace")
    if "dispatch_policy" not in text:
        return [f"{d.relative_to(ROOT)}: does not import the switch, so its "
                f"default harness is a second, drifting copy of the policy. "
                f"Import `dispatch_policy` and call `default_harness()`."]
    return []


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--notes", action="store_true",
                    help="also print the pre-epoch notes, which never fail")
    args = ap.parse_args()

    if errors := check_switch():
        for e in errors:
            print(f"FAIL: {e}")
        return 1
    version = P.in_force()

    errors = check_single_source() + check_dispatch_reads_switch()
    brief_errors, notes = check_briefs(version)
    errors += brief_errors

    for e in errors:
        print(f"FAIL: {e}")
    if args.notes:
        for n in notes:
            print(f"note: {n}")
    if errors:
        print(f"{len(errors)} defect(s) against the `{version}` policy")
        return 1
    print(f"dispatch policy OK: `{version}` in force, "
          f"{len(T.candidate_briefs())} brief(s) read, "
          f"{len(notes)} pre-epoch note(s) not judged "
          f"(run with --notes to see them)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
