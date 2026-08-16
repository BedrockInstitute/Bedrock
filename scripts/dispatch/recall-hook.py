#!/usr/bin/env python3
"""Carry a gate's verdict to the moment of the decision, through a Claude Code hook.

WHY THIS EXISTS, and the diagnosis is the project's own. `dev/LESSONS.md`
**C-59** states the disease in one line: an enforcement point exists, and
nothing carries its verdict to a decision. `[LJ-1.376]`, the owner's audit,
ranked thirteen detour episodes and found the dominant class is the
ORCHESTRATOR'S OWN LIVE RECORD UNREAD, ahead of the archives and the
literature. `[LJ-1.377]` then built the gate for that class, and its own report
says where the gate cannot reach: it fires at the commit, and the brief was
written by an orchestrator that had already forgotten.

THE MISSING MOMENT IS BRIEF-WRITING TIME, and nothing in this repository can
reach it. MEASURED 2026-08-16 over `dev/ORCHESTRATION.md`: it carries ten
`*Enforcement:*` clauses and not one fires at the moment of the action; each
names either the orchestrator's own intention or a checker that runs at the
commit. A Claude Code hook is the one trigger in this toolchain that is
UNCONDITIONAL, so this file is the carrier and nothing more.

WHAT IT ADDS: nothing. No store, no index, no daemon, no port, no dependency.
Every fact it prints comes from a script already wired into `make check`.

WHAT IT REFUSES TO DO. It never blocks a tool call and it never fails a turn.
`[LJ-1.377]` MEASURED two wider designs at 274 firings out of 274 briefs and
killed both, on the finding that a gate which fires on everything trains
pasting. So this fires on a brief write and on a task dispatch, and is silent
otherwise.

EVENTS

    PostToolUse   Write or Edit under agents/tasks/<CODE>/, not a report
                  -> the LIVE RECORD duties this brief owes, the PREMISES the
                     gate already holds it to, the three sections dispatch.py
                     would refuse it for, and whether its `tier:` line agrees
                     with the switch in force

    PreToolUse    Task or Agent, when the prompt names a task code
                  -> the refusals that do NOT fire on the in-harness path.
                     `dev/ORCHESTRATION.md` section 1.1 records the hole and
                     `[LJ-1.11]` went out short two mandatory rules through it

    SessionStart  startup, resume, clear or compact, and never a subagent
                  -> the orchestrator card: the blocked rows and the open work
                     as an INDEX, the return checklist, and which cheap gates
                     are RED right now

THE CARD IS AN INDEX AND NEVER A SUMMARY, ruled by the owner 2026-08-16 after
he was shown both forms. A generated session card is the shape of the dashboard
he ABOLISHED on 2026-08-09 (commit `0b10503`) for a reason the repository does
not record, so the card states no claim of its own: a blocked row gets its
code, its line and its length, and the reader opens it. An open-work headline
is printed whole, because its author wrote it as a headline, and a wrapped one
is REASSEMBLED rather than cut.

THE FIRING LOG turns this tool's own value into a measurement instead of a
claim. Every firing appends one JSON line beside the dispatch registry, which
is owner-private, git-ignored, and survives `make clean`. After a week the
counts answer one question: how often does a firing change the brief before it
is dispatched?

CONTRACT, verified against the installed Claude Code 2.1.233:
    stdin  : one JSON object with hook_event_name, cwd, tool_name, tool_input
    stdout : {"hookSpecificOutput": {"hookEventName": ..,
                                     "additionalContext": ".."}}
    exit   : ALWAYS 0. A recall aid that can fail a turn is a gate, and the
             repository already has nineteen of those.

`additionalContext` reaches the model and is NOT shown in the terminal, so this
costs the owner no reading.

WIRING. The script is tracked here; the wiring is one file in `.claude/`, which
`.gitignore:30` keeps owner-private. That split is the same one `make hooks`
uses for the git hooks, and it answers the defect
`dev/memos/L3.32-context-layering.md` section 5 named against the last routing
proposal: its enforcement point sat in `.claude/` rather than in the tree.

    python3 scripts/dispatch/recall-hook.py --print-settings

prints the JSON to place at `.claude/settings.json`. Delete that file to turn
the whole mechanism off.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

CAP = 9500            # under Claude Code's 10,000-character cap
CHECKER_TIMEOUT = 8   # seconds; a slow recall aid is a broken one

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories. LJ-1.295: this script sits in a group directory, so the
# SCRIPTS root is found by walking up to `repo_root.py` itself.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

# THE LOG LIVES BESIDE THE DISPATCH REGISTRY, and not under `_build/`.
# `Makefile`'s `clean` target deletes everything in `_build/` except
# `literature/`, so a week-long measurement kept there is one routine command
# from destruction, which is the finding `dev/measurements/README.md` was
# written for. This directory is git-ignored, owner-private, and already holds
# `registry.json` and `returns.log`.
LOG = Path(os.environ.get(
    "BEDROCK_RECALL_LOG",
    ROOT / ".claude" / "skills" / "codex-dispatch" / ".state" / "recall-hook.jsonl"))

# The THREE sections `dispatch.py` refuses a brief without. They are
# unconditional on every brief whatever its kind, so their absence is signal
# rather than noise: MEASURED 2026-08-16, 278 of 340 live briefs carry ARCHIVE
# and LITERATURE, 269 carry DD4.
#
# PREMISES and LIVE RECORD are NOT here on purpose. Their gates fire on a
# trigger table, and 37 of 340 briefs carry PREMISES by design. Flagging those
# two unconditionally would fire on most briefs, which is the failure
# `[LJ-1.377]` measured at 274 of 274 and killed two designs for. Their own
# checkers speak for them below.
BRIEF_SECTIONS = {
    "DD4": r"^#+\s*.*\bDD4\b",
    "ARCHIVE": r"^#+\s*ARCHIVE\b",
    "LITERATURE": r"^#+\s*LITERATURE\b",
}

# A dispatch worth speaking to names a task, a directory or a rule. An
# ordinary search subagent does not, and stays silent.
TASK_SHAPED = re.compile(r"\bLJ-\d|\bagents/tasks/|\bDD\d|\bdev/LESSONS\.md")


def run(args: list[str]) -> tuple[int, str]:
    """Run a repository script and return (exit code, combined output)."""
    py = ROOT / ".venv" / "bin" / "python"
    try:
        proc = subprocess.run(
            [str(py) if py.is_file() else sys.executable, *args],
            cwd=str(ROOT), capture_output=True, text=True,
            timeout=CHECKER_TIMEOUT)
    except subprocess.TimeoutExpired:
        return 124, f"(timed out after {CHECKER_TIMEOUT}s: {' '.join(args)})"
    except OSError as exc:
        return 125, f"({exc})"
    return proc.returncode, (proc.stdout + proc.stderr).strip()


def is_brief(path: Path) -> bool:
    """agents/tasks/<CODE>/<file>.md, never a report, never the archive."""
    try:
        rel = path.resolve().relative_to(ROOT)
    except ValueError:
        return False
    parts = rel.parts
    if len(parts) != 4 or parts[0] != "agents" or parts[1] != "tasks":
        return False
    if parts[2] == "archive":
        return False
    return rel.suffix == ".md" and "report" not in rel.name.lower()


def missing_sections(text: str) -> list[str]:
    return [name for name, pat in BRIEF_SECTIONS.items()
            if not re.search(pat, text, re.M | re.I)]


def kind_from_brief(text: str) -> str:
    """Derive the rule bundle from the write scope, never from a self-declared
    kind. `dev/rules.toml`:34-35 states the reason: an author who picks the
    kind picks the bundle ([T105])."""
    scope = re.search(r"^#*\s*SCOPE \(write\)(.*?)(?=^#|\Z)", text, re.M | re.S)
    body = scope.group(1) if scope else text
    src = [p for p in re.findall(r"[\w./-]+\.(?:lagda\.md|agda|md|py)", body)
           if p.startswith("src/")]
    if not src:
        return "recon"
    return "probe" if all("Probe" in p for p in src) else "build"


def tier_findings(brief: Path) -> list[str]:
    """Does the brief's `tier:` line agree with the switch in force?

    THE RULE HAS ONE HOME AND THIS IS NOT IT. `check-dispatch-policy.py` owns
    the question and this calls it, because DD19 forbids a rule that is
    canonical twice and `dev/ORCHESTRATION.md` records that a restated table is
    a table that will drift.

    WHY IT IS WORTH THE CALL. That checker runs at the commit. On 2026-08-16
    it caught `LJ-1.385` carrying `tier: pi` on an ADVERSARIAL review, where
    the switch gives opus, so DD25's invariant that the critic is never the
    author was already broken by the time anybody read the exit code.
    """
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "_cdp", ROOT / "scripts" / "dispatch" / "check-dispatch-policy.py")
        cdp = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cdp)
        import dispatch_policy as dp
        defects, _notes = cdp.check_briefs(dp.VERSION_IN_FORCE, [brief])
        return defects
    except Exception as exc:                     # never break a turn
        return [f"(tier check unavailable: {exc})"]


def clip(sections: list[tuple[str, list[str]]]) -> str:
    out: list[str] = []
    used = 0
    for title, body in sections:
        if not body:
            continue
        block = title + "\n" + "\n".join(body)
        if used + len(block) > CAP:
            out.append("[TRUNCATED at the hook's character cap. "
                       "Run the named commands for the rest.]")
            break
        out.append(block)
        used += len(block) + 2
    return "\n\n".join(out)


def log_firing(event: str, subject: str, duties: dict) -> None:
    """One JSON line per firing. THIS IS THE PRICE, NOT THE CURE.

    The recall audit put the recoverable detour spend at about 2 dispatch
    equivalents of a measured 8, which is about 0.7 percent of dispatch spend,
    and said plainly that the figure is a hypothesis carried from a gate that
    fires at a different moment (P-l: a measured cure does not transfer by
    analogy). These lines are what turn it into a price. Count later: how many
    firings were followed by an edit to the same brief before its dispatch.
    """
    try:
        LOG.parent.mkdir(parents=True, exist_ok=True)
        with LOG.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps({"event": event, "subject": subject,
                                 **duties}, ensure_ascii=False) + "\n")
    except OSError:
        pass                                     # a log is never worth a turn


def on_brief_written(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    rel = path.resolve().relative_to(ROOT)
    kind = kind_from_brief(text)
    sections: list[tuple[str, list[str]]] = []
    duties = {"kind": kind}

    sections.append((f"BEDROCK BRIEF-TIME RECALL ({rel.parts[2]})",
                     [f"  file: {rel}",
                      f"  kind DERIVED from the write scope: {kind}"]))

    gone = missing_sections(text)
    duties["missing_sections"] = gone
    if gone:
        sections.append((
            "SECTIONS THIS BRIEF DOES NOT CARRY. `dispatch.py` refuses a brief "
            "with no ARCHIVE and no LITERATURE section; `check-dd4-stated.py` "
            "gates DD4 at the commit:",
            [f"  MISSING: {', '.join(gone)}"]))

    tiers = tier_findings(path)
    duties["tier_defects"] = len(tiers)
    if tiers:
        sections.append((
            "THE `tier:` LINE CONTRADICTS THE SWITCH IN FORCE. DD25's "
            "invariant is that the critic is never the author:",
            [f"  {t}" for t in tiers[:4]]))

    code, out = run(["scripts/gate/check-live-record-claims.py",
                     "--brief", str(rel)])
    gate_half = out.split("Adjacency read", 1)[0].strip() if out else ""
    # "no trigger, no duty" is the checker saying it has nothing to say. A
    # recall aid that reports its own silence is noise, and noise is what
    # trains pasting.
    if "no trigger, no duty" in gate_half:
        gate_half = ""
    duties["live_record_duties"] = gate_half.count("\n    - ") or (
        1 if "duties a gate would hold" in gate_half else 0)
    if gate_half:
        sections.append((
            "THE LIVE RECORD THIS BRIEF IMPLICATES ([LJ-1.377]). Answer each "
            "in a `## LIVE RECORD` section, quoted or declined in writing:",
            ["  " + l for l in gate_half.split("\n")[:14]]))

    # The premises gate has no per-file mode, so run it over the tree (0.33 s
    # MEASURED) and keep only the lines about THIS brief.
    _, prem = run(["scripts/gate/check-premises-stated.py", "--quiet"])
    mine = [l.strip() for l in prem.split("\n") if str(rel) in l]
    duties["premises_defects"] = len(mine)
    if mine:
        sections.append((
            "THE PREMISES GATE ALREADY HOLDS THIS BRIEF ([LJ-1.212]). Declare "
            "each premise in a `## PREMISES` section with a basis at "
            "`file:line`:", ["  " + l for l in mine[:6]]))

    # THE OPEN-WORK LIST IS DELIVERED, NEVER MATCHED. `dev/JOURNAL.md`
    # 1026-1029 ruled the cross-read on CONTENT, because "Step 6" and "the leaf
    # supply" name one object and share no word, so no token matcher can link
    # them. A reader can. The model IS the matcher; it only needs the text.
    if "open work item" not in gate_half:
        sections.append((
            "THE OPEN-WORK LIST, delivered rather than matched. Read these "
            "against what this brief asks:", open_work()))

    sections.append((
        f"THE MANDATORY BUNDLE for kind `{kind}`. Never select rules from "
        "memory (dev/ORCHESTRATION.md section 3):",
        [f"  .venv/bin/python scripts/dispatch/rules.py --for {kind}"]))

    log_firing("brief", str(rel), duties)
    return clip(sections)


def open_work() -> list[str]:
    """The open-work items of dev/PLAN.md section 0.0, as an INDEX.

    A HEADLINE IS PRINTED ONLY WHEN ITS AUTHOR FINISHED IT. `dev/PLAN.md`
    writes each item as `**N. HEADLINE**`, and some headlines run past the
    line. A headline that does not terminate is NOT continued here and NOT
    cut: the item gets its number and its line, and the reader opens it.

    WHY, and it is measured rather than fastidious. `dev/JOURNAL.md`:938-959
    records a four-word qualifier dropped in one hop, which turned a bounded
    claim into an unbounded one on this very screen. A card that truncates a
    claim manufactures that failure on a schedule.
    """
    out: list[str] = []
    lines = (ROOT / "dev" / "PLAN.md").read_text(encoding="utf-8").split("\n")
    for i, line in enumerate(lines[:700], 1):
        if not re.match(r"^\*\*\d+\. ", line):
            continue
        # THE HEADLINE IS THE BOLD SPAN THE AUTHOR CLOSED, not the rest of the
        # line. A first version read to end-of-line and called six of eight
        # headlines unfinished, because `dev/PLAN.md` continues the paragraph
        # on the same line after the closing `**`.
        #
        # A WRAPPED HEADLINE IS REASSEMBLED, NOT CUT. Four of the eight run
        # across two or three source lines, and joining them back to the
        # closing `**` reproduces exactly what the author wrote. That is
        # unwrapping, and it is the opposite of the truncation this card
        # refuses to do.
        num = re.match(r"^\*\*(\d+)\.", line).group(1)
        span = " ".join(l.strip() for l in lines[i - 1:i + 2])
        done = re.match(r"^\*\*(\d+)\. (.+?)\*\*", span)
        if done:
            head = re.sub(r"\s+", " ", re.sub(r"`", "", done.group(2))).strip()
            out.append(f"  PLAN:{i:<5} item {num}. {head}")
        else:
            out.append(f"  PLAN:{i:<5} item {num}. "
                       "(headline is not closed within three lines; read it there)")
    return out


def blocked_rows() -> list[str]:
    """The blocked-row table of section 0.0, as an INDEX and never a summary.

    THESE ROWS ARE NOT SUMMARISED, and that is the whole design of this
    section. MEASURED 2026-08-16: the three rows are 1,155, 806 and 527
    characters. A 150-character cut keeps 13, 19 and 28 percent of them, and
    what it drops first is the qualifier at the end of a clause. The code and
    the line are enough to open the row; a truncated claim is worse than no
    claim, because it reads as the claim.
    """
    out: list[str] = []
    text = (ROOT / "dev" / "PLAN.md").read_text(encoding="utf-8").split("\n")
    for i, line in enumerate(text[:520], 1):
        m = re.match(r"^\| (`\[LJ-[\d.]+\][^|]*) \| (.+) \|$", line)
        if m and "blocked on" not in line:
            code = re.sub(r"[`\[\]]", "", m.group(1)).strip()
            out.append(f"  PLAN:{i:<5} {code}  ({len(line)} characters, not summarised)")
        if len(out) >= 3:
            break
    return out


def return_checklist() -> list[str]:
    """The numbered steps of dev/ORCHESTRATION.md section 6, headline only.

    These ARE headlines by construction: the document writes each step as
    `N. **Verb the thing**.` and this prints the bold span, whole.
    """
    out: list[str] = []
    lines = (ROOT / "dev" / "ORCHESTRATION.md").read_text(
        encoding="utf-8").split("\n")
    inside = False
    for line in lines:
        if line.startswith("## 6. Handling a return"):
            inside = True
            continue
        if inside and line.startswith("## 7."):
            break
        m = re.match(r"^(\d+)\. \*\*(.+?)\.?\*\*", line)
        if inside and m:
            out.append(f"  {m.group(1)}. {m.group(2)}")
    return out


#: The cheap gates the card may run at session start. Each costs well under a
#: second. The slow ones are NAMED and not run, because a card that took ten
#: seconds would be a card somebody turns off.
CHEAP_GATES = [
    ("premises", "scripts/gate/check-premises-stated.py"),
    ("dd4", "scripts/gate/check-dd4-stated.py"),
    ("ruleids", "scripts/gate/check-rule-ids.py"),
    ("taskindex", "scripts/gate/check-task-index.py"),
    ("dispatchpolicy", "scripts/dispatch/check-dispatch-policy.py"),
]


def on_session_start() -> str:
    """The orchestrator card.

    WHAT IT IS FOR. `dev/ORCHESTRATION.md` is 5,952 words and is the
    orchestrator's own operating manual, and it loads at NO moment: `CLAUDE.md`
    imports `AGENTS.md` and nothing else. MEASURED 2026-08-16: about 2,694
    words reach a session unconditionally against 90,715 words of governing
    text, which is 3.0 percent, and none of the 3 percent is this file.

    IT IS AN INDEX, NOT A DASHBOARD, and the distinction is the owner's
    2026-08-09 abolition. Nothing here is stored, nothing is generated onto
    disk, nothing is a figure of its own: every line is a pointer with the
    line number to open. The card cannot become a proxy for the record,
    because it never states the record's claims.
    """
    sections: list[tuple[str, list[str]]] = []

    sections.append((
        "BEDROCK ORCHESTRATOR CARD, an INDEX and never a summary.",
        ["  Regenerated from dev/PLAN.md and dev/ORCHESTRATION.md at session "
         "start, so no figure here is recalled and no claim here is cut.",
         "  dev/ORCHESTRATION.md is 5,952 words and loads at no other moment."]))

    sections.append(("BLOCKED ROWS (dev/PLAN.md section 0.0). Open them; they "
                     "are not summarised here:", blocked_rows()))
    sections.append(("OPEN WORK, in dependency order. `dev/JOURNAL.md`"
                     ":1026-1029 rules the cross-read on CONTENT, not on a "
                     "name:", open_work()))
    sections.append(("AT EVERY RETURN, in this order (dev/ORCHESTRATION.md "
                     "section 6):", return_checklist()))

    red: list[str] = []
    for name, script in CHEAP_GATES:
        code, _ = run([script])
        if code != 0:
            red.append(f"  RED NOW: make {name}   ({script})")
    names = ", ".join(n for n, _ in CHEAP_GATES)
    sections.append((
        "GATE STATE, read now rather than assumed. C-59: a gate you do not run "
        "is worth what a gate you do not have is worth, and nothing warns you:",
        (red or [f"  green: {names}"]) +
        ["  NOT RUN here, each costing seconds to minutes: typecheck, lint, "
         "liveterritory, liverecord, dd18survey, tree, ledger. `make check` "
         "stays the gate before any commit."]))

    log_firing("session", "start", {"red_gates": len(red)})
    return clip(sections)


def on_in_harness_dispatch(prompt: str) -> str:
    """The hole `dev/ORCHESTRATION.md` section 1.1 names and cannot close.

    An in-harness dispatch passes through no tool, so `dispatch.py`'s refusals
    never fire, and `[LJ-1.11]` went out short two mandatory rules through
    exactly this gap. A PreToolUse hook on the subagent tool DOES fire there.

    THE SCOPE IS SMALLER THAN IT LOOKS TODAY, and the honest figure belongs
    here rather than in a summary. `dispatch_policy.py` pins
    `pi-subagent-mode`, whose default row runs through herdr, so only the
    ADVERSARIAL row is in-harness now. That row is DD25's, which is the
    highest-stakes dispatch this project makes.
    """
    if not TASK_SHAPED.search(prompt):
        return ""
    gone = missing_sections(prompt)
    log_firing("dispatch", "in-harness", {"missing_sections": gone})
    if not gone:
        return ""
    return clip([(
        "BEDROCK IN-HARNESS DISPATCH: THE REFUSALS DID NOT FIRE.\n"
        "`dispatch.py` refuses a brief with no ARCHIVE and no LITERATURE "
        "section, and this dispatch does not pass through it "
        "(dev/ORCHESTRATION.md section 1.1). Apply them by hand:",
        [f"  MISSING FROM THE PROMPT: {', '.join(gone)}",
         "  `[LJ-1.11]` went out short two mandatory rules through this gap."])])


SETTINGS = {
    "hooks": {
        "SessionStart": [{
            "matcher": "startup|resume|clear|compact",
            "hooks": [{"type": "command", "timeout": 20,
                       "command": "${CLAUDE_PROJECT_DIR}/.venv/bin/python "
                                  "${CLAUDE_PROJECT_DIR}/scripts/dispatch/"
                                  "recall-hook.py"}]}],
        "PostToolUse": [{
            "matcher": "Write|Edit|MultiEdit",
            "hooks": [{"type": "command", "timeout": 15,
                       "command": "${CLAUDE_PROJECT_DIR}/.venv/bin/python "
                                  "${CLAUDE_PROJECT_DIR}/scripts/dispatch/"
                                  "recall-hook.py"}]}],
        "PreToolUse": [{
            "matcher": "Task|Agent",
            "hooks": [{"type": "command", "timeout": 15,
                       "command": "${CLAUDE_PROJECT_DIR}/.venv/bin/python "
                                  "${CLAUDE_PROJECT_DIR}/scripts/dispatch/"
                                  "recall-hook.py"}]}],
    }
}


def emit(event: str, context: str) -> None:
    if context.strip():
        json.dump({"hookSpecificOutput": {"hookEventName": event,
                                          "additionalContext": context}},
                  sys.stdout)
    sys.exit(0)


def main() -> None:
    if "--print-settings" in sys.argv[1:]:
        print(json.dumps(SETTINGS, indent=2))
        sys.exit(0)
    if "--log" in sys.argv[1:]:
        if not LOG.is_file():
            print(f"recall-hook: no firings yet ({LOG})")
            sys.exit(0)
        rows = [json.loads(l) for l in LOG.read_text(encoding="utf-8").split("\n") if l.strip()]
        briefs = [r for r in rows if r.get("event") == "brief"]
        print(f"recall-hook: {len(rows)} firing(s), {len(briefs)} on a brief, "
              f"log at {LOG}")
        for key in ("missing_sections", "tier_defects", "premises_defects",
                    "live_record_duties"):
            hit = sum(1 for r in briefs if r.get(key))
            print(f"  {key:22s} fired on {hit} of {len(briefs)} brief writes")
        sys.exit(0)

    try:
        payload = json.load(sys.stdin)
    except Exception:
        sys.exit(0)

    event = payload.get("hook_event_name", "")
    # THE CWD TEST IS CONTAINMENT, NOT `find_root`. `repo_root.find_root`
    # takes a FILE and walks up from its parent, so handing it the repository
    # root directory makes it start one level above and RAISE, which killed
    # the first run of this hook before its own try block could catch it.
    cwd = Path(payload.get("cwd") or os.getcwd()).resolve()
    if cwd != ROOT and ROOT not in cwd.parents:
        sys.exit(0)

    tool = payload.get("tool_name", "")
    tin = payload.get("tool_input") or {}

    try:
        if event == "SessionStart":
            # THE CARD IS THE ORCHESTRATOR'S. A dispatched agent gets its rules
            # from its brief, and a second copy is DD19's canonical-twice
            # defect: two copies drift and a reader who finds one does not know
            # the other exists.
            if payload.get("agent_id") or payload.get("agent_type"):
                sys.exit(0)
            emit(event, on_session_start())
        if event == "PostToolUse" and tool in ("Write", "Edit", "MultiEdit"):
            fp = tin.get("file_path") or ""
            if fp and is_brief(Path(fp)):
                emit(event, on_brief_written(Path(fp)))
        if event == "PreToolUse" and tool in ("Task", "Agent"):
            emit(event, on_in_harness_dispatch(str(tin.get("prompt", ""))))
    except Exception as exc:                     # never break a turn
        json.dump({"hookSpecificOutput": {
            "hookEventName": event,
            "additionalContext": f"(bedrock recall hook error: {exc})"}},
            sys.stdout)
    sys.exit(0)


if __name__ == "__main__":
    main()
