#!/usr/bin/env python3
"""DD18 amended 2026-08-16: the RETURN gates, the BRIEF prints.

WHY THIS EXISTS, and it is measured rather than feared. `[LJ-1.358]` measured
that under DD18's one-honest-line clause the survey decay was LEGAL: one
bullet sat verbatim in 63 briefs, ten reports surveyed a 265-row index at its
first nine lines, and every gate stayed green, because a ritual line satisfies
the clause as written. The owner amended the row the same day in two
deliberately unequal parts, and `dev/PLAN.md`'s DD18 row is the ONE home of
the rule this checker serves:

- **B2, THE RETURN SIDE, GATES.** A return's ARCHIVE USED names every archive
  path its brief cited, TOOK or DECLINED, and quotes ONE line read per
  archived file. LITERATURE USED mirrors it when the brief's LITERATURE
  section cites `dev/literature/`.
- **B1, THE BRIEF SIDE, PRINTS AND NEVER GATES.** A brief's ARCHIVE section
  should name each of the four corpora, cited or declined, and a checker
  reports which briefs do not and shouts TEMPLATE when one bullet's reason
  text repeats verbatim across five briefs.

WHY THE TWO HALVES ARE UNEQUAL. B2 gates because its minimal compliant form
forces an ACT: the author must open the file to quote a line that exists at
the cited line number, and a pasted quote from another brief fails. B1 only
prints because its minimal compliant form is four pastable lines, MEASURED by
`[LJ-1.357]` at one keystroke of gaming cost, twice. A count that gates is
gamed the moment it gates, which is DD4's own ruling and the reason B1's
threshold of five briefs is allowed to exist at all: a count may PRINT.

WHAT B2 CHECKS, and each limit is a written one:

- The universe is the set of paths the BRIEF's ARCHIVE section cites under
  `archive/` or `dev/ARCHIVE.md`. `agents/tasks/archive/` is OUTSIDE the four
  corpora (`[LJ-1.357]`, the LJ-1-153 case), and a live `agents/tasks/` path
  is not compliance at all (`scripts/gate/check-archive-cited.py:26-27`).
- A path is ANSWERED when the report names it exactly, names a DEEPER path
  under it (the brief cites a directory, the report cites files inside it),
  or spells it by suffix (a decline written relative to a root). The prefix
  rule is ONE-WAY: a vaguer parent mention in the report answers nothing.
- A written DECLINE is compliance. "NOT read", a decline by suffix, and a
  cited-and-quoted file all pass, and they are three different honest acts.
- The three over-reaches `[LJ-1.357]` measured in the first design are
  avoided here: a missing LITERATURE USED heading is reported as its own
  defect kind and never as an unanswered path; a deeper path answers a
  shallower one; a decline's spelling is not punished.
- Per archived FILE the report names as read (a `path:line` citation under
  the corpora, no decline wording), at least one quoted phrase of twelve
  characters or more must occur at the cited line in that file. A quote found
  only in a window of three lines is a mis-cited line and fails, which is the
  letter of "at `file:line`" and the defect `[LJ-1.357]` found twice by hand.

WHAT THIS REFUSES TO CHECK, because a row claiming more than its checker
delivers is false safety:

- It cannot tell whether an archive BEARS on a task. Relevance stays review.
- It cannot judge the brief side. B1 prints, and its output is a visibility
  signal, not a verdict.
- It cannot tell a true line quoted without understanding from one read
  deeply. The quote duty forces the file to be opened, not understood.
- A quote from a `dev/literature/` file that no longer matches is COUNTED and
  never failed: those files are live and drift, while the four corpora are
  frozen, so only the frozen corpora give a decisive verdict.

THE EPOCHS, and a gate that fails the whole corpus teaches every author to
paste, so three boundaries are written here with their measured scale.

- PRE-EPOCH: every task before `LJ-1-359`. The amendment is dated 2026-08-16
  and those returns were written under the OLD clause. They are never failed.
  Measured scale at wiring: see `FROZEN_SCALE` below.
- SECOND EPOCH, `LJ-1-359` to `LJ-1-362`: dispatched after the ruling but
  BEFORE this checker existed. The row named `check-dd18-survey.py` while no
  such file was in the tree, which C-48 refuses to call enforcement, and
  their briefs ordered "naming ONE line read", not quoting it. The divergence
  is the orchestrator's, not those authors', and a record is never rewritten.
  Frozen the same way `check-premises-stated.py` froze its twenty-one.
- GATED: `LJ-1-363` on, the first task dispatched with this file in the tree.
  Its own report is the first this gate judges.

USAGE
    python3 scripts/gate/check-dd18-survey.py [--verbose]

Exit status: 0 clean or frozen-only findings, 1 a gated return failed,
2 environment failure. `--verbose` also lists which brief misses which corpus.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
import agents_tree  # noqa: E402
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
TASKS = ROOT / "agents" / "tasks"

#: The first task code this gate judges. LJ-1-363 is the first dispatch whose
#: brief quotes the amended row AND whose checker existed when it was written.
#: Everything at a lower code is a frozen record.
FIRST_GATED_CODE = 363

#: The first task code dispatched under the amended row. LJ-1-359 to LJ-1-362
#: are the SECOND EPOCH: post-ruling, pre-checker, frozen by C-59's rule that
#: a gate nobody could run is not a gate anybody failed.
SECOND_EPOCH_START = 359

#: MEASURED 2026-08-16 at wiring, over 259 completed brief-and-report pairs
#: (2 more are live and in progress), and written here per C-59 so the scale
#: survives outside a commit message. The naming half over the pre-amendment
#: corpus would fail 21 tasks: 14 with a genuinely unanswered citation (all
#: sampled flags read as real: LJ-1-178, LJ-1-195, LJ-1-198, LJ-1-200,
#: LJ-1-228 verified by hand) and 7 with no conditional LITERATURE USED
#: heading, which is exactly the residue [LJ-1.358] measured (LJ-1-103 to
#: LJ-1-132). The quote half, which did not exist before the ruling, was
#: also measured on the four second-epoch returns: 3 of the 3 completed ones
#: fail it (2 name lines without quoting, 1 quotes a table row with silent
#: cuts), because their briefs ordered "naming", not quoting.
FROZEN_SCALE = "21 naming-half tasks (14 unanswered, 7 no LITERATURE USED)"

SECTION = {
    "ARCHIVE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "ARCHIVE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "LITERATURE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "LITERATURE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
}

#: A DD18-scope citation: a path under `archive/` (the four corpora) or the
#: registry `dev/ARCHIVE.md`. The lookbehind refuses `agents/tasks/archive/`,
#: which `[LJ-1.357]` settled is OUTSIDE the corpora.
DD18_PATH = re.compile(r"(?<![\w/.-])(?:archive/[A-Za-z0-9./_-]+|dev/ARCHIVE\.md)")

#: The literature corpus.
LIT_PATH = re.compile(r"dev/literature/[A-Za-z0-9./_-]+")

#: A path:line citation inside a USED section, the form the quote duty binds.
CITE = re.compile(
    r"`?((?:archive|agents/tasks|dev)/[A-Za-z0-9./_+-]+?)`?"
    r"(?::(\d+)(?:-(\d+))?(?:,\d+)*)+")

#: Any file-shaped token, for declines spelled relative to a root.
BARE = re.compile(r"\b[A-Za-z0-9][A-Za-z0-9./_+-]*\.(?:md|toml|py|agda)\b")

#: A written decline. Suffix spellings, "NOT read" and "WHY NOT" prose are
#: compliance, never a defect (`[LJ-1.357]`, the LJ-1-168 case).
DECLINE = re.compile(
    r"(?i)\b(?:not\s+read|declin\w*|not\s+re-?opened|nothing\s+(?:in\s+it\s+)?bears|"
    r"not\s+used|not\s+surveyed|why\s+not)\b")

#: A quoted span worth verifying: 12 or more characters inside double quotes
#: (straight or curly), inside CJK corner quotes, or inside backticks, which
#: is how LJ-1-361 quotes a module line. Short spans match everywhere and
#: verify nothing, and a span with no space is a term mention, not a line.
QUOTE = re.compile(
    r'["\u201c]([^"\u201d]{12,})["\u201d]|'
    r"\u300c([^\u300d]{12,})\u300d|"
    r"`([^`]{12,})`")

#: A report still being written. C-22 orders a skeleton early, so a live
#: task's report carries this line and the gate waits for the return.
IN_PROGRESS = re.compile(r"(?im)^\**\s*status\s*:?\s*\**\s*in[\s-]?progress")

#: The four corpora, as B1 reads them in a brief's ARCHIVE section. CODE is
#: any archive path that is not one of the record indexes, PLUS `dev/ARCHIVE.md`,
#: which DD18 names inside the same corpus; the first design missed it and
#: `[LJ-1.357]` called that miss an over-reach.
CORPORA = {
    "CODE": re.compile(r"archive/(?!dev/)|dev/ARCHIVE\.md"),
    "TASKS": re.compile(r"TASKS-archived"),
    "JOURNAL": re.compile(r"JOURNAL-archived"),
    "DECISIONS": re.compile(r"DECISIONS-archived"),
}

#: Pre-move spellings. The live route's records lived under `_build/` before
#: `[LJ-1.142]` moved them. They are NOT one of the four corpora, but a brief
#: that cites them has surveyed, so B1 reports them beside a zero-of-four
#: score instead of letting it read as no survey at all.
PREMOVE = re.compile(r"_build/[A-Za-z0-9./_+-]+")

#: A path-shaped token, normalized away before template bullets are compared.
PATHISH = re.compile(
    r"(?<![\w/.-])(?:archive|agents/tasks|_build|dev|src|scripts)/[A-Za-z0-9./_+-]+")

#: The template threshold. It PRINTS, and the reason a count may print and
#: may not gate is DD4's own: a count is gamed the moment it gates.
TEMPLATE_THRESHOLD = 5

WINDOW = 3  # lines of slack before a quote is a mis-cited line


def code_of(path: Path) -> int:
    """The task's number, LJ-1-363 -> 363. Zero when the name carries none."""
    m = re.search(r"(\d+)$", path.name.split("-")[-1])
    return int(m.group(1)) if m else 0


def section_of(text: str, name: str) -> str:
    m = SECTION[name].search(text)
    return m.group(1) if m else ""


def brief_of(task: Path) -> Path | None:
    found = [p for p in sorted(task.glob("*.md"))
             if not p.name.endswith(".lagda.md") and agents_tree.is_brief(p)]
    return found[0] if found else None


def report_of(task: Path) -> Path | None:
    """The task's own return: the report named for the task, else the single
    report, else `REPORT.md`. A DD25 companion report is another dispatch's
    return and is not judged here."""
    exact = [p for p in task.glob("*.md")
             if p.stem.lower() == f"{task.name.lower()}-report"]
    if exact:
        return exact[0]
    rep = list(task.glob("REPORT.md"))
    if rep:
        return rep[0]
    found = [p for p in sorted(task.glob("*.md")) if agents_tree.is_report(p)]
    return found[0] if found else None


def normalize(s: str) -> str:
    s = re.sub(r"[*`_]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def resolve(rel: str) -> Path | None:
    p = ROOT / rel
    if p.is_file():
        return p
    # A spelling relative to the retired route's root, the LJ-1-168 form.
    cand = ROOT / "archive" / "src" / "2026-08-09-rud-route" / rel
    return cand if cand.is_file() else None


def answered(want: str, have: set[str]) -> bool:
    """Exact, deeper, or a relative spelling of the SAME file.

    The prefix rule is ONE-WAY: a report may answer a brief's directory by
    citing a file inside it, but a vaguer parent mention answers nothing.
    """
    w = want.rstrip("/")
    if want in have or w in have:
        return True
    for h in have:
        h = h.rstrip("/")
        if h.startswith(w + "/"):
            return True  # the report went deeper than the brief asked
        if h.endswith(w) or w.endswith(h):
            return True  # a decline spelled relative to a root
    return False


def bullets(sec: str) -> list[str]:
    """Bullets with whitespace collapsed only. Emphasis and backticks are
    kept, because a quote is EXTRACTED from the raw bullet and normalized
    only for comparison: stripping backticks first made LJ-1-361's
    backtick-quoted module line invisible to the very check it answers."""
    return [re.sub(r"\s+", " ", b).strip()
            for b in re.findall(r"(?:^|\n)\s*-\s+(.*?)(?=\n\s*-\s|\Z)", sec, re.S)]


def quote_fragments(q: str) -> list[str]:
    """A quote verifies when every fragment occurs in the cited range.
    Ellipsis, the CJK ellipsis, and the table-cell pipe are cut marks: a
    report that quotes two cells of a table row without naming the cells
    between them is using the row's own rendering convention, MEASURED on
    LJ-1-360's quote of TASKS-archived.md:171, not misquoting the file."""
    frags = [f for f in re.split(r"\.\.\.|\u2026|\|", q) if len(f) >= 6]
    return frags


def audit_quotes(sec: str) -> dict[str, dict]:
    """Per archived or literature FILE named in a USED section.

    Returns, per resolved file path: whether it was cited as read, declined
    in writing, or carries a quote verified at the cited line, plus the fail
    reasons of unverified quotes. A quote belongs to the NEAREST citation
    before it in the bullet, never to every citation in the bullet.
    """
    files: dict[str, dict] = {}
    for raw in bullets(sec):
        events = ([(m.start(), "cite", m) for m in CITE.finditer(raw)]
                  + [(m.start(), "quote", m) for m in QUOTE.finditer(raw)])
        events.sort(key=lambda e: e[0])
        current: re.Match | None = None
        pairs: list[tuple[re.Match, str]] = []
        for _, kind, m in events:
            if kind == "cite":
                current = m
            elif current is not None:
                g = next(g for g in m.groups() if g is not None)
                if " " in g:  # a phrase, not a term mention
                    pairs.append((current, normalize(g)))
        decline = bool(DECLINE.search(raw))
        cites = [m for _, k, m in events if k == "cite"]
        extra = [int(n) for n in re.findall(r"`?:(\d{1,4})\b`?", raw)]
        for m in cites:
            rel = m.group(1)
            # The quote duty binds DD18's files only: the four corpora, the
            # registry, and the literature corpus. A citation of a live
            # `src/` or `scripts/` file is evidence, and its truth stays
            # review; gating it would over-reach the row's words.
            if not (rel.startswith("archive/") or rel == "dev/ARCHIVE.md"
                    or rel.startswith("dev/literature/")):
                continue
            fp = resolve(rel)
            if fp is None:
                continue
            frozen = not rel.startswith("dev/literature/")
            rec = files.setdefault(str(fp.relative_to(ROOT)),
                                   {"read": False, "declined": False,
                                    "verified": False, "fails": [],
                                    "frozen": frozen})
            rec["read"] = True
            if decline:
                rec["declined"] = True
        for m, q in pairs:
            rel = m.group(1)
            fp = resolve(rel)
            if fp is None:
                continue
            key = str(fp.relative_to(ROOT))
            if key not in files:
                continue
            start = int(m.group(2))
            end = int(m.group(3) or m.group(2))
            body = fp.read_text(encoding="utf-8", errors="replace").splitlines()
            if start > len(body) or not (1 <= start):
                files[key]["fails"].append(f"{rel}:{start} cites past the file")
                continue
            extras = [n for n in extra if 1 <= n <= len(body)]

            def joined(a: int, b: int) -> str:
                return normalize(" ".join(body[max(0, a - 1):b]))
            exact = " \u00a7 ".join(joined(a, b)
                                    for a, b in [(start, end)] + [(n, n) for n in extras])
            near = " \u00a7 ".join(joined(max(1, a - WINDOW), b + WINDOW)
                                   for a, b in [(start, end)] + [(n, n) for n in extras])
            frags = quote_fragments(q)

            def hits(text: str) -> bool:
                return bool(frags) and all(
                    f.casefold() in text.casefold() for f in frags)

            if hits(exact):
                files[key]["verified"] = True
                files[key]["fails"] = []
            elif not files[key]["verified"]:
                if hits(near):
                    files[key]["fails"].append(
                        f"{rel}:{start} quotes a line off by a few lines")
                elif any(hits(joined(i, min(i + 40, len(body))))
                         for i in range(1, len(body), 20)):
                    files[key]["fails"].append(
                        f"{rel}:{start} is quoted from elsewhere in the file")
                else:
                    files[key]["fails"].append(
                        f"{rel}:{start} quotes text the file does not hold")
    return files


def b2_findings(brief: Path, report: Path, quote_duty: bool) -> tuple[list[str], list[str]]:
    """(defects, notes) for one task. A defect is (kind: detail)."""
    btext = brief.read_text(encoding="utf-8")
    rtext = report.read_text(encoding="utf-8")
    defects: list[str] = []
    notes: list[str] = []
    barch = section_of(btext, "ARCHIVE")
    if not barch.strip():
        return [], ["brief carries no ARCHIVE section: outside DD18's mechanism"]

    wants = {m.group(0).rstrip("./") for m in DD18_PATH.finditer(barch)}
    lit_sec = section_of(btext, "LITERATURE")
    lit_wants = {m.group(0).rstrip("./") for m in LIT_PATH.finditer(lit_sec)}
    have = ({m.group(0).rstrip("./") for m in DD18_PATH.finditer(rtext)}
            | {m.group(0).rstrip("./") for m in LIT_PATH.finditer(rtext)}
            | {t for t in BARE.findall(rtext) if len(t) > 8})

    if not SECTION["ARCHIVE USED"].search(rtext):
        defects.append("no-heading: the return carries no ARCHIVE USED section")
    for w in sorted(wants):
        if not answered(w, have):
            defects.append(f"unanswered: the return never names {w}")
    if lit_wants and not SECTION["LITERATURE USED"].search(rtext):
        defects.append("no-lit-heading: the brief cites dev/literature/ and the "
                       "return carries no LITERATURE USED section")
    elif lit_wants:
        # A missing heading is its own defect kind and already covers the
        # paths; unanswered is the separate duty, reported only when the
        # section exists and a cited path is still nowhere in the return.
        for w in sorted(lit_wants):
            if not answered(w, have):
                defects.append(f"unanswered: the return never names {w}")

    if quote_duty:
        for name in ("ARCHIVE USED", "LITERATURE USED"):
            sec = section_of(rtext, name)
            if not sec:
                continue
            for rel, rec in audit_quotes(sec).items():
                if rec["declined"]:
                    continue
                if rec["verified"]:
                    continue
                # A live literature file drifts, so a mismatch there is
                # counted and never failed; a missing quote is not drift.
                if rec["fails"] and not rec["frozen"]:
                    notes.append(f"quote mismatch on live file {rel}: "
                                 f"{rec['fails'][0]}")
                    continue
                if rec["fails"]:
                    defects.append(f"quote: {rec['fails'][0]}")
                elif rec["read"]:
                    defects.append(f"no-quote: {rel} is named as read with no "
                                   f"line quoted at a cited line")
    return defects, notes


def b1_findings() -> dict:
    """The brief side: corpora named or declined, and TEMPLATE clusters."""
    per_corpus: dict[str, list[str]] = {c: [] for c in CORPORA}
    none_of_four: list[str] = []
    premove: list[str] = []
    clusters: dict[str, set[str]] = {}
    for p in sorted(agents_tree.briefs(include_archive=False), key=code_of):
        sec = section_of(p.read_text(encoding="utf-8"), "ARCHIVE")
        if not sec.strip():
            none_of_four.append(p.parent.name)
            continue
        missing = [c for c, rx in CORPORA.items() if not rx.search(sec)]
        for c in missing:
            per_corpus[c].append(p.parent.name)
        if len(missing) == len(CORPORA):
            none_of_four.append(p.parent.name)
            if PREMOVE.search(sec):
                premove.append(p.parent.name)
        for b in bullets(sec):
            key = PATHISH.sub("<PATH>", normalize(b))
            clusters.setdefault(key, set()).add(p.parent.name)
    templates = {k: sorted(v) for k, v in clusters.items()
                 if len(v) >= TEMPLATE_THRESHOLD}
    return {"per_corpus": {c: sorted(set(v)) for c, v in per_corpus.items()},
            "none": none_of_four, "premove": premove, "templates": templates}


def main(argv: list[str]) -> int:
    verbose = "--verbose" in argv[1:]
    live_defects: list[tuple[str, list[str]]] = []
    frozen_rows: list[tuple[str, list[str]]] = []
    second_rows: list[tuple[str, list[str]]] = []
    live: list[str] = []
    checked = 0

    for d in agents_tree.task_dirs(include_archive=False):
        code = code_of(d)
        brief, report = brief_of(d), report_of(d)
        if brief is None or report is None:
            continue
        head = "\n".join(report.read_text(encoding="utf-8").splitlines()[:15])
        if IN_PROGRESS.search(head):
            live.append(d.name)
            continue
        defects, _ = b2_findings(brief, report, code >= FIRST_GATED_CODE)
        checked += 1
        if not defects:
            if code >= SECOND_EPOCH_START and code < FIRST_GATED_CODE:
                # The quote half is ALSO measured on the second epoch, frozen,
                # so the scale of what the checker's absence cost is visible.
                qd, _ = b2_findings(brief, report, True)
                if qd:
                    second_rows.append((d.name, qd))
            continue
        if code < SECOND_EPOCH_START:
            frozen_rows.append((d.name, defects))
        elif code < FIRST_GATED_CODE:
            second_rows.append((d.name, defects))
        else:
            live_defects.append((d.name, defects))

    gated = [d for d in agents_tree.task_dirs(include_archive=False)
             if code_of(d) >= FIRST_GATED_CODE and report_of(d) is not None]

    if live_defects:
        print(f"check-dd18-survey: {len(live_defects)} gated return(s) fail B2:",
              file=sys.stderr)
        for name, defects in live_defects:
            print(f"  {name}:", file=sys.stderr)
            for x in defects:
                print(f"    {x}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A return's ARCHIVE USED names every archive path its brief cited,",
              file=sys.stderr)
        print("took or declined, and quotes one line read per archived file: the",
              file=sys.stderr)
        print("quote must occur at the cited line in the cited file. A written",
              file=sys.stderr)
        print("decline is compliance. dev/PLAN.md DD18 is the rule's one home.",
              file=sys.stderr)
        return 1

    skip = f"; {len(live)} live report(s) in progress, not judged" if live else ""
    split = {k: sum(1 for _, ds in frozen_rows
                    if any(x.startswith(k) for x in ds))
             for k in ("unanswered", "no-heading", "no-lit-heading")}
    print(f"check-dd18-survey: B2 gate: {len(gated)} gated task(s) at or after "
          f"LJ-1-{FIRST_GATED_CODE}, 0 defects; frozen: {len(frozen_rows)} "
          f"pre-amendment task(s) ({split['unanswered']} unanswered, "
          f"{split['no-heading']} no ARCHIVE USED, {split['no-lit-heading']} "
          f"no LITERATURE USED) and {len(second_rows)} second-epoch task(s) "
          f"(LJ-1-359..362, dispatched before this checker existed){skip}")
    if verbose:
        for name, ds in frozen_rows + second_rows:
            print(f"  frozen {name}: " + "; ".join(ds))

    b1 = b1_findings()
    n_briefs = len(agents_tree.briefs(include_archive=False))
    miss = ", ".join(f"{c} by {len(v)}" for c, v in b1["per_corpus"].items())
    print(f"check-dd18-survey: B1 print, never a gate: {n_briefs} live brief(s); "
          f"corpora not named: {miss}; {len(b1['none'])} name none of the four, "
          f"of which {len(b1['premove'])} cite pre-move `_build/` paths")
    if b1["templates"]:
        print(f"  TEMPLATE, a bullet's reason text verbatim in "
              f"{TEMPLATE_THRESHOLD} or more briefs, {len(b1['templates'])} cluster(s):")
        for key, names in sorted(b1["templates"].items(), key=lambda kv: -len(kv[1])):
            print(f"    {len(names)} briefs: \"{key[:90]}\"")
            if verbose:
                print(f"      {', '.join(names)}")
    if verbose:
        for c, names in b1["per_corpus"].items():
            if names:
                print(f"  {c} not named by: {', '.join(names)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
