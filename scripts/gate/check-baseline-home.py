#!/usr/bin/env python3
"""DD24's bar figures have ONE home, and this gate holds them there.

THE TWO HOMES (DD24, amended by the owner 2026-08-16). The NUMBERS live in
`dev/ledger.toml` and nowhere else: the `[ratio]` table for the live figures
and the superseded records the ledger keeps beside them. The RULE lives in
`dev/PLAN.md`'s DD24 row, which states NO figure by design. The applied bar
is `ac_baseline_module_rate` times `tolerance`, computed at
`scripts/measure/check-ratio.py` and NOWHERE else.

WHY A GATE. The bar had four homes and it drifted: on 2026-08-13 a
recalibration moved it about 13 percent, it stayed moved for three days, and
`[LJ-1.364]` found it while ruling a different question. A rule no machine
enforces is a wish (DD19), and a one-time tidy that nothing enforces decays.
The sweep fixed today's restatements; this gate refuses the next one.

WHAT IT REFUSES. A guarded figure on a line outside `dev/ledger.toml` that
carries no historical marker. A guarded figure is any decimal of five or more
places below one that appears anywhere in `dev/ledger.toml`, plus the applied
bar and its whole-ledger ancestors: for every rate value in `[ratio]`, the
product of that rate and `tolerance`, rounded to six places. The set is
DERIVED at run time. Nothing here is hardcoded, because a checker that
hardcodes the numbers it guards carries the drift it prevents.

THE MARKER, so an author can comply without guessing. Put this on the line,
with the date the figure was TRUE:

    <figure> HISTORICAL(YYYY-MM-DD)

For example: a rate measured on 2026-08-13 keeps its figure and carries
`HISTORICAL(2026-08-13)` on the same line. A LIVE claim names the FIELD
instead: write `ac_baseline_module_rate` and `tolerance`, or `the [ratio]
table`, and no marker is needed because no figure appears. A test that pins
arithmetic READS the ledger and derives its fixture, or names the field in
its comment; `scripts/tests/test_ratio_noise.py` is the worked example.

WHAT IS FROZEN, and why an epoch is required. A gate that fails the whole
corpus teaches authors to paste. Frozen, reported and never failed:

  * every task directory at or below `LJ-1-367`, the birth code of this gate.
    A brief, a report and a run log are records written once, and a record is
    never rewritten (DD19). New task codes are gated.
  * `archive/` and `agents/tasks/archive/`, retired by structure.
  * the `EPOCH` set below: pre-gate lines in live files that this sweep had
    no write scope for. Do not add to this set. A new lapse is a defect.

WHAT IT DOES NOT CATCH, measured rather than guessed. Four-decimal roundings
are not guarded: `0.0136` is both a bar rounding and a true module rate in a
dated record (`scripts/measure/check-ratio.py:257`), so guarding it would
force markers on figures that are not the bar. Verdict multiples like `1.70x`
are not guarded: they are measurements against the bar, not the bar. Line
counts and second totals are not guarded: their staleness guard is
`validate_ratio_baseline`, which fails on a moved tree. And a figure that
appears NOWHERE in the ledger is not guarded at all; when a recalibration
lands, its figures enter the ledger and this set with them.

Run: `.venv/bin/python scripts/gate/check-baseline-home.py`
Wired into `make check` as the `baselinehome` target, 2026-08-16 (`[LJ-1.367]`).
"""

from __future__ import annotations

import re
import sys
import tomllib
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
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
LEDGER = ROOT / "dev" / "ledger.toml"

#: The marker an author puts on a line that keeps a historical figure. The
#: date names the day the figure was true, so the line says both what it was
#: and when it stopped being live.
MARKER = re.compile(r"HISTORICAL\(\d{4}-\d{2}-\d{2}\)")

#: A rate-scale figure: a decimal of five or more places below one. Line
#: counts, second totals and the tolerance sit outside this shape on purpose;
#: see WHAT IT DOES NOT CATCH.
FIGURE = re.compile(r"(?<![\d.])0\.\d{5,}(?!\d)")

#: The task code this gate was born at (`[LJ-1.367]`, 2026-08-16). A live
#: directory whose code is at or below this pair is a record already written;
#: nothing new may be added to it that this gate would forgive, because a
#: record is never rewritten. `LJ-1-368` and everything after is gated.
#: A second series, `LJ-2-*`, is gated from its first code.
BIRTH_TASK = (1, 367)

SKIP_DIRS = {".git", "_build", ".venv", "__pycache__", "node_modules", ".claude"}
SKIP_PREFIXES = ("archive", str(Path("agents") / "tasks" / "archive"))

# `.claude` is TOOL STATE, not project prose, and it is skipped on purpose.
# It holds the dispatch harness's session logs: hundreds of machine-written
# transcripts, each an echo of a brief or a return whose SOURCE is a document
# in `agents/tasks/`, gated above. A marker demanded in a log nobody authors
# teaches pasting, not compliance. The residual is stated: a figure that
# reached only tool state and no project document escapes this gate, and its
# source document is where the gate catches it.

#: THE EPOCH, and every entry is a line this gate had no write scope for when
#: it was born (2026-08-16, [LJ-1.367]). The entries are whole line texts, so
#: they cannot drift with line numbers and they die the moment their line is
#: edited. Do not add to this set. A new lapse is a defect, and that is the
#: point of the epoch. One entry is a LIVE claim, dev/PLAN.md:502, quoting a
#: superseded baseline as the bar of today: the owner was told 2026-08-16 and
#: the entry exists only until the paragraph names the field instead.
#:
#: ONE ENTRY WAS RE-QUOTED, NOT ADDED, on 2026-08-16: the DD26 row. An
#: unrelated repair rewrote `scripts/ledger.py` to `scripts/measure/ledger.py`
#: inside it, eight characters, and the entry fell out of this set and the gate
#: went red on a figure nobody had touched. That is the stated design working
#: as written, and it has a cost worth knowing: ANY edit to a frozen line, for
#: any reason, re-opens the whole line. Re-quote it and say why; do not widen
#: the match.
EPOCH = frozenset({
    # dev/JOURNAL.md:184
    'on the caliber the target was set with. Ratio **0.007913** s per line, plus',
    # dev/JOURNAL.md:185
    "2.85 percent, inside DD24's 1.15 bar of 0.008847. Tree green, every gate",
    # dev/PLAN.md:502
    'in-fence lines. The delivered AC wing measures **0.007913 s/line**, from a',
    # dev/PLAN.md:615
    "| DD26 | **THE CATALOGS ARE NOT COUNTED. `src/Everything.lagda.md` and `src/Landmarks.lagda.md` are excluded from EVERY size figure, past and future.** | **Ruled 2026-08-10 by the owner.** Both are indexes rather than mathematics: one is the import catalog with its per-chapter prose, the other states the two trophies and imports what proves them. **The reason is DRIFT, and it is the owner's:** a catalog GROWS WITH THE PROJECT, so a threshold measured against a total containing one drifts further from the mathematics it is meant to bound, and drifts in the direction that flatters the tree. **RETROSPECTIVE, by the owner's word:** the ruling re-bases figures already recorded, so `[LJ-0.4]`'s prerequisite is met at 16,897 rather than 16,995 and DD24's baseline is 0.007913 over 16,897 rather than 0.007904 over 16,916. **DD8's caliber is untouched:** non-blank lines inside ` ```agda ` fences, still. This ruling says which FILES that caliber runs over. **Enforced by `scripts/measure/ledger.py`'s `UNCOUNTED` and `countable_masters()`**, which every size site now calls, and pinned by `scripts/tests/test_ratio_baseline.py` and `test_deletion_test.py`, whose assertion that Everything IS counted was flipped in the same commit. **The two-numbers discrepancy this ruling collapsed lives in `dev/JOURNAL.md`, 2026-08-14, under `DD26`.** |",
    # dev/PLAN.md:873
    '| LJ-0.5 | RE-MEASURE the DD24 baseline | DONE: 0.007913 over 16,897 | Three cold Landmarks runs, spread 2.15 s, +2.85% and inside the 1.15 bar. Caught a confound: make typecheck builds the wing too |',
    # dev/PLAN.md:970
    '| LJ-1.70-A | Orchestrator audit: I conflated two multiples | CORRECTED | check-ratio prints x the BASELINE 0.011057, not x the bar 0.012716. My 1.28x and 1.39x were baseline multiples |',
    # dev/PLAN.md:1047
    '| LJ-1.135 | Re-measure ac_baseline_module_rate | 0.014367, UP 29.9 PERCENT | The sign was opposite to the brief: the bar gets LOOSER. Control run says 6.9 percent machine, 21.6 percent content |',
    # dev/PLAN.md:1273
    "| LJ-1.265 | Align DD24's bar: three rates are in force | 0.010514 IS LIVE. THE GAP IS 60.0 s | 0.013193 is STALE and the budget with it. check-ratio.py:462-464 settles it in code, not comment |",
    # scripts/measure/ledger.py:272
    '    # denominator excluded them: the ratio read 0.007999 against a true',
    # scripts/measure/ledger.py:273
    '    # 0.007904, inflating the rise by 1.2 percentage points. Unlike compared',
    # scripts/tests/test_ratio_baseline.py:5
    'and got two ratios: 0.007999 through `make typecheck`, which builds',
    # scripts/tests/test_ratio_baseline.py:6
    '`src/Everything.lagda.md` and therefore the GCH wing too, and 0.007904 through',
})


def guarded_figures() -> set[str]:
    """Every rate-scale figure the ledger names, live or superseded.

    The ledger is the home, so the whole file is read: the `[ratio]` table
    holds the live figures, and the superseded records the table keeps sit in
    its comments, its provenance string and earlier sections (the 0.013193
    bar lives above `[ratio]`, which is why the slice would be too narrow).
    The applied bar and every rate's tolerance product are derived, so a bar
    stated before anybody writes it into a comment is still caught.
    """
    figures = set(FIGURE.findall(LEDGER.read_text(encoding="utf-8")))
    with open(LEDGER, "rb") as handle:
        ratio = tomllib.load(handle).get("ratio", {})
    tolerance = ratio.get("tolerance")
    if isinstance(tolerance, (int, float)) and not isinstance(tolerance, bool):
        for value in ratio.values():
            if isinstance(value, float) and 0 < value < 1:
                figures.add(f"{round(value * tolerance, 6):.6f}")
    return figures


def frozen_task(rel: Path) -> bool:
    """A live task directory written before this gate was born."""
    parts = rel.parts
    if len(parts) < 2 or parts[0] != "agents" or parts[1] != "tasks":
        return False
    code = parts[2] if len(parts) > 2 else ""
    m = re.fullmatch(r"LJ-(\d+)-(\d+)", code)
    if not m:
        return False
    return (int(m.group(1)), int(m.group(2))) <= BIRTH_TASK


def corpus() -> list[Path]:
    """Every text file the gate reads, from the working tree and not git.

    Untracked files are scanned too, so a new brief is gated before its first
    commit rather than after. `.claude` is skipped as tool state; see the
    comment at SKIP_DIRS. This file itself is skipped: its `EPOCH` set
    quotes the frozen lines verbatim, so it cannot pass its own rule.
    """
    self_path = Path(__file__).resolve()
    out = []
    for p in sorted(ROOT.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT)
        if rel.parts[0] in SKIP_DIRS or any(d in rel.parts for d in SKIP_DIRS):
            continue
        if str(rel).startswith(SKIP_PREFIXES[0]) or str(rel).startswith(SKIP_PREFIXES[1]):
            continue
        if rel == LEDGER.relative_to(ROOT):
            continue
        if p.resolve() == self_path:
            continue
        if p.stat().st_size > 2_000_000:
            continue
        out.append(p)
    return out


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    figures = guarded_figures()
    patterns = [(f, re.compile(rf"(?<![\d.]){re.escape(f)}(?!\d)")) for f in figures]

    violations: list[str] = []
    frozen = 0
    for p in corpus():
        if frozen_task(p.relative_to(ROOT)):
            continue
        try:
            lines = p.read_text(encoding="utf-8").splitlines()
        except (UnicodeDecodeError, UnicodeError):
            continue
        for number, line in enumerate(lines, 1):
            hit = next((f for f, pat in patterns if pat.search(line)), None)
            if hit is None:
                continue
            if MARKER.search(line):
                continue
            if line in EPOCH:
                frozen += 1
                continue
            violations.append(f"{p.relative_to(ROOT)}:{number}: {hit}")

    if violations:
        print(f"check-baseline-home: {len(violations)} line(s) state a DD24 "
              f"figure with no home and no marker:", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        print("", file=sys.stderr)
        print("DD24's numbers live in dev/ledger.toml and nowhere else. A live "
              "claim names the FIELD (`ac_baseline_module_rate`, `tolerance`, "
              "the [ratio] table); a record keeps its figure and carries "
              "HISTORICAL(YYYY-MM-DD) on the line, naming the date the figure "
              "was true.", file=sys.stderr)
        return 1
    if not quiet:
        print(f"check-baseline-home: {len(figures)} ledger figure(s) guarded, "
              f"{frozen} frozen line(s) reported and not failed.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
