#!/usr/bin/env python3
"""The POD digest of section 8: Chinese, program-written, and every field sourced.

WHY THIS EXISTS, and the measured failure it answers. The owner reads one screen to
learn where the route stands. Before the POD a model wrote that screen, and a model
that writes a status screen writes the number it remembers. The design answers it with
one rule: **the program generates the digest, no model writes it and no model edits it,
every field names its source, and a field with no source is not in the digest**
(`dev/memos/LJ-4-pod-program-design.md:2841-2842`). `FIELD_SOURCES` below is that rule in
executable form, and `scripts/tests/test_pod_digest.py` reads it.

**NO SENTENCE HERE RANKS ANYTHING.** Ranking is a judgement AD1 forbids the program and
AD3 gives to the mathematician (`:2860-2862`). The digest prints the NEWEST `to: DONE`
line's task code and its matched row id, with no adjective. `RANKING_WORDS` is the
banned list and the suite asserts the rendered text holds none of them.

**NOTHING HERE TRIGGERS.** The two AD7 numbers and the twelve reported numbers report.
The rollback criterion is the owner's (`:2891`).

**THE DEFINITION TRAP, section 8.2.** `git log --numstat -- src/` counts every line of a
master, prose and both translations included, while the ledger counts non-blank lines
inside ```agda fences only. The two disagree on any commit that edits prose. THE DIGEST
USES THE LEDGER CALIBER, which is the orchestrator's pick and not an owner ruling, at
gap m2. Every size figure below comes from `scripts/measure/ledger.py`.

**ONE REPORT STATES ONE CALIBER, AND IT IS `at_head=True`.** The ledger reads HEAD by
default and takes a live view only when asked (`scripts/measure/ledger.py:145-150`). This
file called it BOTH ways: `standing()` read HEAD and the orphan line count read the
working tree, so one report carried two calibers and the orphan lines were not a subset
of the standing lines they are subtracted from. Every `count()` call below now passes
`at_head=True` in writing, and the rendered text NAMES the caliber. A15 splits the two
Agda heap calibers by SCOPE, per task against whole tree; a line caliber is not that
split, and a report may not mix one by accident.

**ONE MALFORMED ROW MAY NEVER KILL THE DIGEST.** The loop runs unattended, and the digest
is how the owner learns the loop stopped. A log row whose `used`, `attempt`, `seq` or
`standing` is not a number is therefore REFUSED AT ITS OWN ROW: the row enters no count,
the digest names it in section 四, and every other number still prints. `_as_int()`,
`_as_float()` and `_refuse()` are that rule, and the suite drives one malformed row per
reader.

EXIT STATUS, and each code means one thing:

    0   the digest printed. Refused rows are named inside it and do not change this.
    1   a real failure. The digest could not be built or could not be written, and the
        message names what it could not read.
    2   a usage error: an unknown option, a window of zero hours or less, or a `--root`
        that is not a directory.

THE FOUR SECTIONS AND THEIR SOURCES, section 8.1:

    一、今日结论      the transition log; `ledger.py`
    二、任务台账      the last transition per code
    三、报告数        the two AD7 numbers of 8.2, plus the twelve of 8.1
    四、阻塞与待裁决  the log's park lines; `dev/pod/queue.toml`; section 11's gaps

THREE PICKS THIS FILE MAKES, each disclosed because the design does not rule it.

  1. **Where the output goes.** `write_digest()` at `scripts/pod/pod.py:1787` runs this
     script under `capture_output=True`, so stdout alone reaches nobody. The digest
     prints to stdout AND writes `.pod-state/digest/<stamp>.txt` plus
     `.pod-state/digest/latest.txt`. `--no-write` suppresses the file half.
  2. **Where the standing series lives.** Section 8.2 says the digest RECORDS the
     standing figure once per day, so the second AD7 number is a lookup and never a
     re-derivation. The series is `.pod-state/standing.jsonl`, one row per local day.
     It is runtime state, so a fresh clone starts it empty, and until it holds two days
     the net-gain fields print `无更早记录` rather than a number.
     **Both runtime paths are DECLARED**, in `dev/build-manifest.toml` under
     `[[runtime_outside_build]]`. The series and the stamped digests are `evidence`,
     because re-running the digest rebuilds today alone and never an earlier day;
     `latest.txt` is `exhaust`. `.gitignore` keeps all three out of the index, and the
     manifest states when each may be deleted. `check-build-manifest.py` scans `_build/`
     only, so that section is enforced by review.
  3. **Full-width punctuation.** The worked example at `:2893-2929` writes half-width
     commas. The repository forbids half-width sentence punctuation in CJK prose, so the
     shape below is the example's and the punctuation is the repository's.

WHAT THIS MODULE DOES NOT DO. It never writes the table, never routes a task, never
commits and never starts Agda. It reads, it counts and it prints.
"""

from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import re
import sys
import time
import unicodedata
from pathlib import Path

# LJ-1.291 and LJ-1.295: the root is found by walking up to the repository marker, never
# by counting directories. The group directory joins sys.path for siblings imported by
# bare name, and the scripts root is found by walking up to `repo_root.py` itself.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

import agents_tree  # noqa: E402
import pod as pod_mod  # noqa: E402
import table as table_mod  # noqa: E402

ROOT = find_root(__file__)

#: The window the digest reports, section 8.1's cadence: the maintainer batch runs every
#: 12 hours or at 3 parked tasks, and the digest hangs off the same trigger. Each digest
#: PRINTS its window, so two overlapping windows are visible and never silent.
WINDOW_HOURS = 12.0

#: AD14's stop threshold. Rule (d) at `scripts/pod/pod.py:2109` stops the loop here.
PARK_STOP = 3

#: THE EIGHT PARK CLASSES OF SECTION 8.2, derived from `pod.PARK_REASONS` and never typed
#: a second time. `no-match` is the ninth reason and AD7's first number counts it alone,
#: so it is excluded here. A class is a CLASS: `preflight:P8` and `preflight:P19` are two
#: instances of `preflight`, and the count the digest labels `eight classes` is a count
#: over these eight names.
PARK_CLASSES = tuple(r.rstrip(":") for r in pod_mod.PARK_REASONS if r != "no-match")

#: The bucket for a park reason that matches none of the eight. It is reported on its own
#: line, so the label `eight classes` stays true of the eight.
PARK_UNLISTED = "unlisted"

#: Section 7.4 Part 1b's adopt trigger, printed as text and never evaluated here.
RETRIEVAL_TRIGGER = "两周内缺失率高于 20% 且缺失多数为零重叠"

#: The six states of section 5.2. The design names three of them in Chinese at
#: `dev/memos/LJ-4-pod-program-design.md:2907-2911`; the other three are rendered here.
STATE_ZH = {"READY": "就绪", "RUNNING": "运行中", "RETURNED": "已返回",
            "CHECKING": "验收中", "DONE": "完成", "PARKED": "停放"}

#: The park reasons whose cure is a brief repair, so section 四 names the author. AD3
#: gives the brief to the mathematician and section 6.7 makes the maintainer ASK.
BRIEF_REPAIR = ("preflight:", "no-change")

#: WORDS THE DIGEST MAY NEVER PRINT. Each one states a rank or a judgement, and AD1
#: forbids the program both. `最新` is NOT here: section 8.1 orders the newest done line
#: by name, which is an order in time and not a rank.
RANKING_WORDS = (
    "最好", "最差", "最佳", "最优", "最快", "最慢", "最强", "最弱", "最重要",
    "最高", "最低", "最多", "最少", "排名", "名列", "第一", "领先", "落后",
    "优于", "劣于", "更好", "更差", "较好", "较差", "优秀", "糟糕", "出色",
    "显著", "严重", "值得", "建议", "推荐", "应当", "应该", "表现", "成绩",
)

#: One Chinese noun phrase per section 11 gap that names an OWNER RULING. The parser
#: below reads the memo at run time, so an ID that leaves section 11 stops printing, and
#: an ID with no entry here prints its ID alone rather than an invented phrase.
GAP_ZH = {
    "M8": "维护者头位的模型与思考档位",
    "M10": "NO-GO 关闭是否只凭第 5 与第 6 合取",
    # M12 was here until 2026-08-18. Amendment A11 CLOSED it by building `_rule_g()`
    # REFILL, so it is no longer an open owner ruling and the digest must not
    # print it as one. The label went with the gap.
    "M13": "系统行的绝对秒数上限",
    "M14": "首次 NO-GO 的对抗评审触发行",
    "m2": "第二个报告数的行数口径",
}

#: EVERY FIELD NAMES ITS SOURCE, and this is the naming. Each value is
#: (path, line, needle): the file that produces the field, the line that produces it,
#: and a token that must sit at that line. `test_pod_digest.py` resolves all of them, so
#: a field whose source moves fails the suite instead of printing a stale number.
FIELD_SOURCES = {
    # 一、今日结论
    "finished": ("scripts/pod/pod.py", 2268, "CHECKING, DONE"),
    "dispatched": ("scripts/pod/pod.py", 2379, "READY, RUNNING"),
    "parked": ("scripts/pod/pod.py", 176, "PARK_REASONS"),
    "net_lines": ("scripts/measure/ledger.py", 145, "def count"),
    "newest_done": ("dev/memos/LJ-4-pod-program-design.md", 2940, "to: DONE"),
    # 二、任务台账
    "task_rows": ("scripts/pod/pod.py", 596, "def emit"),
    # 三、报告数, the two AD7 numbers
    "no_match_rate": ("dev/memos/LJ-4-pod-program-design.md", 2948, "no_match_rate"),
    "park_reasons_other": ("scripts/pod/pod.py", 176, "PARK_REASONS"),
    "days_since_gain": ("dev/memos/LJ-4-pod-program-design.md", 2958, "net gain"),
    "standing": ("scripts/measure/ledger.py", 133, "def countable_masters"),
    # 三、报告数, the twelve
    "shadowing": ("scripts/pod/table.py", 542, "def hits"),
    "expiry_fallout": ("scripts/pod/table.py", 719, "def expire_rows"),
    "dropped_returns": ("scripts/pod/pod.py", 2170, "no-change"),
    "orphan_masters": ("scripts/pod/check-closure.py", 94, "def imported_modules"),
    "telescope": ("scripts/measure/check-unbound-hyp.py", 118, "def hypotheses"),
    "vacuous_conjunct_4": ("scripts/pod/accept.py", 422, "unbound_vacuous"),
    "vacuous_conjunct_1": ("scripts/pod/accept.py", 422, "agda_vacuous"),
    "foreign_paths": ("scripts/pod/accept.py", 423, "changed_files_foreign"),
    "corpus_records": ("scripts/pod/pod.py", 512, "def corpus_append"),
    "outcomes": ("scripts/pod/table.py", 104, "outcome"),
    "retrieval_miss": ("scripts/pod/retrieve.py", 376, "def miss_signal"),
    "retrieval_zero_overlap": ("scripts/pod/retrieve.py", 394, "overlap"),
    # The line records a MEAN, so the paths of a dispatch whose mean is above 0 have no
    # per-path score anywhere. That same line is the source of the number that says so.
    "retrieval_undetermined": ("scripts/pod/retrieve.py", 394, "overlap"),
    # 四、阻塞与待裁决
    "blocked_parked": ("scripts/pod/pod.py", 176, "PARK_REASONS"),
    "queue_requests": ("scripts/pod/pod.py", 730, "def split_entry"),
    "owner_rulings": ("dev/memos/LJ-4-pod-program-design.md", 3422, "An owner ruling"),
    # THE ONE FIELD WHOSE SOURCE IS THIS FILE. A refused row is produced by the digest's
    # own readers, so `_refuse()` is its source and there is no other.
    "refused_rows": ("scripts/pod/digest.py", 279, "def _refuse"),
}

#: Section 二's column widths, in display columns, taken from the worked example at
#: `dev/memos/LJ-4-pod-program-design.md:2906-2911`.
COLS = (14, 10, 7, 26)


class DigestError(Exception):
    """The digest cannot read a source it names. It never prints a guessed number."""


# ---------------------------------------------------------------- small helpers


def _width(text: str) -> int:
    """The display width of one string. A CJK character occupies two columns."""
    return sum(2 if unicodedata.east_asian_width(c) in "WF" else 1 for c in text)


def _pad(text: str, cols: int) -> str:
    """One cell, padded to `cols` display columns, with one space at the minimum."""
    return text + " " * max(1, cols - _width(text))


def _wrap(text: str, width: int = 76, indent: str = "  ") -> list[str]:
    """One data-bearing line, folded at a display width, as the worked example folds it.

    A quoted value can be a path, an English reason or a pre-flight detail, and none of
    them is rewritten. The fold breaks at a space when the tail is one Latin word, and at
    a character boundary otherwise, because CJK text carries no spaces.
    """
    out, line = [], indent
    for char in text:
        if _width(line) + _width(char) > width and line.strip():
            cut = line.rstrip()
            if char.isascii() and not char.isspace() and " " in cut.strip():
                head, _, tail = cut.rpartition(" ")
                out.append(head)
                line = indent + tail
            else:
                out.append(cut)
                line = indent
        line += char
    if line.strip():
        out.append(line.rstrip())
    return out


def _rate(num: int, den: int) -> str:
    """`n/d = p%`, or `n/d，比率无定义` when the denominator is 0.

    A zero denominator has no rate. Printing `0%` there would state a measurement the
    evidence does not give, which the Chinese Tech Doc Style forbids.
    """
    if den <= 0:
        return f"{num}/{den}，比率无定义"
    return f"{num}/{den} = {100.0 * num / den:.1f}%"


def _hhmm(seconds: float | None) -> str:
    """Wall time as `H:MM`, the form of the worked example. `未知` when it has no clock."""
    if seconds is None:
        return "未知"
    seconds = max(0.0, float(seconds))
    return f"{int(seconds // 3600)}:{int(seconds % 3600) // 60:02d}"


def _num(value) -> str:
    """One count, or `未知` when its source could not be read. It never prints 0 for a
    number that was not measured: a silent 0 is the shape a broken source hides in."""
    return "未知" if value is None else f"{value:,}"


def _refuse(sink: list[str] | None, where: str, key: str, value) -> None:
    """Refuse ONE row and name it. It never raises and it never guesses a value.

    THE DIGEST IS HOW THE OWNER LEARNS THE LOOP STOPPED, so one malformed row must not
    take the other numbers with it. The refused row enters no count, and section 四 prints
    this line, so a silently dropped row is impossible.
    """
    if sink is None:
        return
    text = repr(value)
    if len(text) > 40:
        text = text[:39] + "…"
    sink.append(f"{where}：字段 {key} 的值 {text} 不可用，该行不计入任何数。")


def _as_int(value) -> int | None:
    """One integer from a log field, or None when the field does not hold one.

    `int("three")` raises and `int(None)` raises, and both shapes reached this file: the
    `used` field of a retrieval line, the `attempt` field of a transition, and the
    `standing` field of a daily row. A bool is REFUSED rather than counted as 0 or 1,
    because `true` in a count field is a malformed row and never the number one.
    """
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def _as_float(value) -> float | None:
    """One real number from a log field, or None when the field does not hold one."""
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _as_day(value) -> str | None:
    """One ISO-8601 calendar day, or None. `date.fromisoformat()` raises on anything
    else, and the standing series is a runtime file that a crash can tear."""
    if not isinstance(value, str):
        return None
    try:
        datetime.date.fromisoformat(value)
    except ValueError:
        return None
    return value


def park_class(reason: str) -> str:
    """The park CLASS of one park reason, from `pod.PARK_REASONS` and never a second list.

    Section 8.2 names EIGHT classes beside `no-match`, and four of them carry an instance:
    `preflight:P8` and `preflight:P19` are two instances of ONE class, and so are
    `attempt_max:<row id>`, `row:<row id>` and `stop_loop:<row id>`. A reason that matches
    no class returns `unlisted`, because a count labelled `eight classes` may not quietly
    hold a ninth.
    """
    for known in pod_mod.PARK_REASONS:
        if known.endswith(":"):
            if reason.startswith(known):
                return known[:-1]
        elif reason == known:
            return known
    return "unlisted"


def _local_day(epoch: float) -> str:
    """The LOCAL day of one epoch stamp. The log is UTC and the reader is not, so the
    header date and the standing series key follow the reader's clock."""
    return time.strftime("%Y-%m-%d", time.localtime(epoch))


_LOADED: dict[str, object] = {}


def _load(name: str, rel: str, root: Path):
    """One module whose file name holds a hyphen, so `import` cannot reach it.

    IT IS CACHED PER NAME, because two fields read the ledger and executing a module
    body twice in one digest buys nothing.
    """
    key = f"{name}@{root}"
    if key in _LOADED:
        return _LOADED[key]
    path = root / rel
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise DigestError(f"{rel}: not importable")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    _LOADED[key] = mod
    return mod


# ---------------------------------------------------------------- the log window


def in_window(lines: list[dict], t0: float, t1: float) -> list[dict]:
    """Every log line whose stamp sits inside [t0, t1). The window is epoch seconds, so
    the reader's time zone never enters the arithmetic."""
    out = []
    for line in lines:
        at = pod_mod._epoch(line.get("ts"))
        if at is not None and t0 <= at < t1:
            out.append(line)
    return out


def record_of(line: dict, root: Path):
    """The WHOLE acceptance record of one routed line, or None.

    THE LOG LINE CARRIES THREE PARTS OF THE RECORD and not all of it: `emit()` at
    `scripts/pod/pod.py:591` writes `facts`, `caliber` and `concurrency`. The vacuous
    flags and the foreign path list sit OUTSIDE `facts` (`scripts/pod/accept.py:422-423`)
    and survive in the run file, whose path the line carries as `run`
    (`scripts/pod/accept.py:437`). The last non-empty line of that file is the record.
    """
    rel = line.get("run")
    if not rel or not isinstance(rel, str):
        return None
    try:
        text = (root / rel).read_text(encoding="utf-8")
    except (OSError, ValueError):               # a missing file, or a path with a NUL
        return None
    for raw in reversed(text.split("\n")):
        if raw.strip().startswith("{"):
            try:
                return json.loads(raw)
            except json.JSONDecodeError:
                return None
    return None


def routable(line: dict) -> dict | None:
    """The routable half of one log line, in the shape `matches()` reads: `task`,
    `caliber` and `concurrency` at the top level and the six facts nested."""
    if "facts" not in line:
        return None
    return {"task": line.get("task") or "", "facts": line["facts"],
            "caliber": line.get("caliber"), "concurrency": line.get("concurrency")}


# ---------------------------------------------------------------- the table and corpus


def load_table(root: Path):
    """The rule table, or None when it cannot be read. A table-derived number then
    prints `未知`, because a field whose source is unreadable has no value."""
    try:
        return table_mod.load_table(root / "dev" / "pod" / "table.toml",
                                    table_mod.head_slots(root))
    except Exception:                          # a refusal, a missing file, a bad head
        return None


def corpus_records(root: Path) -> list[dict]:
    """Every record of `dev/pod/replay-corpus.jsonl`. A torn line is SKIPPED, exactly as
    `log_lines()` skips one: one bad tail write must not lose every record before it."""
    path = root / "dev" / "pod" / "replay-corpus.jsonl"
    out = []
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return out
    for raw in text.split("\n"):
        if not raw.strip():
            continue
        try:
            out.append(json.loads(raw))
        except json.JSONDecodeError:
            continue
    return out


def _hits(table, rec):
    """`table.hits()` with a guard. A malformed record routes nowhere and is not a crash:
    the digest reports, and a report that dies takes the other eleven numbers with it."""
    try:
        return table_mod.hits(table, rec)
    except (KeyError, TypeError, ValueError):
        return []


# ---------------------------------------------------------------- the two AD7 numbers


def no_match_rate(lines: list[dict]) -> tuple[int, int]:
    """AD7's first number: park lines with reason `no-match` over all return lines.

    Section 8.2 rules the numerator exactly. Rule (c) writes the string `no-match` on the
    ONE site that produces a no-match park (`scripts/pod/pod.py:2070`), so the numerator
    has a source. The other eight park reasons are counted separately by
    `park_reasons_other()`, because none of them is a gap in the table.
    """
    num = sum(1 for r in lines if r.get("reason") == "no-match")
    den = sum(1 for r in lines if r.get("to") == "RETURNED")
    return num, den


def park_reasons_other(lines: list[dict]) -> dict[str, int]:
    """The EIGHT other park CLASSES of section 8.2, counted apart from the no-match rate.

    `preflight:P<n>` is a malformed brief, `no-change` is a dead worker,
    `attempt_max:<row id>` is a row that cannot change its own facts, `r4` is a close the
    acceptance refused, `admission` is a table conflict R3 caught, `launch` is a launcher
    refusal, `row:<row id>` asked for the park, and `stop_loop:<row id>` is the stop.

    THE LABEL SAYS CLASSES, SO THE DATA IS CLASSES. This counted the raw reason string,
    which puts `preflight:P8` and `preflight:P19` in two buckets and makes a report of
    `eight classes` print eleven of them. `park_class()` collapses the four classes that
    carry an instance, and a reason section 8.2 does not name lands in `unlisted` rather
    than inflating the eight.
    """
    out: dict[str, int] = {}
    for r in lines:
        reason = r.get("reason")
        if not isinstance(reason, str) or reason == "no-match":
            continue
        if r.get("to") != "PARKED":
            continue
        key = park_class(reason)
        out[key] = out.get(key, 0) + 1
    return dict(sorted(out.items()))


def standing(root: Path) -> tuple[int, int]:
    """The standing figure and the master count, in the LEDGER caliber of section 8.2.

    It calls the same two functions `ledger.py --brief` prints from, so the digest and
    the one admissible source for a standing figure can never disagree:
    `countable_masters()` at `scripts/measure/ledger.py:133` and `count()` at `:145`.

    `at_head=True` IS WRITTEN AND NOT INHERITED. It is the ledger's default, and this
    report states one caliber, so the caliber is stated at every call site rather than
    read out of another module's default.
    """
    ledger = _load("pod_digest_ledger", "scripts/measure/ledger.py", root)
    files = ledger.countable_masters()
    return sum(ledger.count(f, at_head=True) for f in files), len(files)


def standing_path(root: Path) -> Path:
    return root / ".pod-state" / "standing.jsonl"


def standing_series(root: Path, refused: list[str] | None = None) -> list[dict]:
    """The recorded standing series, oldest day first, ONE row per day.

    EVERY ROW IS VALIDATED HERE, so the two readers below can compare and subtract.
    `days_since_gain()` compares two standings and `net_gain()` subtracts one, and both
    raise `TypeError` the moment a row carries `"standing": null` or a string. The file
    is runtime state that a crash can tear, and a torn row must cost its own row and
    nothing more. A row with no calendar day, or a standing that is not an integer, is
    refused and named.
    """
    out: dict[str, dict] = {}
    try:
        text = standing_path(root).read_text(encoding="utf-8")
    except OSError:
        return []
    for n, raw in enumerate(text.split("\n"), 1):
        if not raw.strip():
            continue
        try:
            row = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(row, dict):
            continue
        where = f"每日行数记录 第 {n} 行"
        day = _as_day(row.get("day"))
        if day is None:
            _refuse(refused, where, "day", row.get("day"))
            continue
        lines = _as_int(row.get("standing"))
        if lines is None:
            _refuse(refused, where, "standing", row.get("standing"))
            continue
        out[day] = dict(row, day=day, standing=lines)   # the newest row of a day wins
    return [out[d] for d in sorted(out)]


def record_standing(root: Path, day: str, lines: int, masters: int) -> None:
    """Record the standing figure ONCE PER DAY, so AD7's second number is a lookup.

    Section 8.2 rules the lookup, not the re-derivation: `git log --numstat` and the
    ledger disagree on any commit that edits prose, so a number derived twice by two
    calibers is two numbers. The file is append only and the reader takes the last row
    of each day, so a second digest in one day corrects the first and loses nothing.
    """
    path = standing_path(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    row = {"day": day, "standing": lines, "masters": masters,
           "recorded": datetime.datetime.now(datetime.timezone.utc)
           .strftime("%Y-%m-%dT%H:%M:%SZ")}
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def days_since_gain(series: list[dict], today: str) -> tuple[int | None, str | None]:
    """AD7's second number: days since `src/` last had a net gain, and the gain day.

    `gain_day` is the NEWEST day whose standing exceeded the day before it. It returns
    (None, None) while the series holds fewer than two days, because a first row has no
    day before it and a gain cannot be established from one measurement.

    IT READS EVERY ROW THROUGH THE TWO COERCIONS AND NEVER TRUSTS ITS CALLER. `>` between
    an int and a `None` raises `TypeError`, and this function is reached from the digest,
    from the tests and from `maintainer_inputs()`. A row that carries no comparable
    standing takes part in no comparison, so a torn row costs its own row alone.
    """
    gain = None
    pairs = [(_as_day(r.get("day")), _as_int(r.get("standing"))) for r in series]
    pairs = [(d, n) for d, n in pairs if d is not None and n is not None]
    pairs.sort(key=lambda pair: pair[0])       # oldest day first, whatever the caller did
    for (_d0, older), (d1, newer) in zip(pairs, pairs[1:]):
        if newer > older:
            gain = d1
    if gain is None or _as_day(today) is None:
        return None, None
    return (datetime.date.fromisoformat(today)
            - datetime.date.fromisoformat(gain)).days, gain


def net_gain(series: list[dict], now_lines: int,
             today: str) -> tuple[int | None, str | None]:
    """The net `src/` line gain against the last recorded day, in the ledger caliber.

    THE BASELINE IS A DAY AND NOT THE WINDOW EDGE, because section 8.2 records the
    standing figure ONCE PER DAY: a 12-hour window holds no second daily row to subtract.
    The digest therefore names the baseline day beside the number, so the figure states
    what it measured. With no earlier day the gain has no baseline and the digest says so
    rather than printing 0.

    A ROW WITH NO COMPARABLE STANDING IS NO BASELINE. Subtracting a `None` raises, so the
    reader takes the newest earlier day that carries an integer, and reports no baseline
    when there is none.
    """
    usable = [(d, n) for d, n in
              ((_as_day(r.get("day")), _as_int(r.get("standing"))) for r in series)
              if d is not None and n is not None and d < today]
    if not usable:
        return None, None
    usable.sort(key=lambda pair: pair[0])      # oldest day first, whatever the caller did
    day, base = usable[-1]
    return now_lines - base, day


# ---------------------------------------------------------------- the twelve numbers


def shadow_list(window: list[dict], table) -> list[tuple[str, int]]:
    """Section 4.4: every row that LOST inside the window, with how often it lost.

    SHADOWING IS REPORTED AND NEVER REFUSED. The list re-runs the router's hit list over
    each record in the window and counts every hit that is not the winner, so a row that
    never wins in 30 days is a maintainer signal and needs no extra log field. Section
    6.7 puts this list into the maintainer's batch brief.
    """
    lost: dict[str, int] = {}
    if table is None:
        return []
    for line in window:
        rec = routable(line)
        if rec is None:
            continue
        for row in _hits(table, rec)[1:]:
            lost[row["id"]] = lost.get(row["id"], 0) + 1
    return sorted(lost.items())


def shadowing(window: list[dict], table) -> int | None:
    """Number 1, section 4.4: how often a row lost inside the window, as one count."""
    if table is None:
        return None
    return sum(n for _row, n in shadow_list(window, table))


def fallout_list(records: list[dict], table) -> list[dict]:
    """Section 4.6: every corpus record an EXPIRED row used to win, and where it falls.

    The router drops an expired row, so expiry DOES move every record that row used to
    win, to the next matching row or to NO MATCH. The list re-routes each corpus record
    against the table with expiry lifted, and reports the records an expired row wins.
    Section 6.7 puts this list into the maintainer's batch brief.
    """
    if table is None:
        return []
    dead = {r["id"] for r in table if r.get("expired")}
    if not dead:
        return []
    lifted = [dict(r, expired=False) for r in table]
    out = []
    for rec in records:
        if "facts" not in rec:
            continue
        got = _hits(lifted, rec)
        if not got or got[0]["id"] not in dead:
            continue
        live = _hits(table, rec)
        out.append({"record": rec.get("id"), "task": rec.get("task"),
                    "row": got[0]["id"],
                    "falls_to": live[0]["id"] if live else None})
    return out


def expiry_fallout(records: list[dict], table) -> int | None:
    """Number 2, section 4.6: how many corpus records an expired row used to win."""
    if table is None:
        return None
    return len(fallout_list(records, table))


def dropped_returns(window: list[dict]) -> int:
    """Number 3, section 4.5.4: a return the program could not measure.

    R7 drops it loudly, writes NO corpus record, and parks the task with the reason that
    names the missing fact. Rule (c) writes `no-change` at `scripts/pod/pod.py:2065`,
    which is section 4.3.2 case 3: no changed file in scope, so no fact has a source.
    """
    return sum(1 for r in window if r.get("reason") == "no-change")


def orphan_masters(root: Path) -> tuple[int, int]:
    """Number 4, section 7.2: masters `src/Everything.lagda.md` does not import, and
    their lines.

    AD13 LEAVES A HOLE. A task writes a new master, never edits the catalog, and passes:
    Agda is green on the file, the consumer set is empty, and `make check` never reads
    it. The ledger still counts it, so `src/` records a net gain from code the trophy
    does not depend on. ONE parser owns the import list, `imported_modules()` at
    `scripts/pod/check-closure.py:90`, so conjunct 3 and this count never disagree.

    **ONE REPORT, ONE CALIBER, AND IT IS HEAD.** This read `at_head=False` while
    `standing()` read HEAD, so the same digest printed a working-tree figure beside a
    HEAD figure and the orphan lines were not a subset of the standing lines the reader
    subtracts them from. Both read HEAD now. A staged master that HEAD does not hold
    contributes 0 lines here, exactly as it contributes 0 to standing.
    """
    closure = _load("pod_digest_closure", "scripts/pod/check-closure.py", root)
    ledger = _load("pod_digest_ledger", "scripts/measure/ledger.py", root)
    imported = closure.imported_modules()
    known = closure._tracked_or_staged()
    count, lines = 0, 0
    for p in closure.masters():
        if p == closure.EVERYTHING:
            continue
        rel = str(p.relative_to(closure.ROOT))
        if closure.module_of(p) in imported or rel not in known:
            continue
        count += 1
        lines += ledger.count(rel, at_head=True)
    return count, lines


def telescope(root: Path) -> int:
    """Number 5, section 4.7: the module telescope hypothesis count.

    IT IS A REPORTED NUMBER AND NEVER A METER. It works as a delta only, it over-counts
    an ordinary binder such as `(n : ℕ)`, and it is a whole-tree proxy, so work landed
    elsewhere moves it. Fact 3 is the declared obligation list; this is not fact 3.
    """
    unbound = _load("pod_digest_unbound", "scripts/measure/check-unbound-hyp.py", root)
    total = 0
    for path in unbound.tracked_masters():
        for _line, names, _body in unbound.hypotheses(unbound.fences(path)):
            total += len(names)
    return total


def vacuous_and_foreign(window: list[dict], root: Path) -> tuple[int, int, int]:
    """Numbers 6, 7 and 8: conjunct 4 vacuous, conjunct 1 vacuous, and foreign paths.

    All three sit OUTSIDE `facts` in the acceptance record, which is why `record_of()`
    reads the run file: `unbound_vacuous` and `agda_vacuous` at
    `scripts/pod/accept.py:422`, `changed_files_foreign` at `:423`. A vacuous conjunct
    1 is section 4.3.2 case 4, a report-only return; a vacuous conjunct 4 is a return
    that changed no master, so no new unbound hypothesis is possible.
    """
    c4 = c1 = foreign = 0
    for line in window:
        rec = record_of(line, root)
        if not isinstance(rec, dict):
            continue
        c4 += 1 if rec.get("unbound_vacuous") else 0
        c1 += 1 if rec.get("agda_vacuous") else 0
        paths = rec.get("changed_files_foreign")
        # A COUNT OF PATHS AND NOT A COUNT OF CHARACTERS. `len()` accepts a string too,
        # so a run record that wrote one path as a bare string would report its length.
        foreign += len(paths) if isinstance(paths, (list, tuple)) else 0
    return c4, c1, foreign


def outcomes(window: list[dict], table) -> tuple[int, int] | None:
    """Number 10, section 4.2: the GO and NO-GO close counts.

    `outcome` is a declaration and never a matcher. It sits on the `done` row, so the
    count reads the MATCHED row of every `to: DONE` line, which is what A6 admits.
    """
    if table is None:
        return None
    by_id = {r.get("id"): r for r in table if isinstance(r, dict)}
    go = nogo = 0
    for line in window:
        if line.get("to") != "DONE":
            continue
        row = by_id.get(line.get("row")) or {}
        if row.get("outcome") == "no-go":
            nogo += 1
        elif row.get("outcome") == "go":
            go += 1
    return go, nogo


def retrieval(window: list[dict],
              refused: list[str] | None = None) -> tuple[int, int, int, int]:
    """Numbers 11 and 12, section 7.4 Part 1b: the miss rate and the zero-overlap share.

    One `retrieval` line per dispatch carries `offered`, `used`, `missed` and `overlap`
    (`scripts/pod/retrieve.py:376`). The miss rate is `missed / used`, and both sides
    count PATHS.

    **THE ZERO-OVERLAP SHARE COUNTS PATHS TOO, because the trigger does.** Section 7.4
    Part 1b adopts a semantic index when the miss rate goes above 20 percent AND MOST
    MISSED PATHS carry zero discriminative overlap. This counted one per LINE, so a
    dispatch that missed six paths weighed the same as a dispatch that missed one, and
    the half of the owner's trigger that reads `most` had the wrong denominator.

    **THE LINE RECORDS A MEAN, SO ONE CLASS OF PATH IS NOT DECIDABLE FROM IT.**
    `miss_signal()` writes the MEAN discriminative overlap over the missed files
    (`scripts/pod/retrieve.py:394`), and every per-file score is a count of shared
    discriminative tokens, so it is 0 or more. A mean of 0 therefore proves EVERY missed
    path of that dispatch scored 0. A mean above 0 proves only that at least one did not,
    and the line does not say which. The digest returns both: the paths it knows carry
    zero overlap, and the paths whose own score the log never recorded. It states the
    second number rather than folding it into either side.

    A HIGH overlap says the file ranked low, so the cure is scope or ranking. A ZERO
    overlap says no lexical method reaches it.
    """
    missed = used = zero = undetermined = 0
    for line in window:
        if line.get("event") != "retrieval":
            continue
        where = f"转移日志 seq={line.get('seq')}"
        paths = line.get("missed")
        if paths is None:
            paths = []
        count = _as_int(line.get("used"))
        overlap = _as_float(line.get("overlap"))
        # THE WHOLE ROW IS REFUSED, never half of it. Taking `missed` from a row whose
        # `used` cannot be read would put a numerator and a denominator from two
        # different sets of rows into one rate.
        if not isinstance(paths, list):
            _refuse(refused, where, "missed", paths)
            continue
        if count is None:
            _refuse(refused, where, "used", line.get("used"))
            continue
        if overlap is None:
            _refuse(refused, where, "overlap", line.get("overlap"))
            continue
        missed += len(paths)
        used += count
        if overlap == 0.0:
            zero += len(paths)
        else:
            undetermined += len(paths)
    return missed, used, zero, undetermined


# ---------------------------------------------------------------- the four sections


def conclusions(window: list[dict]) -> dict:
    """Section 一: finished, dispatched, parked, and the newest done line.

    IT PRINTS THE NEWEST `to: DONE` LINE'S TASK CODE AND ITS MATCHED ROW ID, with no
    adjective (section 8.1). Ranking is a judgement AD1 forbids the program.
    """
    done = [r for r in window if r.get("to") == "DONE"]
    return {
        "finished": len(done),
        "dispatched": sum(1 for r in window
                          if r.get("from") == "READY" and r.get("to") == "RUNNING"),
        "parked": sum(1 for r in window if r.get("to") == "PARKED"),
        "newest_done": (done[-1].get("task"), done[-1].get("row")) if done else None,
    }


def task_rows(lines: list[dict], window: list[dict], state, now: float,
              refused: list[str] | None = None) -> list[dict]:
    """Section 二: one row per code, from the LAST transition per code.

    WHICH CODES. Every code with a transition inside the window, plus every code whose
    current state is live. A worker dispatched before the window and still running emits
    no line inside it, and a task ledger that hides a running task is a false ledger.

    A CODE IS A STRING AND AN ATTEMPT IS AN INTEGER, and both are checked. `sorted()` over
    a set holding a string and a number raises `TypeError`, and `int(attempt)` raises on
    any string that is not a number. Neither may stop the digest, so a row that fails
    either test is refused and named, and every other row still prints.
    """
    codes = {r.get("task") for r in window if isinstance(r.get("task"), str) and r["task"]}
    codes |= {c for c, t in state.tasks.items()
              if isinstance(c, str) and t.status in ("READY", "RUNNING", "RETURNED",
                                                     "CHECKING")}
    out = []
    for code in sorted(codes):
        # A TRANSITION and never an event. A `retrieval` line carries the task code and
        # no `to`, so reading the last line of a code would report an empty state.
        mine = [r for r in lines if r.get("task") == code and r.get("to")]
        if not mine:
            continue
        last = mine[-1]
        launched = [r for r in mine if r.get("to") == "RUNNING"]
        t0 = pod_mod._epoch(launched[-1].get("ts")) if launched else None
        t1 = (pod_mod._epoch(last.get("ts"))
              if last.get("to") in ("DONE", "PARKED") else now)
        model = next((r.get("model") for r in reversed(mine) if r.get("model")), None)
        effort = next((r.get("effort") for r in reversed(mine) if r.get("effort")), None)
        attempt = next((r.get("attempt") for r in reversed(mine)
                        if r.get("attempt") is not None), None)
        instance = None if attempt is None else _as_int(attempt)
        if attempt is not None and instance is None:
            _refuse(refused, f"转移日志 任务 {code}", "attempt", attempt)
        out.append({
            "code": code,
            "state": last.get("to") if isinstance(last.get("to"), str) else "",
            # `attempt` counts the retries, so the FIRST dispatch is instance 1.
            "instance": None if instance is None else instance + 1,
            "head": f"{model} / {effort}" if model else "未知",
            "elapsed": None if t0 is None or t1 is None else t1 - t0,
        })
    return out


def parked_now(lines: list[dict], state) -> list[dict]:
    """Section 四: every PARKED code with its reason, from the log's park lines.

    IT READS THE LOG AND NOT THE FOLD. `replay_log()` at `scripts/pod/pod.py:433` looks
    for `park_reason` in the line while `emit()` writes the key as `reason`, so a folded
    task carries no reason. The park line always carries one.

    THE REASON IS RENDERED AND MUST THEREFORE BE A STRING. `render()` calls
    `startswith()` on it, and a reason that is not a string would raise there, one section
    after every number was already computed.
    """
    out = []
    for code in sorted(c for c, t in state.tasks.items()
                       if isinstance(c, str) and t.status == "PARKED"):
        park = [r for r in lines
                if r.get("task") == code and r.get("to") == "PARKED"]
        if not park:
            continue
        last = park[-1]
        detail = last.get("detail") or []
        reason = last.get("reason")
        out.append({"code": code,
                    "reason": reason if isinstance(reason, str) and reason else "未记录",
                    "detail": detail[0] if isinstance(detail, list) and detail else None,
                    "dir": _task_dir(code)})
    return out


def _task_dir(code: str) -> str | None:
    """The task's directory, through `agents_tree.task_dir()`, which looks in
    `agents/tasks/` and then in `agents/tasks/archive/`.

    IT READS THE CHECKOUT AND NOT THE DIGEST'S ROOT, because `agents_tree` anchors on the
    repository marker. In the loop the two are the same directory.
    """
    try:
        found = agents_tree.task_dir(code)
    except Exception:
        return None
    return str(found).replace(str(agents_tree.ROOT) + "/", "") if found else None


def queue_requests(root: Path) -> list[dict]:
    """Section 四: every queue REQUEST, which is an entry that names NO brief.

    An entry with no `brief` is never a task: rule (a1) skips it, and the digest prints
    it until the mathematician adds the brief path. The program never writes a brief,
    because AD3 gives the brief to the mathematician.
    """
    out = []
    # `queue_entries()` returns whatever the `[[task]]` array holds, and the file is
    # hand-written, so an entry that is not a table must not raise here.
    for entry in pod_mod.queue_entries(root / "dev" / "pod" / "queue.toml"):
        if not isinstance(entry, dict) or entry.get("brief"):
            continue
        out.append({"code": entry.get("code") or "未命名",
                    "reason": entry.get("reason") or entry.get("failed_check") or "未记录"})
    return out


def owner_rulings(root: Path) -> list[dict]:
    """Section 四: every open gap of section 11 whose settlement needs an OWNER RULING.

    THE MEMO IS THE SOURCE and it is parsed at run time, so a gap that closes stops
    printing with no edit here. A row qualifies when its second cell names an owner
    ruling and neither cell records it as closed, absorbed or settled.
    """
    path = root / "dev" / "memos" / "LJ-4-pod-program-design.md"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return []
    head = text.find("## 11. Open gaps and risks")
    if head < 0:
        return []
    out = []
    row_re = re.compile(r"^\|\s*([Mm]\d+)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*$", re.M)
    for m in row_re.finditer(text[head:]):
        gap, cell, settle = m.group(1), m.group(2), m.group(3)
        if "owner ruling" not in settle.lower():
            continue
        if "CLOSED" in cell or "ABSORBED" in settle or settle.startswith("Settled"):
            continue
        out.append({"gap": gap, "what": GAP_ZH.get(gap)})
    return out


# ---------------------------------------------------------------- build and render


def build(root: Path | None = None, hours: float = WINDOW_HOURS,
          now: float | None = None, record: bool = True) -> dict:
    """Every field of the digest, each from the source `FIELD_SOURCES` names.

    IT COMPUTES AND IT NEVER DECIDES. No value below is compared with a threshold, and
    no action follows from any of them: the two AD7 numbers report, the twelve report,
    and the rollback criterion is the owner's.

    EVERY READER THAT CAN MEET A MALFORMED ROW TAKES THE SAME SINK, `refused`. A refused
    row enters no count and is named in section 四. The digest still prints, because a
    digest that dies on one torn row tells the owner nothing about a loop that stopped.
    """
    root = ROOT if root is None else Path(root)
    now = time.time() if now is None else float(now)
    t0 = now - hours * 3600.0
    refused: list[str] = []
    # THE LOG READER AND THE FOLD BELONG TO `pod.py`. Both walk untrusted JSON, so a
    # refusal there is reported here and loses its own section rather than the report.
    try:
        lines = pod_mod.log_lines(root)
    except Exception as exc:                   # a torn `seq`, an unreadable directory
        refused.append(f"转移日志：无法读取，{type(exc).__name__}。本报告无转移数据。")
        lines = []
    window = in_window(lines, t0, now)
    try:
        state = pod_mod.replay_log(pod_mod.State(), root)
    except Exception as exc:
        refused.append(f"转移日志：无法折叠为状态，{type(exc).__name__}。停放清单可能不全。")
        state = pod_mod.State()
    table = load_table(root)
    corpus = corpus_records(root)

    day = _local_day(now)
    # THREE FIELDS MEASURE THE CHECKOUT and each one runs `git` or reads 99 masters. A
    # reader that fails loses ITS OWN field and prints `未知`; it never takes the other
    # eleven numbers with it, and it never falls back to 0.
    try:
        lines_now, masters = standing(root)
    except Exception:
        lines_now, masters = None, None
    # THE RECORD IS WRITTEN BEFORE THE SERIES IS READ, and the series is read ONCE. The
    # newest day of the series must be today, or a gain landed today is invisible to
    # `days_since_gain()`, which compares consecutive days.
    if record and lines_now is not None:
        try:
            record_standing(root, day, lines_now, masters)
        except OSError as exc:
            refused.append(f"每日行数记录：无法写入，{type(exc).__name__}。今日不记录。")
    series = standing_series(root, refused)

    c4, c1, foreign = vacuous_and_foreign(window, root)
    missed, used, zero, undetermined = retrieval(window, refused)
    try:
        orphans, orphan_lines = orphan_masters(root)
    except Exception:
        orphans, orphan_lines = None, None
    try:
        telescopes = telescope(root)
    except Exception:
        telescopes = None
    gain_days, gain_day = days_since_gain(series, day)
    net, net_base = ((None, None) if lines_now is None
                     else net_gain(series, lines_now, day))

    data = dict(conclusions(window))
    data.update({
        "day": day,
        "hours": hours,
        "standing": lines_now,
        "masters": masters,
        "net_lines": net,
        "net_baseline_day": net_base,
        "task_rows": task_rows(lines, window, state, now, refused),
        "no_match_rate": no_match_rate(window),
        "no_match_cumulative": no_match_rate(lines),
        "park_reasons_other": park_reasons_other(window),
        "days_since_gain": gain_days,
        "gain_day": gain_day,
        "shadowing": shadowing(window, table),
        "expiry_fallout": expiry_fallout(corpus, table),
        "dropped_returns": dropped_returns(window),
        "orphan_masters": orphans,
        "orphan_lines": orphan_lines,
        "telescope": telescopes,
        "vacuous_conjunct_4": c4,
        "vacuous_conjunct_1": c1,
        "foreign_paths": foreign,
        "corpus_records": len(corpus),
        "outcomes": outcomes(window, table),
        "retrieval_miss": (missed, used),
        "retrieval_zero_overlap": zero,
        "retrieval_undetermined": undetermined,
        "blocked_parked": parked_now(lines, state),
        "parked_total": state.count("PARKED"),
        "queue_requests": queue_requests(root),
        "owner_rulings": owner_rulings(root),
        "refused_rows": refused,
    })
    return data


def render(data: dict) -> str:
    """The four sections of 8.1, in the shape of the worked example at 8.3.

    NO SENTENCE RANKS ANYTHING. Every line states a count, a rate, a code or a reason.
    """
    hours = data["hours"]
    hours_txt = f"{hours:g}"
    out = [f"POD 日报  {data['day']}  （窗口：前 {hours_txt} 小时）", ""]

    # ---- 一、今日结论
    out.append("一、今日结论")
    net = data["net_lines"]
    net_txt = (f"src/ 净增 {net:,} 行，对比 {data['net_baseline_day']} 的记录。"
               if net is not None else "src/ 净增无更早记录可比。")
    # ONE POINT PER LINE. The counts are one point, the size figure is another, and the
    # CALIBER is a third. One report states one caliber, so it is stated once, here, and
    # every line figure in the four sections is that measurement.
    out.append(f"  完成 {data['finished']} 个任务，派发 {data['dispatched']} 个，"
               f"停放 {data['parked']} 个。")
    out.append(f"  {net_txt}")
    out.append("  行数口径为 ledger.toml 在 HEAD 上的计数，本报告的每个行数都用它。")
    newest = data["newest_done"]
    out.append(f"  最新完成：[{newest[0]}]，命中规则 {newest[1]}。" if newest
               else "  最新完成：窗口内无完成记录。")
    out.append("")

    # ---- 二、任务台账
    out.append("二、任务台账")
    out.append("  " + _pad("代码", COLS[0]) + _pad("状态", COLS[1])
               + _pad("实例", COLS[2]) + _pad("头", COLS[3]) + "用时")
    if not data["task_rows"]:
        out.append("  窗口内无任务转移，且无运行中的任务。")
    for row in data["task_rows"]:
        out.append("  " + _pad(row["code"], COLS[0])
                   + _pad(STATE_ZH.get(row["state"], row["state"]), COLS[1])
                   + _pad("未知" if row["instance"] is None else str(row["instance"]),
                          COLS[2])
                   + _pad(row["head"], COLS[3]) + _hhmm(row["elapsed"]))
    out.append("")

    # ---- 三、报告数
    out.append("三、报告数")
    wn, wd = data["no_match_rate"]
    cn, cd = data["no_match_cumulative"]
    out.append(f"  规则表未命中率：窗口内 {_rate(wn, wd)}；累计 {_rate(cn, cd)}。")
    # THE LABEL SAYS EIGHT CLASSES, SO ONLY THE EIGHT ARE ON THAT LINE. A reason section
    # 8.2 does not name gets its own line, and the eight-class count stays true.
    other = data["park_reasons_other"]
    eight = {k: v for k, v in other.items() if k in PARK_CLASSES}
    unlisted = other.get(PARK_UNLISTED, 0)
    eight_txt = ("；".join(f"{k} {v} 次" for k, v in eight.items()) if eight else "无")
    out.append(f"  其余八类停放原因单独计数：{eight_txt}。")
    if unlisted:
        out.append(f"  另有 {unlisted} 次停放，其原因不属于第 8.2 节的八类。")
    mn, mu = data["retrieval_miss"]
    # THE UNIT IS THE PATH, because the adopt trigger reads "most missed PATHS". The
    # second number names the paths whose own overlap the log recorded only as a mean.
    out.append(f"  检索缺失率：窗口内 {_rate(mn, mu)}；"
               f"其中零判别重叠 {data['retrieval_zero_overlap']} 条路径，")
    out.append(f"        另有 {data['retrieval_undetermined']} 条路径只有均值记录，"
               "无法逐条判定。触发线为")
    out.append(f"        {RETRIEVAL_TRIGGER}。")
    days = data["days_since_gain"]
    if days is None:
        out.append("  src/ 距上次净增：无净增记录。")
    elif days == 0:
        out.append("  src/ 距上次净增：0 天。上次净增为今日。")
    else:
        out.append(f"  src/ 距上次净增：{days} 天。上次净增日为 {data['gain_day']}。")
    go_nogo = data["outcomes"]
    out.append(f"  其他：遮蔽 {_num(data['shadowing'])} 次；"
               f"过期回落 {_num(data['expiry_fallout'])} 条；"
               f"丢弃返回 {_num(data['dropped_returns'])} 次；"
               f"孤儿母本 {_num(data['orphan_masters'])} 个，"
               f"共 {_num(data['orphan_lines'])} 行；")
    out.append(f"        望远镜假设 {_num(data['telescope'])} 个；"
               f"第 4 合取空过 {_num(data['vacuous_conjunct_4'])} 次；"
               f"第 1 合取空过 {_num(data['vacuous_conjunct_1'])} 次；")
    out.append(f"        越界改动 {_num(data['foreign_paths'])} 个；"
               f"语料记录 {_num(data['corpus_records'])} 条；"
               + (f"结论 GO {go_nogo[0]} 个，NO-GO {go_nogo[1]} 个。"
                  if go_nogo else "结论 GO 与 NO-GO 未知。"))
    out.append("  以上只作报告，不触发任何动作。是否回滚由仓库所有者判断。")
    out.append("")

    # ---- 四、阻塞与待裁决
    out.append("四、阻塞与待裁决")
    for park in data["blocked_parked"]:
        out.append(f"  [{park['code']}] 停放，原因 {park['reason']}。")
        if park["detail"]:
            out += _wrap(f"详情：{park['detail']}")
        if park["dir"]:
            out.append(f"  任务目录：{park['dir']}")
        if park["reason"].startswith(BRIEF_REPAIR):
            out.append("  简报由数学家修复。")
    out.append(f"  停放计数 {data['parked_total']}/{PARK_STOP}。"
               f"到 {PARK_STOP} 个停放，整个循环停止。")
    for req in data["queue_requests"]:
        out += _wrap(f"[{req['code']}] 队列请求，无简报路径，原因 {req['reason']}。")
    for gap in data["owner_rulings"]:
        what = f"{gap['what']}（见第 11 节 {gap['gap']}）" if gap["what"] \
            else f"见第 11 节 {gap['gap']}"
        out.append(f"  待仓库所有者裁决：{what}。")
    # THE REFUSED ROWS ARE PRINTED AND NEVER DROPPED. A row the digest could not read is
    # a defect in the record, so the owner sees the row and the field that failed.
    refused = data.get("refused_rows") or []
    if refused:
        out.append(f"  本报告拒绝了 {len(refused)} 行记录，其中的数不进入任何统计。")
        for item in refused:
            out += _wrap(item)
    return "\n".join(out) + "\n"


def maintainer_inputs(root: Path | None = None, hours: float = WINDOW_HOURS,
                      now: float | None = None) -> dict:
    """The three log-derived lists section 6.7 puts into the maintainer's batch brief.

    THE BATCH BRIEF IS PROGRAM-WRITTEN and the program fills it from the log: every
    PARKED code with its reason and its facts, EVERY NO-MATCH RECORD IN THE WINDOW, THE
    SHADOWING LIST and THE EXPIRY FALLOUT LIST. `spawn_maintainer()` at
    `scripts/pod/pod.py:1714` writes the parked half and calls this for the other three,
    so the batch and the digest count one thing one way.

    IT SHARES THE DIGEST'S READERS ON PURPOSE. A second implementation of the hit list
    would let the batch see a shadowing count the owner's digest does not.
    """
    root = ROOT if root is None else Path(root)
    now = time.time() if now is None else float(now)
    window = in_window(pod_mod.log_lines(root), now - hours * 3600.0, now)
    table = load_table(root)
    no_match = [{"task": r.get("task"), "facts": r.get("facts"), "run": r.get("run")}
                for r in window if r.get("reason") == "no-match"]
    return {"hours": hours,
            "no_match": no_match,
            "shadowed": shadow_list(window, table),
            "fallout": fallout_list(corpus_records(root), table)}


def write_out(root: Path, text: str, now: float) -> Path:
    """`.pod-state/digest/<stamp>.txt`, plus `latest.txt`.

    `write_digest()` at `scripts/pod/pod.py:1787` runs this script with
    `capture_output=True`, so a digest that only prints reaches nobody.
    """
    d = root / ".pod-state" / "digest"
    d.mkdir(parents=True, exist_ok=True)
    path = d / (time.strftime("%Y-%m-%d-%H%M", time.localtime(now)) + ".txt")
    path.write_text(text, encoding="utf-8")
    (d / "latest.txt").write_text(text, encoding="utf-8")
    return path


def main(argv: list[str]) -> int:
    """The command line, and the three exit codes of the module docstring.

    NOTHING HERE MAY RAISE THROUGH. `write_digest()` at `scripts/pod/pod.py:1787` runs
    this script unattended, and a traceback on stderr is a report nobody reads. The
    digest prints BEFORE it writes, so a write that fails still leaves the owner the text.
    """
    ap = argparse.ArgumentParser(description="The POD digest, section 8")
    ap.add_argument("--hours", type=float, default=WINDOW_HOURS,
                    help="the reported window, in hours (default 12)")
    ap.add_argument("--root", default=None, help="the repository root")
    ap.add_argument("--now", type=float, default=None,
                    help="the window end, in epoch seconds (a test hook)")
    ap.add_argument("--no-write", action="store_true",
                    help="print only; write no file under .pod-state/digest/")
    ap.add_argument("--no-record", action="store_true",
                    help="print only; add no row to .pod-state/standing.jsonl")
    args = ap.parse_args(argv)
    # A USAGE ERROR EXITS 2 AND NAMES THE OPTION. A window of zero hours has no rate to
    # report, and a root that is not a directory reads nothing at all.
    if not (args.hours > 0):
        print("digest: --hours must be above 0", file=sys.stderr)
        return 2
    root = ROOT if args.root is None else Path(args.root).resolve()
    if not root.is_dir():
        print(f"digest: --root is not a directory: {root}", file=sys.stderr)
        return 2
    now = time.time() if args.now is None else args.now

    try:
        data = build(root, args.hours, now, record=not args.no_record)
        text = render(data)
    except DigestError as exc:
        print(f"digest: refused: {exc}", file=sys.stderr)
        return 1
    except Exception as exc:                    # never a traceback in an unattended loop
        print(f"digest: refused, {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    sys.stdout.write(text)
    if not args.no_write:
        try:
            write_out(root, text, now)
        except OSError as exc:
            print(f"digest: printed, but not written: {exc}", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
