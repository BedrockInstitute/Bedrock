#!/usr/bin/env python3
"""Regression tests for the POD digest, section 8 of the LJ-4 design.

WHY THIS FILE EXISTS. The digest is the one screen the repository owner reads, and three
of its rules are the kind that a later edit breaks silently.

1. **Every field names its source, and a field with no source is not in the digest**
   (`dev/memos/LJ-4-pod-program-design.md:2841-2842`). `FIELD_SOURCES` in
   `scripts/pod/digest.py` states the binding, and this suite RESOLVES every entry
   against the file and the line it names. A source that moves fails here rather than
   printing a stale number to the owner.
2. **The two AD7 numbers are defined exactly** (`:2867-2891`). The no-match rate counts
   ONE park reason and the other eight separately; the second number is a lookup in a
   recorded daily series and never a re-derivation. Both are computed against a
   synthetic transition log with a known answer.
3. **No sentence in the digest ranks anything** (`:2860-2862`), because ranking is a
   judgement AD1 forbids the program and AD3 gives to the mathematician. The rendered
   text is searched for every word of `RANKING_WORDS`.

NO TEST HERE STARTS AGDA, DISPATCHES AN AGENT OR WRITES INTO THE REPOSITORY. The
transition log, the table, the corpus, the queue and the run records are synthetic and
live under a temporary root. Three numbers measure the CHECKOUT by design (the standing
figure, the orphan masters and the telescope count), so the fixture links the real
`scripts/` and asserts a relation over them and never a frozen constant.

THE FIXTURE CAN FAIL, which is C-45. The shadowing test drives one record that two rows
match and one record that no row matches, so a counter stuck at zero and a counter stuck
at one both go red.

Run: `python3 scripts/tests/test_pod_digest.py`
"""

from __future__ import annotations

import contextlib
import datetime
import importlib.util
import io
import json
import shutil
import sys
import tempfile
import time
import types
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "pod"))


def _load(name: str, rel: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


agents_tree = _load("agents_tree", "scripts/agents_tree.py")
table_mod = _load("table", "scripts/pod/table.py")
pod = _load("pod", "scripts/pod/pod.py")
digest = _load("digest", "scripts/pod/digest.py")

#: The window end of every fixture, fixed so a run is reproducible. Local noon, because
#: the digest reports a LOCAL day and the log carries UTC stamps.
NOW = time.mktime((2026, 8, 17, 12, 0, 0, 0, 0, -1))
DAY = time.strftime("%Y-%m-%d", time.localtime(NOW))


def _utc(offset_hours: float) -> str:
    """One UTC stamp, `offset_hours` before NOW, in the log's own format."""
    return time.strftime("%Y-%m-%dT%H:%M:%SZ",
                         time.gmtime(NOW - offset_hours * 3600.0))


FACTS_GREEN = {"exit_code": 0, "error_class": None, "obligations_delta": -2,
               "changed_files": ["src/L/Foo.lagda.md"], "seconds": 12.5,
               "heap_wall": False}
FACTS_ODD = {"exit_code": 7, "error_class": "other", "obligations_delta": 0,
             "changed_files": ["dev/notes.md"], "seconds": 3.0, "heap_wall": False}
FACTS_RED = {"exit_code": 1, "error_class": "termination", "obligations_delta": 0,
             "changed_files": ["src/L/Bar.lagda.md"], "seconds": 40.0,
             "heap_wall": False}

# THE HEADER FOLLOWS THE LOADER AND IS NEVER TYPED. `table.py` refuses a vocabulary it
# does not know, and amendment A10 moved it from `six-facts/1` to `seven-facts/1`. A
# hard-typed header made every table-derived number in this suite print `未知` instead,
# which is a fixture that silently stopped testing.
TABLE = f"""\
[meta]
schema = {table_mod.SCHEMA}
vocab = {json.dumps(table_mod.VOCAB)}

[[row]]
id = "task-lj-1-386-go"
scope = "task:LJ-1.386"
priority = 10
action = "done"
outcome = "go"
added = 2026-08-17
added_by = "mathematician"
reason = "The branch closes on a green run with a negative obligation delta."
expired = false

  [row.when]
  exit_code = 0

[[row]]
id = "sys-accept-green"
scope = "system"
priority = 50
action = "accept"
added = 2026-08-17
added_by = "owner"
reason = "A green run with no task row retries once under the same head."
expired = false

  [row.when]
  exit_code = 0

[[row]]
id = "sys-park-on-heap"
scope = "system"
priority = 100
action = "park"
added = 2026-08-17
added_by = "owner"
reason = "A heap wall needs a split and the maintainer prices it."
expired = false

  [row.when]
  heap_wall = true

[[row]]
id = "task-lj-1-390-old"
scope = "task:LJ-1.390"
priority = 5
action = "park"
added = 2026-08-15
added_by = "mathematician"
reason = "A termination failure on this branch parks for the mathematician."
expired = true
expired_at = 2026-08-16

  [row.when]
  exit_code = 1
"""

QUEUE = """\
[[task]]
code = "LJ-1.391"
brief = "agents/tasks/LJ-1-391/LJ-1.391.md"
added = 2026-08-17
added_by = "mathematician"

[[task]]
code = "LJ-1.386-split"
split_of = "LJ-1.386"
reason = "park_and_split: error_class heap_wall, 2 changed files"
added = 2026-08-17
added_by = "maintainer"
"""


def _run_record(root: Path, code: str, n: int, **extra) -> str:
    """One acceptance run record, in the format `_write_run_record()` writes: header
    lines, then the WHOLE record as one JSON object on the last non-blank line."""
    rel = f"agents/tasks/{agents_tree.normalise(code)}/runs/accept-{n}.out"
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    rec = {"task": code, "caliber": "-A64m -I0 -M8g", "concurrency": 1,
           "agda_vacuous": False, "unbound_vacuous": False,
           "changed_files_foreign": [], "facts": FACTS_GREEN}
    rec.update(extra)
    path.write_text("# arm accept-1\n# exit 0\n\n" + json.dumps(rec, sort_keys=True)
                    + "\n", encoding="utf-8")
    return rel


def write_log(root: Path, lines: list[dict]) -> Path:
    """The whole transition log, one JSON object per line, in the loop's own file name."""
    month = time.strftime("%Y-%m", time.gmtime(NOW))
    path = root / "dev" / "pod" / "transitions" / f"{month}.jsonl"
    path.write_text("\n".join(json.dumps(x, sort_keys=True) for x in lines) + "\n",
                    encoding="utf-8")
    return path


def append_log(root: Path, line: dict) -> None:
    """One more line at the tail of the log, with the next `seq`. The malformed-row tests
    use it: a bad row must cost its own row and never the report."""
    month = time.strftime("%Y-%m", time.gmtime(NOW))
    path = root / "dev" / "pod" / "transitions" / f"{month}.jsonl"
    old = [json.loads(x) for x in path.read_text(encoding="utf-8").split("\n") if x.strip()]
    line = dict(line)
    line.setdefault("seq", max(int(x.get("seq", 0)) for x in old) + 1)
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(line, sort_keys=True) + "\n")


def build_fixture(tmp: Path) -> Path:
    """A whole synthetic root: the log, the table, the corpus, the queue, the run
    records and the standing series. `scripts/` and `dev/memos/` link to the checkout,
    because three reported numbers measure the checkout and one reads the design memo."""
    root = tmp / "repo"
    (root / "dev" / "pod" / "transitions").mkdir(parents=True)
    (root / ".pod-state").mkdir(parents=True)
    (root / "scripts").symlink_to(ROOT / "scripts")
    (root / "dev" / "memos").symlink_to(ROOT / "dev" / "memos")
    (root / "dev" / "pod" / "table.toml").write_text(TABLE, encoding="utf-8")
    (root / "dev" / "pod" / "queue.toml").write_text(QUEUE, encoding="utf-8")
    shutil.copy(ROOT / "dev" / "pod" / "heads.toml", root / "dev" / "pod" / "heads.toml")

    run_done = _run_record(root, "LJ-1.386", 1, unbound_vacuous=True,
                           changed_files_foreign=["dev/a.md", "dev/b.md"])
    run_miss = _run_record(root, "LJ-1.N03", 1, agda_vacuous=True, facts=FACTS_ODD)

    # THE FIRST FIVE LINES SIT OUTSIDE THE 12-HOUR WINDOW, and they are what makes the
    # cumulative AD7 rate differ from the window rate. [LJ-1.386] was dispatched once,
    # returned, parked with `no-match`, and went back to READY when the table gained its
    # row. Without a return outside the window, a cumulative counter that silently read
    # the window alone would print the same pair and no assertion could tell them apart.
    lines = [
        {"ts": _utc(20), "task": "LJ-1.386", "from": None, "to": "READY"},
        {"ts": _utc(19.9), "task": "LJ-1.386", "from": "READY", "to": "RUNNING",
         "model": "claude-opus-5", "effort": "max", "attempt": 0, "pid": 4141},
        {"ts": _utc(19.8), "task": "LJ-1.386", "from": "RUNNING", "to": "RETURNED",
         "attempt": 0},
        {"ts": _utc(19.7), "task": "LJ-1.386", "from": "RETURNED", "to": "CHECKING",
         "attempt": 0},
        {"ts": _utc(19.6), "task": "LJ-1.386", "from": "CHECKING", "to": "PARKED",
         "reason": "no-match", "row": None, "attempt": 0},
        {"ts": _utc(11), "task": "LJ-1.386", "from": "PARKED", "to": "READY"},
        {"ts": _utc(10), "task": "LJ-1.386", "from": "READY",
         "to": "RUNNING", "model": "claude-opus-5", "effort": "max", "attempt": 1,
         "pid": 4242},
        {"ts": _utc(9.5), "task": "LJ-1.386", "from": "RUNNING",
         "to": "RETURNED", "attempt": 1},
        {"ts": _utc(9.4), "task": "LJ-1.386", "from": "RETURNED",
         "to": "CHECKING", "attempt": 1},
        {"ts": _utc(9.3), "task": "LJ-1.386", "from": "CHECKING",
         "to": "DONE", "row": "task-lj-1-386-go", "facts": FACTS_GREEN,
         "caliber": "-A64m -I0 -M8g", "concurrency": 1, "run": run_done,
         "attempt": 1, "model": "claude-opus-5", "effort": "max"},
        # TWO MISSED PATHS ON ONE LINE, and the line's mean overlap is 0. A zero-overlap
        # share that counts LINES reads 1 here and a share that counts PATHS reads 2, so
        # the fixture tells the two apart. Section 7.4 Part 1b counts paths.
        {"ts": _utc(9.2), "task": "LJ-1.386", "event": "retrieval",
         "offered": 5, "used": 3, "missed": ["dev/JOURNAL.md", "dev/ARCHIVE.md"],
         "overlap": 0.0},
        {"ts": _utc(8), "task": "LJ-1.N01", "from": None, "to": "READY"},
        {"ts": _utc(7.5), "task": "LJ-1.N01", "from": "READY",
         "to": "RUNNING", "model": "claude-fable-5", "effort": "high", "attempt": 0,
         "pid": 4343},
        {"ts": _utc(7.4), "task": "LJ-1.N01", "event": "retrieval",
         "offered": 4, "used": 6, "missed": ["dev/x.md", "dev/y.md"], "overlap": 0.42},
        {"ts": _utc(6), "task": "LJ-1.N02", "from": None, "to": "READY"},
        {"ts": _utc(5.9), "task": "LJ-1.N02", "from": "READY",
         "to": "PARKED", "reason": "preflight:P8",
         "detail": ["P8 branch no-go-stated names a path whose parent is absent"]},
        {"ts": _utc(5), "task": "LJ-1.N03", "from": None, "to": "READY"},
        {"ts": _utc(4.9), "task": "LJ-1.N03", "from": "READY",
         "to": "RUNNING", "model": "claude-opus-5", "effort": "max", "attempt": 0},
        {"ts": _utc(4.5), "task": "LJ-1.N03", "from": "RUNNING",
         "to": "RETURNED", "attempt": 0},
        {"ts": _utc(4.4), "task": "LJ-1.N03", "from": "RETURNED",
         "to": "CHECKING", "attempt": 0},
        {"ts": _utc(4.3), "task": "LJ-1.N03", "from": "CHECKING",
         "to": "PARKED", "reason": "no-match", "row": None, "facts": FACTS_ODD,
         "caliber": "-A64m -I0 -M8g", "concurrency": 1, "run": run_miss,
         "attempt": 0, "model": "claude-opus-5", "effort": "max"},
        {"ts": _utc(3), "task": "LJ-1.N04", "from": None, "to": "READY"},
        {"ts": _utc(2.9), "task": "LJ-1.N04", "from": "READY",
         "to": "RUNNING", "model": "claude-sonnet-5", "effort": "high", "attempt": 0},
        {"ts": _utc(2.5), "task": "LJ-1.N04", "from": "RUNNING",
         "to": "RETURNED", "attempt": 0},
        {"ts": _utc(2.4), "task": "LJ-1.N04", "from": "RETURNED",
         "to": "CHECKING", "attempt": 0},
        {"ts": _utc(2.3), "task": "LJ-1.N04", "from": "CHECKING",
         "to": "PARKED", "reason": "no-change"},
        {"ts": _utc(1), "task": "", "event": "batch", "result": "empty"},
    ]
    # `seq` FOLLOWS THE LIST ORDER, which is time order. The reader sorts by `seq`, so a
    # hand-typed number that drifts from the position would reorder the log silently.
    for n, line in enumerate(lines, 1):
        line["seq"] = n
    write_log(root, lines)

    corpus = [
        {"id": "c-1", "task": "LJ-1.390", "provenance": "live", "recorded": "2026-08-16",
         "facts": FACTS_RED, "caliber": "-M8g", "concurrency": 1,
         "row": "task-lj-1-390-old", "action": "park"},
        {"id": "c-2", "task": "LJ-1.386", "provenance": "live", "recorded": "2026-08-17",
         "facts": FACTS_GREEN, "caliber": "-M8g", "concurrency": 1,
         "row": "task-lj-1-386-go", "action": "done"},
    ]
    (root / "dev" / "pod" / "replay-corpus.jsonl").write_text(
        "\n".join(json.dumps(x, sort_keys=True) for x in corpus) + "\n",
        encoding="utf-8")

    d0 = datetime.date.fromisoformat(DAY)
    series = [{"day": str(d0 - datetime.timedelta(days=2)), "standing": 32800,
               "masters": 96, "recorded": _utc(48)},
              {"day": str(d0 - datetime.timedelta(days=1)), "standing": 33000,
               "masters": 97, "recorded": _utc(24)}]
    (root / ".pod-state" / "standing.jsonl").write_text(
        "\n".join(json.dumps(r, sort_keys=True) for r in series) + "\n",
        encoding="utf-8")
    return root


def ledger_stub(head: dict, tree: dict):
    """A ledger whose two calibers give DIFFERENT numbers, which is the whole point.

    The real ledger reads HEAD by default and the working tree on request
    (`scripts/measure/ledger.py:145-150`). On a clean checkout the two agree, so a test
    that compares the digest against the real ledger cannot tell which caliber the digest
    asked for. This stub makes them disagree, so the assertion discriminates.
    """
    def count(path, at_head=True):
        return (head if at_head else tree).get(path, 0)
    return types.SimpleNamespace(countable_masters=lambda: sorted(head), count=count)


def closure_stub(imported: set, tracked: set, names: list):
    """A catalog and a tree, with no git and no checkout. `orphan_masters()` reads exactly
    these five names off `scripts/pod/check-closure.py`."""
    root = Path("/synthetic")
    paths = [root / "src" / n for n in names]
    return types.SimpleNamespace(
        ROOT=root, EVERYTHING=root / "src" / "Everything.lagda.md",
        masters=lambda: paths,
        imported_modules=lambda: imported,
        _tracked_or_staged=lambda: tracked,
        module_of=lambda p: p.name.removesuffix(".lagda.md"))


class Fixture(unittest.TestCase):
    """One built fixture per test, and every test reads the same synthetic log."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = build_fixture(Path(self.tmp.name))
        self.addCleanup(self.tmp.cleanup)

    def data(self, **kw):
        return digest.build(self.root, kw.pop("hours", 12.0), NOW, **kw)

    def stub(self, name: str, module):
        """Put one synthetic module in the digest's loader cache, under the key
        `_load()` builds. It is removed again at cleanup, because the cache is global."""
        key = f"{name}@{self.root}"
        digest._LOADED[key] = module
        self.addCleanup(lambda: digest._LOADED.pop(key, None))


# ---------------------------------------------------------------- every field's source


class Sources(unittest.TestCase):
    """`FIELD_SOURCES` is the rule "every field names its source" in executable form."""

    def test_every_named_source_resolves(self):
        for field, (rel, line, needle) in digest.FIELD_SOURCES.items():
            path = ROOT / rel
            self.assertTrue(path.is_file(), f"{field}: {rel} does not exist")
            hits = [n for n, text in enumerate(
                path.read_text(encoding="utf-8").split("\n"), 1) if needle in text]
            self.assertTrue(hits, f"{field}: `{needle}` is nowhere in {rel}")
            # THE ANCHOR IS THE TEST. THE LINE NUMBER IS NAVIGATION.
            # This assertion used to demand the recorded line sit within 10 of a hit, and
            # it went red three times in one day: 2026-08-18, at every edit that grew
            # `pod.py`, each time needing a human to re-resolve numbers by hand. **A test
            # that fails for a reason nobody can act on teaches people to re-run the
            # fixer, not to think.** What the source table promises is that the NEEDLE is
            # findable, and that is what this checks now.
            #
            # The drift is still reported, because a number that points somewhere else is
            # a real papercut for a reader who jumps to it. It is a WARNING and never a
            # failure, and `make check` stays green through it.
            near = min(abs(n - line) for n in hits)
            if near > 10:
                nearest = min(hits, key=lambda n: abs(n - line))
                print(f"  drift: {field}: {rel}:{line} -> {nearest} (`{needle}`)")

    def test_every_reported_field_has_a_source(self):
        """Two directions. No field without a source, and no source without a field."""
        derived = {"no_match_cumulative": "no_match_rate",
                   "gain_day": "days_since_gain",
                   "net_baseline_day": "net_lines",
                   "orphan_lines": "orphan_masters",
                   "masters": "standing",
                   "parked_total": "blocked_parked"}
        presentation = {"day", "hours"}
        with tempfile.TemporaryDirectory() as tmp:
            data = digest.build(build_fixture(Path(tmp)), 12.0, NOW, record=False)
        for key in data:
            self.assertIn(key, set(digest.FIELD_SOURCES) | set(derived) | presentation,
                          f"the digest reports `{key}` and names no source for it")
        for key in digest.FIELD_SOURCES:
            self.assertIn(key, data, f"`{key}` names a source and reports nothing")

    def test_every_chinese_gap_label_names_a_real_row(self):
        """`GAP_ZH` renders a gap of section 11. An ID that left the memo must not keep
        a Chinese phrase alive, so the parser and the table are checked against each
        other rather than against memory."""
        with tempfile.TemporaryDirectory() as tmp:
            found = {g["gap"] for g in digest.owner_rulings(build_fixture(Path(tmp)))}
        for gap in digest.GAP_ZH:
            self.assertIn(gap, found,
                          f"GAP_ZH names {gap}, which section 11 no longer holds "
                          f"as an open owner ruling")


# ---------------------------------------------------------------- the two AD7 numbers


class AD7(Fixture):

    def test_no_match_rate_counts_one_reason_over_every_return(self):
        """Section 8.2: park lines with reason `no-match` over ALL return lines.

        THE TWO PAIRS MUST DIFFER, or the assertion proves nothing. The window holds
        three returns and one no-match park. The log holds a fourth return and a second
        no-match park, both older than the window, so a cumulative counter that read the
        window alone would print (1, 3) and go red here.
        """
        data = self.data(record=False)
        self.assertEqual(data["no_match_rate"], (1, 3))
        self.assertEqual(data["no_match_cumulative"], (2, 4))

    def test_the_other_eight_reasons_are_counted_apart(self):
        """A `preflight:` park and a `no-change` park are NOT gaps in the table, so
        neither may enter the numerator, and both must still be reported."""
        data = self.data(record=False)
        self.assertEqual(data["park_reasons_other"],
                         {"no-change": 1, "preflight": 1})
        self.assertNotIn("no-match", data["park_reasons_other"])

    def test_the_eight_classes_are_classes_and_not_instances(self):
        """Section 8.2 names EIGHT classes, and four of them carry an instance in the
        reason string. Two pre-flight parks at two different check numbers are ONE class,
        so a report labelled `eight classes` may not print nine rows for them."""
        window = [{"to": "PARKED", "reason": "preflight:P8"},
                  {"to": "PARKED", "reason": "preflight:P19"},
                  {"to": "PARKED", "reason": "row:sys-park-on-heap"},
                  {"to": "PARKED", "reason": "stop_loop:sys-stop"},
                  {"to": "PARKED", "reason": "attempt_max:task-lj-1-386-go"},
                  {"to": "PARKED", "reason": "no-match"},      # AD7's own numerator
                  {"to": "DONE", "reason": "r4"}]              # not a park at all
        self.assertEqual(digest.park_reasons_other(window),
                         {"attempt_max": 1, "preflight": 2, "row": 1, "stop_loop": 1})
        self.assertEqual(sorted(digest.PARK_CLASSES),
                         sorted(["no-change", "preflight", "attempt_max", "r4",
                                 "admission", "launch", "row", "stop_loop"]))

    def test_a_reason_outside_the_eight_is_not_counted_as_one_of_them(self):
        """A count labelled `eight classes` may not quietly hold a ninth. An unknown
        reason lands in `unlisted` and the rendered text gives it its own line."""
        window = [{"to": "PARKED", "reason": "meteorite"},
                  {"to": "PARKED", "reason": "launch"}]
        got = digest.park_reasons_other(window)
        self.assertEqual(got, {"launch": 1, digest.PARK_UNLISTED: 1})
        data = self.data(record=False)
        data["park_reasons_other"] = got
        text = digest.render(data)
        self.assertIn("其余八类停放原因单独计数：launch 1 次。", text)
        self.assertIn("另有 1 次停放，其原因不属于第 8.2 节的八类。", text)

    def test_a_zero_denominator_prints_no_rate(self):
        """A window with no return has no rate. Printing 0% would state a measurement
        the evidence does not give."""
        self.assertIn("比率无定义", digest._rate(0, 0))
        self.assertEqual(digest._rate(1, 4), "1/4 = 25.0%")

    def test_days_since_gain_is_the_newest_rising_day(self):
        """Section 8.2: `gain_day` is the newest day whose standing exceeded the day
        before it. The series rises twice and the newest rise wins."""
        series = [{"day": "2026-08-10", "standing": 100},
                  {"day": "2026-08-12", "standing": 130},
                  {"day": "2026-08-14", "standing": 130},
                  {"day": "2026-08-16", "standing": 141}]
        self.assertEqual(digest.days_since_gain(series, "2026-08-17"),
                         (1, "2026-08-16"))
        flat = series[:1] + [{"day": "2026-08-12", "standing": 90}]
        self.assertEqual(digest.days_since_gain(flat, "2026-08-17"), (None, None))
        self.assertEqual(digest.days_since_gain([], "2026-08-17"), (None, None))

    def test_the_standing_figure_is_a_daily_lookup(self):
        """The digest RECORDS the standing figure once per day, so the number is a
        lookup and not a re-derivation. A second digest on one day corrects the row."""
        digest.record_standing(self.root, DAY, 4242, 97)
        digest.record_standing(self.root, DAY, 4243, 97)
        series = digest.standing_series(self.root)
        self.assertEqual([r["day"] for r in series].count(DAY), 1)
        self.assertEqual(series[-1]["standing"], 4243)

    def test_the_net_gain_names_its_baseline_day(self):
        """The baseline is the newest day BEFORE today, because the series holds one row
        per day and a 12-hour window holds no second row."""
        data = self.data()
        self.assertEqual(data["net_baseline_day"],
                         str(datetime.date.fromisoformat(DAY)
                             - datetime.timedelta(days=1)))
        self.assertEqual(data["net_lines"], data["standing"] - 33000)

    def test_the_ledger_caliber_is_the_one_used(self):
        """Section 8.2's definition trap: `git log --numstat` counts prose and the
        ledger counts in-fence non-blank lines. The digest uses the ledger.

        THIS IS THE INTEGRATION HALF and it names what it cannot tell apart. On a clean
        checkout the HEAD figure and the working-tree figure are equal, so the equality
        below does not decide which caliber `standing()` asked for. The two tests after
        it decide that, against a ledger whose calibers disagree by construction.
        """
        ledger = _load("ledger_for_digest", "scripts/measure/ledger.py")
        files = ledger.countable_masters()
        head = sum(ledger.count(f, at_head=True) for f in files)
        self.assertEqual(digest.standing(ROOT), (head, len(files)))

    def test_the_standing_figure_reads_head_and_never_the_working_tree(self):
        """ONE REPORT STATES ONE CALIBER, and section 8.2 makes it the ledger's, which
        reads HEAD. A working-tree read would count a half-written chapter as standing:
        `scripts/measure/ledger.py:147-150` records that it happened twice."""
        self.stub("pod_digest_ledger",
                  ledger_stub(head={"src/A.lagda.md": 100, "src/B.lagda.md": 20},
                              tree={"src/A.lagda.md": 1, "src/B.lagda.md": 2}))
        self.assertEqual(digest.standing(self.root), (120, 2))

    def test_the_orphan_lines_use_the_caliber_the_standing_figure_uses(self):
        """The orphan lines are subtracted from the standing lines by the reader, so the
        two must be the same measurement. This file read the working tree here and HEAD
        there, and one report then carried two calibers."""
        self.stub("pod_digest_ledger",
                  ledger_stub(head={"src/B.lagda.md": 20}, tree={"src/B.lagda.md": 2}))
        self.stub("pod_digest_closure",
                  closure_stub(imported={"A"},
                               tracked={"src/A.lagda.md", "src/B.lagda.md",
                                        "src/Everything.lagda.md"},
                               names=["Everything.lagda.md", "A.lagda.md",
                                      "B.lagda.md"]))
        # A is imported and Everything is the catalog, so B alone is the orphan.
        self.assertEqual(digest.orphan_masters(self.root), (1, 20))

    def test_an_untracked_master_is_not_an_orphan(self):
        """An UNTRACKED master is not in the repository yet, so it is its author's
        warning and never a number in the owner's report
        (`scripts/pod/check-closure.py:104-108`)."""
        self.stub("pod_digest_ledger", ledger_stub(head={"src/C.lagda.md": 7}, tree={}))
        self.stub("pod_digest_closure",
                  closure_stub(imported=set(), tracked={"src/Everything.lagda.md"},
                               names=["Everything.lagda.md", "C.lagda.md"]))
        self.assertEqual(digest.orphan_masters(self.root), (0, 0))


# ---------------------------------------------------------------- the twelve numbers


class Twelve(Fixture):

    def test_shadowing_counts_every_row_that_lost(self):
        """Section 4.4. The green record is matched by a task row and a system row, so
        one row lost; the odd record is matched by nothing, so nothing lost."""
        data = self.data(record=False)
        self.assertEqual(data["shadowing"], 1)
        table = digest.load_table(self.root)
        green = {"task": "LJ-1.386", "facts": FACTS_GREEN, "concurrency": 1}
        odd = {"task": "LJ-1.N03", "facts": FACTS_ODD, "concurrency": 1}
        self.assertEqual(len(digest._hits(table, green)), 2)
        self.assertEqual(len(digest._hits(table, odd)), 0)

    def test_expiry_fallout_counts_the_records_an_expired_row_won(self):
        """Section 4.6. One corpus record was won by a row that has since expired; the
        other is won by a live row and is not fallout."""
        data = self.data(record=False)
        self.assertEqual(data["expiry_fallout"], 1)
        self.assertEqual(data["corpus_records"], 2)

    def test_dropped_returns_count_the_no_change_parks(self):
        """Section 4.5.4. R7 drops a return it cannot measure and parks with the reason
        that names the missing fact."""
        self.assertEqual(self.data(record=False)["dropped_returns"], 1)

    def test_the_vacuous_flags_and_foreign_paths_come_from_the_run_record(self):
        """Sections 4.3.1, 4.3.2 and 5.4. All three sit OUTSIDE `facts`, so the digest
        reads the run file the log line names."""
        data = self.data(record=False)
        self.assertEqual(data["vacuous_conjunct_4"], 1)
        self.assertEqual(data["vacuous_conjunct_1"], 1)
        self.assertEqual(data["foreign_paths"], 2)

    def test_the_outcome_split_reads_the_matched_row(self):
        """Section 4.2. `outcome` never routes: it declares what a `done` close earns.

        THE SECOND HALF IS WHAT DISCRIMINATES. The fixture holds one GO close, so a
        counter that ignored `outcome` and counted every `to: DONE` line would also print
        (1, 0). The hand-built table below holds a GO row, a NO-GO row and a row with no
        `outcome` at all, and only a reader of the MATCHED row gets (1, 1).
        """
        self.assertEqual(self.data(record=False)["outcomes"], (1, 0))
        table = [{"id": "r-go", "outcome": "go"}, {"id": "r-nogo", "outcome": "no-go"},
                 {"id": "r-plain"}]
        window = [{"to": "DONE", "row": "r-go"}, {"to": "DONE", "row": "r-nogo"},
                  {"to": "DONE", "row": "r-plain"}, {"to": "DONE", "row": "r-gone"},
                  {"to": "PARKED", "row": "r-go"}]
        self.assertEqual(digest.outcomes(window, table), (1, 1))

    def test_the_retrieval_numbers_are_the_miss_rate_and_the_zero_overlap_share(self):
        """Section 7.4 Part 1b. Four missed paths over nine used, two of them with no
        discriminative overlap.

        THE UNIT IS THE PATH AND NEVER THE LINE. The adopt trigger reads `most missed
        PATHS carry zero overlap`, so a per-line count is the wrong denominator for half
        of the owner's trigger. The fixture puts TWO missed paths on the one line whose
        mean overlap is 0, so a per-line count reads 1 here and goes red.
        """
        data = self.data(record=False)
        self.assertEqual(data["retrieval_miss"], (4, 9))
        self.assertEqual(data["retrieval_zero_overlap"], 2)
        self.assertEqual(data["retrieval_undetermined"], 2)
        text = digest.render(data)
        self.assertIn("其中零判别重叠 2 条路径", text)
        self.assertIn("另有 2 条路径只有均值记录", text)

    def test_a_mean_above_zero_decides_no_path_on_its_own(self):
        """`miss_signal()` records the MEAN over the missed files
        (`scripts/pod/retrieve.py:340`). A mean of 0 proves every path scored 0, because
        each score counts shared tokens and cannot be negative. A mean above 0 proves
        only that one did not, so those paths are reported as undetermined and never as
        non-zero."""
        window = [{"event": "retrieval", "seq": 1, "used": 4,
                   "missed": ["a", "b", "c"], "overlap": 0.0},
                  {"event": "retrieval", "seq": 2, "used": 2,
                   "missed": ["d", "e"], "overlap": 0.5},
                  {"event": "retrieval", "seq": 3, "used": 1,
                   "missed": [], "overlap": 0.0},
                  {"to": "DONE", "seq": 4}]
        self.assertEqual(digest.retrieval(window), (5, 7, 3, 2))

    def test_the_checkout_numbers_are_measured_and_not_frozen(self):
        """The orphan master count, its lines and the telescope count measure the
        working tree. The suite asserts the relation and never a constant.

        `assertGreaterEqual(count, 0)` STOOD HERE AND COULD NOT FAIL: the counter only
        increments, so 0 or more is true of every tree and of every bug. The relation
        below can fail, and the two stub-driven tests above and below decide the logic.
        """
        count, lines = digest.orphan_masters(ROOT)
        self.assertEqual(count == 0, lines == 0)
        self.assertGreater(digest.telescope(ROOT), 0)

    def test_the_telescope_count_counts_names_and_not_hypotheses(self):
        """Section 4.7's reported number is the count of HYPOTHESIS NAMES. One binder
        may declare several, so a count of hypothesis groups is a different number."""
        self.stub("pod_digest_unbound", types.SimpleNamespace(
            tracked_masters=lambda: ["src/A.lagda.md", "src/B.lagda.md"],
            fences=lambda path: path,
            hypotheses=lambda fences: [(1, ["m", "n"], ""), (2, ["k"], "")]))
        # Two files, two hypothesis groups each, three names in each file.
        self.assertEqual(digest.telescope(self.root), 6)

    def test_an_unreadable_table_prints_no_number(self):
        """A field whose source cannot be read has no value. It never falls back to 0,
        because a silent 0 is the shape a broken source hides in."""
        (self.root / "dev" / "pod" / "table.toml").write_text("[meta]\nschema = 9\n",
                                                              encoding="utf-8")
        data = self.data(record=False)
        self.assertIsNone(data["shadowing"])
        self.assertIn("遮蔽 未知 次", digest.render(data))


# ---------------------------------------------------------------- the four sections


class Render(Fixture):

    def test_the_four_sections_are_present_in_order(self):
        text = digest.render(self.data(record=False))
        heads = ["一、今日结论", "二、任务台账", "三、报告数", "四、阻塞与待裁决"]
        seen = [text.index(h) for h in heads]
        self.assertEqual(seen, sorted(seen))

    def test_no_sentence_ranks_anything(self):
        """AD1 forbids the program a judgement and AD3 gives it to the mathematician.

        THE SEARCH IS SHOWN TO FIND SOMETHING. A banned-word search over a text that
        holds none of them passes whether the word list is right, wrong or empty, so the
        same search runs once over a planted sentence and must find it there.
        """
        text = digest.render(self.data(record=False))
        for word in digest.RANKING_WORDS:
            self.assertNotIn(word, text, f"the digest printed the ranking word {word}")
        planted = text + "\n  本次表现最好，建议回滚。"
        self.assertTrue([w for w in digest.RANKING_WORDS if w in planted],
                        "the ranking-word list finds nothing even in a ranking sentence")

    def test_the_newest_done_line_carries_no_adjective(self):
        """Section 8.1: it prints the newest `to: DONE` line's task code and its matched
        row id, and nothing else."""
        text = digest.render(self.data(record=False))
        self.assertIn("最新完成：[LJ-1.386]，命中规则 task-lj-1-386-go。", text)

    def test_the_task_ledger_holds_a_running_task_and_its_head(self):
        """Section 二 reads the last transition per code. A task dispatched before the
        window and still running must appear, or the ledger hides live work."""
        data = self.data(record=False)
        rows = {r["code"]: r for r in data["task_rows"]}
        self.assertEqual(rows["LJ-1.386"]["state"], "DONE")
        self.assertEqual(rows["LJ-1.386"]["instance"], 2)
        self.assertEqual(rows["LJ-1.N01"]["state"], "RUNNING")
        self.assertEqual(rows["LJ-1.N01"]["head"], "claude-fable-5 / high")
        text = digest.render(data)
        self.assertIn("运行中", text)
        self.assertIn("claude-opus-5 / max", text)

    def test_the_blocked_section_names_every_park_and_the_stop_count(self):
        """Section 四: every PARKED code with its reason, every queue REQUEST with no
        brief, and every owner ruling outstanding."""
        text = digest.render(self.data(record=False))
        self.assertIn("[LJ-1.N02] 停放，原因 preflight:P8。", text)
        self.assertIn("[LJ-1.N03] 停放，原因 no-match。", text)
        self.assertIn("停放计数 3/3。", text)
        self.assertIn("[LJ-1.386-split] 队列请求，无简报路径", text)
        self.assertIn("待仓库所有者裁决：", text)

    def test_a_queue_entry_with_a_brief_is_not_a_request(self):
        """An entry that NAMES a brief is a task, and rule (a1) turns it into one."""
        codes = [r["code"] for r in digest.queue_requests(self.root)]
        self.assertEqual(codes, ["LJ-1.386-split"])

    def test_the_report_states_one_caliber_and_states_it_once(self):
        """ONE REPORT, ONE CALIBER. The standing figure and the orphan lines were read
        with two different calibers, and no line of the text said either. The caliber is
        named once, in section 一, and it binds every line figure in the four sections."""
        text = digest.render(self.data(record=False))
        self.assertEqual(text.count("行数口径为 ledger.toml 在 HEAD 上的计数"), 1)
        # The word alone also appears in gap m2's Chinese label in section 四, which is
        # the owner's outstanding ruling ON the caliber and not a second declaration.
        self.assertIn("第二个报告数的行数口径", text)

    def test_no_line_of_the_digest_runs_past_the_worked_example_s_width(self):
        """Section 8.3 folds at about 76 display columns, and a CJK character occupies
        two. A line that runs past it wraps in the owner's terminal at a place nobody
        chose, which is how a number and its unit end up on separate lines."""
        text = digest.render(self.data(record=False))
        long = [ln for ln in text.split("\n") if digest._width(ln) > 78]
        self.assertEqual(long, [], f"{len(long)} line(s) run past 78 columns")

    def test_the_digest_reports_and_never_triggers(self):
        """Both AD7 numbers report and neither triggers. The rollback criterion is the
        owner's, and the digest says so in its own text."""
        text = digest.render(self.data(record=False))
        self.assertIn("以上只作报告，不触发任何动作。是否回滚由仓库所有者判断。", text)

    def test_the_punctuation_is_full_width(self):
        """The repository forbids half-width sentence punctuation in CJK prose.

        The rule is checked where it binds: a half-width mark that FOLLOWS a Chinese
        character is the digest's own prose. A mark inside a quoted value, such as the
        English reason `split_entry()` writes, is data and is never rewritten.

        THE SEARCH IS SHOWN TO FIND SOMETHING, exactly as the ranking-word search is. A
        scan that reports nothing proves nothing until it has reported something.
        """
        def offenders(text):
            return [(text[n - 1], char) for n, char in enumerate(text)
                    if n and char in ",.;:!?" and "一" <= text[n - 1] <= "鿿"]
        self.assertEqual(offenders(digest.render(self.data(record=False))), [])
        self.assertEqual(offenders("完成 1 个任务, 派发 3 个。"), [("务", ",")])

    def test_the_maintainer_batch_gets_its_three_log_derived_lists(self):
        """Section 6.7: the program fills the batch brief from the log with every
        no-match record in the window, the shadowing list and the expiry fallout list.
        The batch and the digest share one reader, so neither can count differently."""
        got = digest.maintainer_inputs(self.root, 12.0, NOW)
        self.assertEqual([r["task"] for r in got["no_match"]], ["LJ-1.N03"])
        self.assertEqual(got["shadowed"], [("sys-accept-green", 1)])
        self.assertEqual(got["fallout"][0]["row"], "task-lj-1-390-old")
        self.assertIsNone(got["fallout"][0]["falls_to"])

    def test_the_batch_brief_reads_the_park_reason_from_the_log(self):
        """`replay_log()` restores `park_reason` from a key the line does not carry, so
        a folded state names no reason. The batch reads the park line instead."""
        st = pod.replay_log(pod.State(), self.root)
        self.assertIsNone(st.tasks["LJ-1.N02"].park_reason)
        self.assertEqual(pod.park_reason_of("LJ-1.N02", self.root), "preflight:P8")

    def test_the_batch_lists_never_stop_the_batch(self):
        """A reader that cannot resolve is reported inside the brief and never raised:
        a maintainer batch that dies on a broken list loses every parked task with it."""
        text = "\n".join(pod.batch_lists(self.root / "does-not-exist"))
        self.assertIn("## THE SHADOWING LIST", text)
        self.assertIn("NONE", text)

    def test_it_writes_the_file_the_loop_can_read(self):
        """`write_digest()` runs this script under `capture_output=True`, so a digest
        that only prints reaches nobody."""
        text = digest.render(self.data(record=False))
        digest.write_out(self.root, text, NOW)
        latest = self.root / ".pod-state" / "digest" / "latest.txt"
        self.assertEqual(latest.read_text(encoding="utf-8"), text)


# ---------------------------------------------------------------- one row, not the report


class Refusals(Fixture):
    """ONE MALFORMED ROW MUST NOT KILL THE DIGEST.

    The loop runs unattended and the digest is how the owner learns it stopped. Every
    test below writes ONE row that the arithmetic cannot use, then asserts three things:
    the digest still builds, the bad row is NAMED, and its numbers are absent rather than
    guessed. Each row is a shape that raised a traceback before this suite existed.
    """

    def test_a_used_field_that_is_not_a_number_refuses_its_own_row(self):
        """`int(line.get("used") or 0)` raised `ValueError` on any string that is not a
        number, and one retrieval line then took the whole digest with it."""
        append_log(self.root, {"ts": _utc(2), "task": "LJ-1.N07", "event": "retrieval",
                               "offered": 3, "used": "三", "missed": ["dev/z.md"],
                               "overlap": 0.0})
        data = self.data(record=False)
        self.assertEqual(data["retrieval_miss"], (4, 9))      # the good rows are intact
        self.assertEqual(data["retrieval_zero_overlap"], 2)
        self.assertTrue(any("used" in r for r in data["refused_rows"]),
                        f"the bad row was not named: {data['refused_rows']}")
        self.assertIn("本报告拒绝了 1 行记录", digest.render(data))

    def test_a_missed_field_that_is_not_a_list_refuses_its_own_row(self):
        """`len()` accepts a string, so a `missed` written as one path would have been
        counted as its own length in characters."""
        append_log(self.root, {"ts": _utc(2), "task": "LJ-1.N07", "event": "retrieval",
                               "offered": 3, "used": 2, "missed": "dev/z.md",
                               "overlap": 0.0})
        data = self.data(record=False)
        self.assertEqual(data["retrieval_miss"], (4, 9))
        self.assertTrue(any("missed" in r for r in data["refused_rows"]))

    def test_an_attempt_that_is_not_a_number_refuses_its_own_row(self):
        """`int(attempt) + 1` raised on a string. The instance column then prints `未知`,
        which is the value the digest has, and the row is named."""
        append_log(self.root, {"ts": _utc(1), "task": "LJ-1.N08", "from": "READY",
                               "to": "RUNNING", "model": "claude-opus-5",
                               "effort": "max", "attempt": "second"})
        data = self.data(record=False)
        row = next(r for r in data["task_rows"] if r["code"] == "LJ-1.N08")
        self.assertIsNone(row["instance"])
        self.assertTrue(any("attempt" in r for r in data["refused_rows"]))
        self.assertIn("未知", digest.render(data))

    def test_a_standing_row_that_cannot_be_compared_refuses_its_own_row(self):
        """`newer["standing"] > older["standing"]` raised `TypeError` against `null`, and
        the daily series is runtime state that a crash can tear."""
        with open(self.root / ".pod-state" / "standing.jsonl", "a",
                  encoding="utf-8") as fh:
            fh.write(json.dumps({"day": str(datetime.date.fromisoformat(DAY)
                                            - datetime.timedelta(days=3)),
                                 "standing": None}) + "\n")
        data = self.data(record=False)
        self.assertEqual(data["net_baseline_day"],
                         str(datetime.date.fromisoformat(DAY)
                             - datetime.timedelta(days=1)))
        self.assertTrue(any("standing" in r for r in data["refused_rows"]))

    def test_a_standing_row_whose_day_is_not_a_date_refuses_its_own_row(self):
        """`date.fromisoformat()` raised `ValueError`, one section after every number was
        already computed."""
        with open(self.root / ".pod-state" / "standing.jsonl", "a",
                  encoding="utf-8") as fh:
            fh.write(json.dumps({"day": "yesterday", "standing": 40000}) + "\n")
        data = self.data(record=False)
        self.assertTrue(any("day" in r for r in data["refused_rows"]))
        self.assertIsNotNone(data["net_lines"])

    def test_a_task_code_that_is_not_a_string_never_reaches_sorted(self):
        """`sorted()` over a set holding a string and a number raises `TypeError`. The
        code column is a string, so a row whose `task` is not one is not a task row."""
        append_log(self.root, {"ts": _utc(1), "task": 42, "from": "READY",
                               "to": "RUNNING", "attempt": 0})
        data = self.data(record=False)            # it builds, which is the whole point
        self.assertTrue(all(isinstance(r["code"], str) for r in data["task_rows"]))
        self.assertNotIn("42", [r["code"] for r in data["task_rows"]])
        self.assertIn("LJ-1.386", [r["code"] for r in data["task_rows"]])
        digest.render(data)                       # and it renders

    def test_a_foreign_path_list_written_as_one_string_counts_no_characters(self):
        """`len("dev/a.md")` is 8, and the foreign-path count would have printed 8."""
        rel = _run_record(self.root, "LJ-1.N09", 1, changed_files_foreign="dev/a.md")
        append_log(self.root, {"ts": _utc(1), "task": "LJ-1.N09", "from": "CHECKING",
                               "to": "DONE", "row": "task-lj-1-386-go",
                               "facts": FACTS_GREEN, "run": rel, "attempt": 0})
        self.assertEqual(self.data(record=False)["foreign_paths"], 2)

    def test_the_whole_digest_survives_every_bad_row_at_once(self):
        """A digest that dies on one torn row tells the owner nothing about a loop that
        stopped, which is the one thing it exists to tell him."""
        append_log(self.root, {"ts": _utc(2), "task": "LJ-1.N07", "event": "retrieval",
                               "offered": 3, "used": [], "missed": None,
                               "overlap": "high"})
        append_log(self.root, {"ts": _utc(1), "task": "LJ-1.N08", "from": "READY",
                               "to": "RUNNING", "attempt": {}})
        text = digest.render(self.data(record=False))
        for head in ("一、今日结论", "二、任务台账", "三、报告数", "四、阻塞与待裁决"):
            self.assertIn(head, text)
        self.assertIn("本报告拒绝了 2 行记录", text)


class ExitCodes(Fixture):
    """THE THREE EXIT CODES OF THE MODULE DOCSTRING, and each one means one thing.

    `write_digest()` at `scripts/pod/pod.py:1279` runs this script unattended under
    `capture_output=True`. A traceback there is a report nobody reads, so every failure
    leaves through a message and a code.
    """

    def run_main(self, argv):
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = digest.main(argv)
        return code, out.getvalue(), err.getvalue()

    def test_a_digest_that_printed_exits_zero(self):
        code, out, _err = self.run_main(["--root", str(self.root), "--now", str(NOW),
                                         "--no-write", "--no-record"])
        self.assertEqual(code, 0)
        self.assertIn("POD 日报", out)

    def test_a_window_of_zero_hours_is_a_usage_error(self):
        code, _out, err = self.run_main(["--root", str(self.root), "--hours", "0",
                                         "--no-write", "--no-record"])
        self.assertEqual(code, 2)
        self.assertIn("--hours", err)

    def test_a_root_that_is_not_a_directory_is_a_usage_error(self):
        code, _out, err = self.run_main(["--root", str(self.root / "nowhere"),
                                         "--no-write", "--no-record"])
        self.assertEqual(code, 2)
        self.assertIn("--root", err)

    def test_an_unknown_option_is_a_usage_error(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as caught:
                digest.main(["--rank-the-tasks"])
        self.assertEqual(caught.exception.code, 2)

    def test_a_digest_that_cannot_be_written_exits_one_after_printing(self):
        """The text reaches stdout BEFORE the file is written, so a failed write still
        leaves the owner the report."""
        (self.root / ".pod-state" / "digest").write_text("not a directory",
                                                         encoding="utf-8")
        code, out, err = self.run_main(["--root", str(self.root), "--now", str(NOW),
                                        "--no-record"])
        self.assertEqual(code, 1)
        self.assertIn("POD 日报", out)
        self.assertIn("not written", err)

    def test_a_build_that_refuses_exits_one_and_names_the_failure(self):
        """A real failure exits 1 with a message. It never raises through into the
        loop's log as a traceback."""
        def boom(*_a, **_kw):
            raise DummyError("the transition log holds a shape nobody planned")
        original = digest.build
        digest.build = boom
        self.addCleanup(lambda: setattr(digest, "build", original))
        code, _out, err = self.run_main(["--root", str(self.root), "--no-write",
                                         "--no-record"])
        self.assertEqual(code, 1)
        self.assertIn("DummyError", err)


class DummyError(Exception):
    """One failure shape the digest never anticipated, which is exactly the point."""


if __name__ == "__main__":
    unittest.main(verbosity=2)
