#!/usr/bin/env python3
"""The regression replay of AD10, and the frozen record corpus it runs over.

WHY THIS FILE EXISTS. A rule table that anybody may edit is a table that silently changes
what happened yesterday. The maintainer widens one `when` block to cover a new failure,
and that block now captures a record another row used to win: the routing of a past return
changes, nobody reads the change, and the table's history stops meaning anything.

R3 IS THE ANSWER, AND IT IS PURE ARITHMETIC. A new row must not move any record an
existing row already matches. `replay()` routes every frozen record through the OLD table
and the NEW table and compares the pair `(row_id, action)`. It needs no ground-truth
label, because it tests a CHANGE and never a correctness.

THREE RULES FOLLOW, and section 4.5.1 states each one:

- A record that MATCHED must keep the same `row_id` AND the same `action`.
- A record that did NOT match MAY become a match. Added coverage is the reason to add a
  row, so a new match is admitted.
- An EDIT is a remove plus an add, and the same test guards it. `admit_rows()` is an edit
  of exactly that shape, so R3 guards an admission as it guards a maintainer batch.

EXPIRY IS EXEMPT, and section 4.6 gives the reason. The router drops an expired row, so
expiry DOES move every record that row used to win. R3 forbids a maintainer from moving
traffic; it does not forbid a row from dying with its task. The replay uses the SAME
expiry state on both sides, so an expiry can never hide inside a table edit.

THE CORPUS IS BUILT FORWARD AND NEVER RECONSTRUCTED, section 4.5.3, and that is measured.
Facts 3 and 4 are reconstructible from history: 1,326 of 1,395 commits name a task code
and 298 of the 503 distinct codes also have a task directory. Facts 1, 2, 5 and 6 are not,
measured four ways: the dispatch registry's 14 fields over 469 records hold no fact;
`returns.log` holds one status word over 496 lines; the codex transcripts name `agda` in
6,508 shell blocks and only 48 end the command chain with the agda call, which is
0.7 percent; and the pi session store gives 73 Agda-shaped records over 127 files.

`check_record()` IS ALSO THE TYPE BOUNDARY, and one measured crash is why. A corpus line
whose `obligations_delta` held a string reached `table.matches()` and raised `TypeError`
on `>=`. `admit_rows()` catches `TableError` and `OSError`, so that raise escaped into the
unattended loop as a traceback. The shape test and the type test now sit together, in one
function, and `matches()` states that it validates nothing.

DAY ONE THE CORPUS IS EMPTY, AND THE CONSEQUENCE IS STATED RATHER THAN HIDDEN. `replay()`
iterates the corpus, so an empty corpus returns `("ADMIT", [])` for every table and R3
guards nothing until the first record lands. The digest prints the record count, so an
admission against an empty corpus is visible.

Usage:
  replay.py --count                     print the live and the retired record count
  replay.py --check <new-table.toml>    replay the live table against a proposed one
Exit status: 0 ADMIT, 1 REJECT or a refusal, 2 usage error.
"""

from __future__ import annotations

import json
import sys
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

import table  # noqa: E402

ROOT = find_root(__file__)
CORPUS = ROOT / "dev" / "pod" / "replay-corpus.jsonl"

#: `provenance` takes one of three values, section 4.5.2. `live` is `emit()`'s own stream
#: and IS the corpus in steady state. `probe-rerun` is the seed. `report` is hand-loaded,
#: it must carry `source` as `file:line`, and it writes `"concurrency": null` unless the
#: report states the process count. NO FACT IS EVER GUESSED.
PROVENANCE = ("live", "probe-rerun", "report")

#: The TYPE of every fact, at the one boundary a record enters through. `None` in a tuple
#: means the fact may be null and says what null means:
#:   `exit_code`          null when conjunct 1's Agda deadline passed, section 4.3.
#:   `error_class`        null on a green run, which then matches no class key.
#:   `lines`              absent or null when the write scope was not counted (A10).
#: `bool` is a subclass of `int` in Python, so every integer test rejects `bool` first.
FACT_TYPES = {
    "exit_code": (int, type(None)),
    "error_class": (str, type(None)),
    "obligations_delta": (int,),
    "changed_files": (list,),
    "seconds": (int, float),
    "heap_wall": (bool,),
    table.FACT_KEY_A10: (int, type(None)),
}


def _bad_type(value, want) -> bool:
    """True when `value` is outside `want`. `bool` never counts as an integer."""
    if isinstance(value, bool) and bool not in want:
        return True
    return not isinstance(value, want)


def check_record(rec, where="record"):
    """One corpus or log record. The corpus line and the transition log line are ONE shape.

    `facts` HOLDS THE SIX KEYS, and `lines` may join them under amendment A10. Every other
    key is provenance and no `[row.when]` key names one, except `concurrency`, which
    `matches()` reads as a GUARD. A `facts` object of any other shape is refused, because
    a half-record with a guessed field would license a row no evidence supports and the
    replay would then certify that row as safe (R7, section 4.5.4).

    THIS IS THE ONE BOUNDARY, AND THE TYPE TEST BELONGS HERE. A fact carrying a STRING
    where a number belongs used to reach `table.matches()` and raise `TypeError` on `>=`:
    `admit_rows()` catches `TableError` and `OSError` and never a `TypeError`, so one
    malformed corpus line stopped the unattended loop with a traceback. Testing the type
    at each of the seventeen comparisons would put one rule in seventeen homes (W5), so
    the test is here, and `matches()` states that it validates nothing.
    """
    if not isinstance(rec, dict):
        raise table.TableError(f"{where}: is not an object")
    for k in ("id", "task", "facts"):
        if k not in rec:
            raise table.TableError(f"{where}: carries no `{k}`")
    for k in ("id", "task"):
        if not isinstance(rec[k], str) or not rec[k]:
            raise table.TableError(f"{where}: `{k}` is not a non-empty string")
    con = rec.get("concurrency")
    if con is not None and _bad_type(con, (int,)):
        raise table.TableError(f"{where}: `concurrency` is neither an integer nor null")
    f = rec["facts"]
    if not isinstance(f, dict):
        raise table.TableError(f"{where}: `facts` is not an object")
    missing = [k for k in table.FACT_KEYS if k not in f]
    if missing:
        raise table.TableError(f"{where}: `facts` carries no `{missing[0]}`")
    extra = [k for k in f if k not in table.FACT_KEYS and k != table.FACT_KEY_A10]
    if extra:
        raise table.TableError(f"{where}: `facts` carries `{extra[0]}`, not a fact")
    for k, want in FACT_TYPES.items():
        if k in f and _bad_type(f[k], want):
            raise table.TableError(
                f"{where}: `facts.{k}` is {f[k]!r}, which is not "
                f"{' or '.join(t.__name__ for t in want)}")
    for p in f["changed_files"]:
        if not isinstance(p, str):
            raise table.TableError(f"{where}: `facts.changed_files` holds {p!r}, "
                                   f"which is not a path")
    prov = rec.get("provenance")
    if prov is not None and prov not in PROVENANCE:
        raise table.TableError(f"{where}: provenance `{prov}` is not one of "
                               f"{list(PROVENANCE)}")
    if prov == "report" and not rec.get("source"):
        raise table.TableError(f"{where}: a report record carries no `source` file:line")
    return rec


def records(path=None, retired=False):
    """Every line of the corpus, live or all. It raises on a line that does not parse."""
    path = CORPUS if path is None else Path(path)
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return []
    out = []
    for n, line in enumerate(text.split("\n"), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError as e:
            raise table.TableError(f"{path}:{n} does not parse: {e}") from e
        if rec.get("retired") and not retired:
            continue                     # a retired record STAYS in the file and is skipped
        out.append(check_record(rec, f"{path}:{n}"))
    return out


def corpus(path=None):
    """Every frozen record the replay must not move. Order does not matter.

    A RECORD IS NEVER EDITED AND NEVER DELETED, which is clause W4 applied to a record. An
    obsolete record gets `"retired": true` and stays in the file, so the history of what
    the table used to do stays readable.
    """
    return records(path)


def replay(old_table, new_table, records_in):
    """ADMIT the new table, or REJECT it and name every record it moved. R3.

    The return is `("ADMIT", [])`, or `("REJECT", moved)` where each moved entry is
    `(record id, old row id, old action, new row id, new action)`. The caller prints it:
    a refusal that names no record teaches a maintainer nothing.
    """
    moved = []
    for rec in records_in:                   # each rec is one whole record
        old_id, old_act = table.route(old_table, rec)
        if old_id is None:
            continue                         # was NO MATCH. It MAY become a match.
        new_id, new_act = table.route(new_table, rec)
        if (new_id, new_act) != (old_id, old_act):
            moved.append((rec["id"], old_id, old_act, new_id, new_act))
    return ("ADMIT", []) if not moved else ("REJECT", moved)


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 2
    try:
        if argv[0] == "--count":
            live = len(records())
            every = len(records(retired=True))
            print(f"dev/pod/replay-corpus.jsonl: {live} live records, "
                  f"{every - live} retired")
            if live == 0:
                print("EMPTY. replay() returns ADMIT for every table and R3 guards "
                      "nothing until the first record lands.")
            return 0
        if argv[0] == "--check" and len(argv) > 1:
            old = table.load_table()
            new = table.load_table(argv[1])
            verdict, moved = replay(old, new, corpus())
            print(verdict)
            for row in moved:
                print("  moved {0}: {1} {2} -> {3} {4}".format(*row))
            return 0 if verdict == "ADMIT" else 1
    except table.TableError as e:
        print(f"REFUSED {e}", file=sys.stderr)
        return 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
