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
admission against an empty corpus is visible. The `live` stream is what ends that state:
`emit()` appends every routed record, so the corpus fills as real tasks return.

CORPUS BALANCE, section 4.5.3, IS `check_balance()` AND IT RUNS INSIDE `replay()`. A row
whose `when` block names an error class the corpus does not hold is a row no record can
regress-test, so R3 would certify it as safe on no evidence at all. That row is REFUSED,
by name. The check is INERT while the corpus is empty, because a corpus of no records
holds no class and would otherwise refuse every row on day one. It reads only rows the
new table ADDS or CHANGES, so a row already in the table is never refused for a class it
has always named.

THERE IS NO SEED ANY MORE, owner's ruling 2026-08-19. `--seed` re-ran 426 tracked probes
and wrote one `probe-rerun` record per file. **A probe is one-shot and afterwards it is a
static reference**: to use an old one you write a NEW probe informed by it, or you turn it
into live code. `AGENTS.md` says the same to every agent, that nothing typechecks a probe
once its task closes, and the seed was the only thing that ever did. See the retirement
note further down for what was removed and why.

**WHAT THE PROJECT STILL OWES IS THE OTHER HALF, AND IT NEEDS NO PROBE.** Section 4.5.3
owes one MEASURED record per RUNNER class, made by failing each of acceptance conjuncts 2
to 6 on purpose and running the acceptance runner over it, which doubles as that runner's
self-test. Nothing in this file produces those five records. Until they land, and until
the `live` stream has run, `check_balance()` refuses a NEW row that names
`obligations_up`, `closure_open`, `unbound_hyp`, `spec_surface` or `lint`. The refusal
names the class, so the gap says what it needs rather than hiding as a silent pass.

Usage:
  replay.py --count                     print the live and the retired record count
  replay.py --check <new-table.toml>    replay the live table against a proposed one
    --dry-run                           measure nothing, and print the file list only
Exit status: 0 ADMIT, 1 REJECT or a refusal, 2 usage error.
"""

from __future__ import annotations

import json
import os
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

#: `provenance` takes one of two values, section 4.5.2. `live` is `emit()`'s own stream
#: and IS the corpus in steady state. `report` is hand-loaded by the maintainer. The
#: third value, `probe-rerun`, was RETIRED on 2026-08-19 and is no longer legal: a record
#: carrying it is refused, which is correct, because no such record exists (the corpus was
#: 0 bytes when the seed went). See the retirement note further down.
PROVENANCE = ("live", "report")   # `probe-rerun` retired 2026-08-19, see below

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


def corpus_classes(records_in):
    """Every error class the corpus HOLDS. A green record holds none and is not counted."""
    return {r["facts"].get("error_class") for r in records_in} - {None}


def _new_rows(old_table, new_table):
    """Every row the new table ADDS or CHANGES, by id. An untouched row is not one.

    A row whose `when` block is unchanged has always named whatever class it names, and
    refusing it would refuse the table that is already running.
    """
    was = {r["id"]: r.get("when") for r in old_table}
    return [r for r in new_table if r["id"] not in was or was[r["id"]] != r.get("when")]


def check_balance(old_table, new_table, records_in):
    """Section 4.5.3's corpus balance. It RAISES `table.TableError`, naming the class.

    A row whose `when` block names an error class the corpus does not hold is a row NO
    record can regress-test. R3 would return ADMIT for it every time, and that ADMIT would
    read as evidence when it is only an empty corpus, which is exactly the false safety
    section 4.5.4 refuses elsewhere.

    IT IS INERT WHILE THE CORPUS IS EMPTY, and that is not a courtesy. An empty corpus
    holds no class at all, so an eager check would refuse every row the program ever
    admits, including the first. The digest's record count is what makes the inert period
    visible, exactly as it does for R3 itself.

    IT RAISES RATHER THAN RETURNING A VERDICT, because a balance failure moves NO record
    and has no `(record, old row, new row)` shape to report. Both callers already handle
    the raise: `harvest_batch()` turns it into one `result="refused"` batch line carrying
    this message, and `admit_rows()` catches `TableError` and parks the task.

    THE LIMIT THIS DOCSTRING USED TO STATE IS CLOSED, 2026-08-19. It said the ADMISSION
    path drops the message above, so a task parks with `reason: "admission"` and no class
    name, and that the cure belonged in `scripts/pod/table.py`. The cure was made there:
    `admit_rows()` records every refusal in `table.LAST_REFUSAL` and rule (f) writes it
    into the park's `detail`. MEASURED 2026-08-19: LJ-1.388 parked with `detail: None`,
    which is what sent the maintainer to read this paragraph in the first place.
    """
    for row in _new_rows(old_table, new_table):
        when = row.get("when") or {}
        named = []
        if isinstance(when.get("error_class"), str):
            named.append(when["error_class"])
        named += [c for c in (when.get("error_class_in") or []) if isinstance(c, str)]
        if not named:
            continue
        # **THE EVIDENCE IS THE EVIDENCE THIS ROW COULD EVER TOUCH, and not the whole
        # corpus.** `hits()` at `scripts/pod/table.py:575` admits a row into the routing
        # of ONE record only when the row is `system` or its scope is exactly
        # `task:<that record's task>`. So a brand-new task's rows cannot move any existing
        # record: every record in the corpus belongs to another code. For them R3 is
        # VACUOUS rather than falsely reassuring, and the paragraph above about「an ADMIT
        # that reads as evidence」does not apply, because there is nothing to certify.
        #
        # THE INERT RULE IS UNCHANGED, IT IS ONLY MEASURED PER SCOPE. An empty corpus made
        # the whole check inert for the same reason: no evidence can be had, so demanding
        # it refuses the first row for ever.
        #
        # MEASURED 2026-08-19, and this is the deadlock it breaks: the corpus held one
        # class, `spec_surface`, from LJ-1.386's stop. LJ-1.388's brief named
        # `unsolved_meta`, so admission parked it. To hold an `unsolved_meta` record the
        # program must first CLOSE a task on that class, and to run that task it must
        # first admit these rows. A system row still faces the whole corpus, which is
        # where the gate has teeth and where backlog item 5's records are still owed.
        scope = row.get("scope")
        if scope == "system":
            seen = records_in
        else:
            code = str(scope or "")[len(table.SCOPE_TASK):]
            seen = [r for r in records_in if r.get("task") == code]
        held = corpus_classes(seen)
        if not held:
            continue                         # INERT for this scope: no evidence to have
        for cls in named:
            if cls not in held:
                raise table.TableError(
                    f"row `{row['id']}` names the error class `{cls}`, which the corpus "
                    f"does not hold for scope `{scope}`. It holds {sorted(held)}. "
                    f"Section 4.5.3: a row no record can regress-test is not admitted, "
                    f"because R3 would pass it on no evidence. Seed a record of that "
                    f"class first.")


def replay(old_table, new_table, records_in):
    """ADMIT the new table, or REJECT it and name every record it moved. R3.

    The return is `("ADMIT", [])`, or `("REJECT", moved)` where each moved entry is
    `(record id, old row id, old action, new row id, new action)`. The caller prints it:
    a refusal that names no record teaches a maintainer nothing.

    IT ALSO RAISES on a corpus-balance failure, section 4.5.3, which is a REFUSAL and not
    a moved record. `check_balance()` above carries the reason and the inert period.
    """
    check_balance(old_table, new_table, records_in)      # section 4.5.3, before R3
    moved = []
    for rec in records_in:                   # each rec is one whole record
        old_id, old_act = table.route(old_table, rec)
        if old_id is None:
            continue                         # was NO MATCH. It MAY become a match.
        new_id, new_act = table.route(new_table, rec)
        if (new_id, new_act) != (old_id, old_act):
            moved.append((rec["id"], old_id, old_act, new_id, new_act))
    return ("ADMIT", []) if not moved else ("REJECT", moved)


# ------------------------------------------------- the retired seed, section 4.5.3

#: THE `probe-rerun` SEED IS RETIRED, owner's ruling 2026-08-19.
#:
#: **A PROBE IS ONE-SHOT AND AFTERWARDS IT IS A STATIC REFERENCE.** The owner's words:
#: to use an old probe you either write a NEW probe informed by it, or you turn it into
#: live code. Re-running one to build a regression fixture is a category error, and
#: `AGENTS.md` already told every agent the same thing: "`src/` is forbidden for a probe.
#: Nothing typechecks it once your task closes, so run it while you can." **The seed was
#: the only thing in the project that ever re-ran one.**
#:
#: WHAT WAS HERE: `SEED_DEADLINE_S`, `SEED_CONCURRENCY`, `live_probe_files()`,
#: `_seed_id()`, `_task_of()`, `seed_record()`, `seed()` and the `--seed` command, about
#: 130 lines. Section 4.5.3 of the design memo carries the reasoning that put them there,
#: which was an argument from exhaustion: the dispatch registry, `returns.log`, the codex
#: transcripts and the pi session store were each measured and each held no usable Agda
#: exit code, so probes were the last remaining source of one.
#:
#: AND IT WAS ALREADY BROKEN. `seed()` never passed `include=` to `run_agda()`, so every
#: probe failed at module resolution and bucketed to one class. That is the SAME failure
#: the design used to justify excluding the 221 archived probes: "the corpus would learn
#: one class 221 times." MEASURED 2026-08-19 over five probes before the run was stopped.
#:
#: WHAT ARMS R3 INSTEAD: the `live` stream, which section 4.5.3 already calls the corpus
#: in steady state, plus the half of day 4 that was never built, one MEASURED record per
#: RUNNER class made by failing acceptance conjuncts 2 to 6 on purpose. That half needs
#: no probe.


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
        # A RETIRED COMMAND ANSWERS FOR ITSELF. Falling through to the usage text would
        # tell a reader that `--seed` never existed, and 130 lines of this file plus a
        # section of the design memo say otherwise.
        if argv[0] == "--seed":
            print("replay.py: `--seed` is RETIRED, owner's ruling 2026-08-19. It re-ran "
                  "426 tracked probes to build the corpus, and a probe is one-shot: "
                  "afterwards it is a static reference, so to use an old one you write a "
                  "NEW probe informed by it or you turn it into live code. AGENTS.md "
                  "already says nothing typechecks a probe once its task closes.\n"
                  "The corpus now fills from the `live` stream as real tasks return. The "
                  "one thing still owed is a MEASURED record per RUNNER class, made by "
                  "failing acceptance conjuncts 2 to 6 on purpose; it needs no probe.",
                  file=sys.stderr)
            return 2
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
