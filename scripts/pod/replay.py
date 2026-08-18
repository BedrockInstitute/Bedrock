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
admission against an empty corpus is visible. `--seed` below is what ends that state.

CORPUS BALANCE, section 4.5.3, IS `check_balance()` AND IT RUNS INSIDE `replay()`. A row
whose `when` block names an error class the corpus does not hold is a row no record can
regress-test, so R3 would certify it as safe on no evidence at all. That row is REFUSED,
by name. The check is INERT while the corpus is empty, because a corpus of no records
holds no class and would otherwise refuse every row on day one. It reads only rows the
new table ADDS or CHANGES, so a row already in the table is never refused for a class it
has always named.

THE SEED IS `--seed`, AND IT IS HALF OF DAY 4. Section 4.5.2 gives the corpus two seed
streams and this mode builds the first: it runs every tracked live probe under Agda and
writes one `probe-rerun` record per file. **THE SECOND HALF IS NOT BUILT AND NOT HIDDEN.**
Section 4.5.3 also owes one MEASURED record per RUNNER class, made by failing each of
acceptance conjuncts 2 to 6 on purpose and running the acceptance runner over it. Nothing
in this file produces those five records. Until they land the corpus holds Agda classes
only, and `check_balance()` refuses a NEW row that names `obligations_up`,
`closure_open`, `unbound_hyp`, `spec_surface` or `lint`. The refusal names the class, so
the gap says what it needs rather than hiding as a silent pass.

Usage:
  replay.py --count                     print the live and the retired record count
  replay.py --check <new-table.toml>    replay the live table against a proposed one
  replay.py --seed [options]            run every tracked live probe and write its record
    --out PATH                          write there instead of the tracked corpus
    --limit N                           stop after N files, for a cheap rehearsal
    --deadline S                        the per-file Agda deadline, 300 s by default
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

    ONE LIMIT, STATED AND NOT HIDDEN. `admit_rows()` catches `TableError` and returns
    False, so on the ADMISSION path the message above is dropped and the task parks with
    `reason: "admission"` and no class name. The maintainer batch path keeps the message.
    Widening `admit_rows()` to carry a reason is a change to `scripts/pod/table.py` and
    this file does not make it.
    """
    held = corpus_classes(records_in)
    if not held:
        return                               # INERT. An empty corpus holds no class.
    for row in _new_rows(old_table, new_table):
        when = row.get("when") or {}
        named = []
        if isinstance(when.get("error_class"), str):
            named.append(when["error_class"])
        named += [c for c in (when.get("error_class_in") or []) if isinstance(c, str)]
        for cls in named:
            if cls not in held:
                raise table.TableError(
                    f"row `{row['id']}` names the error class `{cls}`, which the corpus "
                    f"does not hold. The corpus holds {sorted(held)}. Section 4.5.3: a "
                    f"row no record can regress-test is not admitted, because R3 would "
                    f"pass it on no evidence. Seed a record of that class first.")


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


# ---------------------------------------------------------------- the seed, section 4.5.2

#: The per-file Agda deadline of section 4.5.2. A probe that has not finished in five
#: minutes gives the class `timeout`, which is a valid fixture and not a lost record.
SEED_DEADLINE_S = 300

#: The seed runs ONE Agda process at a time. `matches()` refuses a seconds key against a
#: record whose `concurrency` is not 1, so a parallel seed would produce records no row
#: could ever read on time.
SEED_CONCURRENCY = 1


def live_probe_files(root=None):
    """Every TRACKED `.agda` and `.lagda.md` file under `agents/tasks/`, archive excluded.

    THE ARCHIVE IS EXCLUDED AND THE REASON IS MEASURED, section 4.5.2. The 221 archived
    probes import from `archive/src/`, which `bedrock.agda-lib` does not put on the
    include path, so every one of them buckets to a single scope error and the corpus
    would learn one class 221 times.

    IT ASKS GIT AND NEVER THE FILESYSTEM. An untracked probe is not a record the project
    keeps, and W4 says a tracked probe is never deleted, so the tracked set is the stable
    one.
    """
    import subprocess                                              # noqa: PLC0415
    root = ROOT if root is None else Path(root)
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", "agents/tasks/*.agda", "agents/tasks/*.lagda.md"],
        cwd=root, capture_output=True, text=True, check=False)
    if out.returncode != 0:
        raise table.TableError(f"git ls-files failed under {root}: {out.stderr.strip()}")
    rels = [r for r in out.stdout.split("\0") if r]
    return [r for r in rels if not r.startswith("agents/tasks/archive/")]


def _seed_id(rel):
    """A stable id for one probe rerun, so a second seed appends nothing twice."""
    import hashlib                                                 # noqa: PLC0415
    return "pr-" + hashlib.sha256(rel.encode("utf-8")).hexdigest()[:12]


def _task_of(rel):
    """The task code a probe path carries: `agents/tasks/LJ-1-141/P.agda` gives `LJ-1-141`.

    A file sitting directly under `agents/tasks/` belongs to no task directory, and
    `check_record()` refuses an empty `task`, so it takes the literal `unknown` rather
    than a code invented from the file name.
    """
    parts = rel.split("/")
    return parts[2] if len(parts) > 3 else "unknown"


def seed_record(rel, run, tier):
    """One `probe-rerun` corpus record, from one Agda run over one probe.

    THREE FACTS ARE FIXED BY THE SEED'S OWN SHAPE and none of them is guessed. Fact 3,
    `obligations_delta`, is 0 because a rerun resolves nothing. Fact 4, `changed_files`,
    is empty because a rerun writes nothing. Facts 1, 2, 5 and 6 are the run's own.

    A5 IS WHY FACT 1 IS AGDA'S HERE AND NOT THE RUNNER'S. Section 4.5.2 rules that the
    seed runs acceptance conjunct 1 per probe and conjuncts 2 to 6 ONCE, so a per-probe
    record can only carry conjunct 1's exit code, and this function never pretends
    otherwise.
    """
    import facts as facts_mod                                      # noqa: PLC0415
    return {"id": _seed_id(rel), "task": _task_of(rel), "provenance": "probe-rerun",
            "path": rel, "caliber": facts_mod.caliber_of(tier), "tier": tier,
            "concurrency": SEED_CONCURRENCY,
            "facts": {"exit_code": run["rc"], "error_class": run["agda_class"],
                      "obligations_delta": 0, "changed_files": [],
                      "seconds": run["seconds"], "heap_wall": run["heap_wall"]}}


def seed(out=None, limit=None, deadline_s=SEED_DEADLINE_S, dry_run=False, root=None):
    """Day 4's first seed stream. It APPENDS and never rewrites, which is clause W4.

    IT IS IDEMPOTENT BY ID. A file whose `pr-` id is already in the target file is
    skipped, so an interrupted seed resumes where it stopped and a second full run writes
    nothing. That matters because the full run is 426 Agda processes.

    IT WRITES THE RECORD AS SOON AS IT MEASURES IT, one line at a time with an fsync.
    A seed that held 426 records in memory and wrote them at the end would lose every
    measurement to one interruption, and each one costs an Agda run.

    THE PRICE IS NOT MEASURED HERE AND THIS DOCSTRING DOES NOT INVENT ONE. Section 4.5.2
    calls it a projection that gap m1's probe settles. Use `--limit` first and read the
    real seconds before you fund the whole run.
    """
    import facts as facts_mod                                      # noqa: PLC0415
    root = ROOT if root is None else Path(root)
    path = Path(out) if out else CORPUS
    tier = facts_mod.DEFAULT_TIER
    rels = live_probe_files(root)
    if limit is not None:
        rels = rels[:limit]
    seen = {r["id"] for r in records(path, retired=True)} if path.is_file() else set()
    written, skipped = 0, 0
    for rel in rels:
        rid = _seed_id(rel)
        if rid in seen:
            skipped += 1
            continue
        if dry_run:
            print(f"would seed {rid} {rel}")
            written += 1
            continue
        run = facts_mod.run_agda(rel, root, deadline_s, SEED_CONCURRENCY, tier=tier)
        rec = check_record(seed_record(rel, run, tier), where=rel)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(rec, sort_keys=True, default=str) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
        written += 1
        print(f"seeded {rid} {rel}: exit_code {run['rc']}, "
              f"error_class {run['agda_class']}, {run['seconds']} s")
    print(f"seed: {written} record(s) written, {skipped} already present, "
          f"{len(rels)} file(s) considered")
    return written


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
        if argv[0] == "--seed":
            opt, rest = {}, argv[1:]
            while rest:
                k = rest.pop(0)
                if k == "--dry-run":
                    opt["dry_run"] = True
                elif k in ("--out", "--limit", "--deadline") and rest:
                    v = rest.pop(0)
                    opt[{"--out": "out", "--limit": "limit",
                         "--deadline": "deadline_s"}[k]] = v
                else:
                    print(f"seed: `{k}` is not one of --out, --limit, --deadline, "
                          f"--dry-run", file=sys.stderr)
                    return 2
            for k in ("limit", "deadline_s"):
                if k in opt:
                    opt[k] = int(opt[k])
            seed(**opt)
            return 0
    except table.TableError as e:
        print(f"REFUSED {e}", file=sys.stderr)
        return 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
