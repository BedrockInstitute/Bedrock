#!/usr/bin/env python3
"""The ONE rule table of AD8, its loader, the router, the replay and the admission.

WHY THIS FILE EXISTS. The old flow routed a return by reading prose: the orchestrator
read a report, decided what it meant, and wrote the next brief. The measured failure is
`[LJ-1.375]` and `[LJ-1.376]` on 2026-08-16: a verdict LINE disagreed with its own BODY,
and the audit named the orchestrator's own unread live record the costliest defect in the
tree. A router that reads six measured facts and one closed key list cannot read a report
wrongly, because it never reads one.

WHAT EACH RULE HERE COSTS IF IT IS DROPPED
(`dev/memos/LJ-4-pod-program-design.md` sections 4.1 to 4.6):

- **The loader refuses an unknown key.** A typo in a `[row.when]` block would otherwise
  become a silent no-match row: the row loads, it never fires, and the maintainer reads
  the table as covered.
- **R1, the six facts and nothing else.** `matches()` raises on any other key. The loader
  catches it first, so the raise is an alarm and never a routine path.
- **R3, the replay.** A new row must not move a record an existing row already matches.
  `admit_rows()` runs it BEFORE it writes, so a brief cannot capture another row's
  traffic. Expiry is exempt, because a row that dies with its task is not a maintainer
  moving traffic.
- **A3, `stop_loop` sorts first.** `sys-spec-surface` is a system row. A task branch that
  reads only `seconds_min` and `changed_files_count_max` matches the same record and
  never mentions fact 1, so without A3 that branch outranks the system row and the loop
  keeps running through a change to the trophy statement.
- **The scope guard.** `route()` reads a `task:<CODE>` row only for its own task, so one
  task's rows can never grade another task's return.
- **Idempotent admission.** A second instance re-writes nothing. Without it every retry
  would rewrite the tracked table and every rewrite is a commit.
- **The concurrency guard.** No `[row.when]` key names `concurrency`; it can only make a
  seconds key FAIL. A contended cold gate measured 150.09 s against 133.69 s, so a
  seconds comparison across process counts is worse than no comparison.

AMENDMENT A10, AND THE KEY NAMES ARE THIS FILE'S PICK. The owner ruled on 2026-08-17 that
DD24 is NOT superseded and that its RATIO form is restored, seconds over in-fence lines
(`dev/memos/LJ-4-pod-program-design.md:71-77`). That amendment names the FACT, `lines`, and
it names NO `[row.when]` key; section 4.3's key table names none either. **So this file
picks ONE pair, `seconds_per_line_min` and `seconds_per_line_max`, and says so here.** The
bar is a QUOTIENT, and no pair of raw keys can express a quotient. This file adds no
`lines_min` and no `lines_max`: fact 7 exists to carry the divisor, a key that no ruled
bar needs is a key every maintainer must still read, and the closed list is the one thing
that keeps R1 cheap.

WHERE A RECORD IS CHECKED, and it is ONE place. `replay.check_record()` is the boundary:
it refuses a record whose shape or whose fact TYPES are wrong, and every reader of the
corpus and of `--route` passes through it. **`matches()` compares and never validates.** A
string-valued fact reaching `>=` raises `TypeError`, and that traceback stops an
unattended loop with nobody watching, so the type test belongs at the boundary and not at
each of the seventeen comparisons.

WHAT THIS MODULE DOES NOT DO. It never runs Agda, it never reads a report, and it never
decides an action. `scripts/pod/facts.py` measures; this file compares. The eight actions
are performed by `scripts/pod/pod.py` (section 5.1), which day 5 builds.

Usage:
  table.py --check                 load `dev/pod/table.toml` and print every refusal
  table.py --route <record.json>   print the row id and the action for one record
  table.py --rows [<scope>]        print one line per row, in router order
Exit status: 0 clean, 1 a refusal or NO MATCH, 2 usage error.
"""

from __future__ import annotations

import datetime
import fnmatch
import json
import os
import re
import subprocess
import sys
import tomllib
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

ROOT = find_root(__file__)
TABLE = ROOT / "dev" / "pod" / "table.toml"
HEADS = ROOT / "dev" / "pod" / "heads.toml"

SCHEMA = 1

#: Section 4.2 bumps `vocab` when the fact set changes, and amendment A10 changed it: fact
#: 7 `lines` joined the six of AD11. A table written for `six-facts/1` is refused by this
#: loader, which is the point of the field: a router that reads a table written for
#: another fact set routes a return by a vocabulary its author never agreed to.
#: **A23 ADDS FACT 8, `obligations_open`, THE UNRESOLVED COUNT AT EXIT.** Fact 3 is a
#: DIFFERENCE, and a difference cannot separate a finished task from an idle one: 0 before
#: and 0 after reads exactly like 5 and 5. Every `done` row therefore had to key on
#: `obligations_delta_max`, which fires only on the ONE instance that discharges the
#: names, so a re-run, a review and a mathematician's return were each complete and unable
#: to close. MEASURED 2026-08-19: five tasks parked `no-match` in one afternoon by three
#: legitimate routes, all reading `exit_code 0`, `error_class None`, `obligations_delta 0`.
VOCAB = "eight-facts/1"

#: The eight actions of section 4.2. The set is CLOSED, so the program makes no judgement,
#: and every one names the function that performs it in `scripts/pod/pod.py`.
ACTIONS = ("done", "accept", "park", "park_and_split", "redispatch",
           "redispatch_narrower", "escalate", "stop_loop")

#: The two `outcome` values. `outcome` is a declaration and NEVER a matcher: it sits
#: outside `[row.when]`, the router never reads it, and pre-flight P19 admits a `no-go`
#: close under A6 because a NO-GO leaves every declared name unresolved.
OUTCOMES = ("go", "no-go")

ADDED_BY = ("maintainer", "owner", "mathematician")

#: Every admitted row key, in EMITTED order. `write_table()` prints them in this order, so
#: a re-write of an unchanged table is a byte-identical file.
ROW_KEYS = ("id", "scope", "priority", "action", "head_slot", "outcome",
            "added", "added_by", "reason", "expired", "expired_at", "when")
ROW_REQUIRED = ("id", "scope", "priority", "action", "added", "added_by", "reason", "when")

#: Every admitted BRANCH key. A brief writes a branch; admission turns it into a row and
#: fills `scope`, `added`, `added_by` and `reason` itself, so a branch carries none of
#: those four. An unknown branch key is a refusal, which is the safe direction: the
#: alternative is a key the author believes routes and that nothing reads.
BRANCH_KEYS = ("id", "priority", "action", "outcome", "head_slot", "when")

#: The six facts of AD11, and `lines` is fact 7 under amendment A10. The `facts` object of
#: a record carries the six ALWAYS and `lines` when the task's write scope was counted.
FACT_KEYS = ("exit_code", "error_class", "obligations_delta", "changed_files",
             "seconds", "heap_wall")
FACT_KEY_A10 = "lines"
#: Fact 8, amendment A23. OPTIONAL exactly as `lines` is: a record written before this
#: amendment does not carry it, is never migrated and is never guessed, and `matches()`
#: below refuses every `obligations_open` key against such a record. R7: the program never
#: guesses a fact, so an old record simply cannot open a row that keys on a new one.
FACT_KEY_A23 = "obligations_open"

#: Every `[row.when]` key, in EMITTED order, with its value type. The list is CLOSED:
#: R1 says a branch matches only the facts of AD11, and pre-flight P4 refuses a key that
#: is not here. `int` admits `bool` in Python, so the checker tests `bool` first.
WHEN_TYPES = {
    "exit_code": int,
    "exit_code_in": list,
    "exit_code_absent": bool,
    "error_class": str,
    "error_class_in": list,
    "obligations_delta_min": int,
    "obligations_delta_max": int,
    "changed_files_any": list,
    "changed_files_none": list,
    "changed_files_all_within": list,
    "changed_files_count_min": int,
    "changed_files_count_max": int,
    "seconds_min": float,
    "seconds_max": float,
    "heap_wall": bool,
    # AMENDMENT A10, fact 7. DD24 is NOT superseded and its RATIO form is restored, so a
    # seventh key is admitted. THE PAIR BELOW IS THIS FILE'S PICK, disclosed in the module
    # docstring: A10 names the FACT (`lines`, the in-fence line count of the task's own
    # write scope) and names no key, and section 4.3's table names none. ONE pair is
    # admitted, and it is the quotient, because that is the form the ruled bar takes.
    "seconds_per_line_min": float,
    "seconds_per_line_max": float,
    "obligations_open_min": int,
    "obligations_open_max": int,
}
WHEN_KEYS = tuple(WHEN_TYPES)

#: The list-valued keys and the element type each admits.
LIST_ELEMENT = {"exit_code_in": int, "error_class_in": str,
                "changed_files_any": str, "changed_files_none": str,
                "changed_files_all_within": str}

REASON_MAX = 200
ID_FORM = re.compile(r"[a-z0-9]+(-[a-z0-9]+)*\Z")
SCOPE_TASK = "task:"
BRANCH_FENCE = re.compile(r"^```toml\s+pod-branches\s*$(.*?)^```\s*$", re.M | re.S)
BRANCH_HEAD = re.compile(r"^\s*\[\[branch\]\]\s*(?:#\s*(?P<note>.*?))?\s*$", re.M)

#: The header `write_table()` re-emits. The table is a PROGRAM-WRITTEN file: `admit_rows()`
#: and `expire_rows()` rewrite it whole, so a hand-written comment inside it would be lost
#: at the first admission. One constant header keeps the file self-describing and keeps
#: the re-write byte-identical when no row changed.
HEADER = """\
# The ONE rule table of AD8. The router reads this file and nothing else.
#
# THIS FILE IS PROGRAM-WRITTEN. `admit_rows()` appends a task's branches at admission and
# `expire_rows()` retires them at close, both through `write_table()` in
# `scripts/pod/table.py`, which rewrites the whole file. A comment added by hand inside it
# does not survive the next write. The header you are reading is a constant in that file.
#
# WHAT A ROW IS. One `[row.when]` block of the six facts of AD11 (plus fact 7 `lines`
# under amendment A10), AND-ed, with no OR. The row's `action` is one of the eight closed
# names of section 4.2. `outcome` never routes: it declares what a `done` close earns.
#
# HOW A CONFLICT IS DECIDED, section 4.4, and no judgement is involved:
#   1. `stop_loop` first, whatever the scope. Amendment A3.
#   2. then a `task:<CODE>` row before a `system` row.
#   3. then `priority` ascending.
#   4. then `id` ascending by byte order.
#
# A ROW IS NEVER DELETED, which is clause W4 applied to a table row. A task row that
# retires carries `expired = true` and `expired_at`; the router skips it and the file
# keeps it, because it records why one task routed differently.
#
# R3: a new row must not move any record an existing row already matches. `replay()` runs
# over `dev/pod/replay-corpus.jsonl` before every write. Expiry is exempt.
"""


class TableError(Exception):
    """The table, a branch block or a corpus record is malformed. NOTHING is guessed.

    Every raise here is a refusal with a reason. `admit_rows()` catches it and returns
    False, rule (f) parks the task with `reason: "admission"`, and no row enters the file.
    """


# ---------------------------------------------------------------- heads


def head_slots(root=None) -> tuple[str, ...]:
    """The slot NAMES of `dev/pod/heads.toml`, and only the names.

    THIS IS NOT THE HEAD LOADER of section 6.1. That loader resolves a model, an effort,
    a harness and a sandbox, and it refuses a value outside `legal.models` or
    `legal.efforts`. The table and the pre-flight need one thing from that file, the set
    of legal `head_slot` values, so this reader takes that and leaves the resolution with
    its own owner. Two readers of one file are admissible; two owners of one rule are not.
    """
    path = (ROOT if root is None else Path(root)) / "dev" / "pod" / "heads.toml"
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as e:
        raise TableError(f"dev/pod/heads.toml is unreadable: {e}") from e
    heads = data.get("heads")
    if not isinstance(heads, dict) or not heads:
        raise TableError("dev/pod/heads.toml carries no [heads] table")
    return tuple(heads)


# ---------------------------------------------------------------- the loader


def _refuse(where: str, msg: str):
    raise TableError(f"{where}: {msg}")


def _check_when(when, where, slots=None):
    """R1 and the closed key list. An empty block would match EVERY record, so it is
    refused; a wrong value type is refused for the same reason a wrong key is."""
    if not isinstance(when, dict) or not when:
        _refuse(where, "the [when] block is empty or is not a table")
    for k, v in when.items():
        if k not in WHEN_TYPES:
            _refuse(where, f"matches on `{k}`, which is not one of the "
                           f"{len(WHEN_TYPES)} admitted keys (R1)")
        want = WHEN_TYPES[k]
        if want is bool and not isinstance(v, bool):
            _refuse(where, f"`{k}` takes true or false, not {v!r}")
        if want is int and (isinstance(v, bool) or not isinstance(v, int)):
            _refuse(where, f"`{k}` takes an integer, not {v!r}")
        if want is float and (isinstance(v, bool) or not isinstance(v, (int, float))):
            _refuse(where, f"`{k}` takes a number, not {v!r}")
        if want is str and not isinstance(v, str):
            _refuse(where, f"`{k}` takes a string, not {v!r}")
        if want is list:
            if not isinstance(v, list) or not v:
                _refuse(where, f"`{k}` takes a non-empty list, not {v!r}")
            el = LIST_ELEMENT[k]
            for item in v:
                if el is int and (isinstance(item, bool) or not isinstance(item, int)):
                    _refuse(where, f"`{k}` holds {item!r}, which is not an integer")
                if el is str and not isinstance(item, str):
                    _refuse(where, f"`{k}` holds {item!r}, which is not a string")


def check_row(row, slots=None, where=None):
    """One row, or one namespaced branch, against section 4.2. It RETURNS a clean row.

    The two conditional fields are the reason this is one function and not two checks.
    `head_slot` is required exactly when `action` is `escalate` and is absent otherwise;
    `outcome` is required exactly when `action` is `done`. A row carrying both would be
    illegal, and pre-flight P11 tests the same two directions on a brief.
    """
    where = where or f"row `{row.get('id', '?')}`"
    unknown = [k for k in row if k not in ROW_KEYS]
    if unknown:
        _refuse(where, f"carries the unknown key `{unknown[0]}`")
    missing = [k for k in ROW_REQUIRED if k not in row]
    if missing:
        _refuse(where, f"has no `{missing[0]}`")
    rid = row["id"]
    if not isinstance(rid, str) or not ID_FORM.match(rid):
        _refuse(where, f"id `{rid}` is not kebab-case")
    scope = row["scope"]
    if scope != "system" and not (isinstance(scope, str) and scope.startswith(SCOPE_TASK)
                                  and len(scope) > len(SCOPE_TASK)):
        _refuse(where, f"scope `{scope}` is neither `system` nor `task:<CODE>`")
    pri = row["priority"]
    if isinstance(pri, bool) or not isinstance(pri, int) or pri < 0:
        _refuse(where, f"priority `{pri}` is not an integer at or above zero")
    action = row["action"]
    if action not in ACTIONS:
        _refuse(where, f"names the action `{action}`, which is not one of the eight")
    if action == "escalate":
        if "head_slot" not in row:
            _refuse(where, "escalates and carries no head_slot")
    elif "head_slot" in row:
        _refuse(where, f"carries a head_slot but its action is `{action}`")
    if "head_slot" in row:
        legal = head_slots() if slots is None else slots
        if row["head_slot"] not in legal:
            _refuse(where, f"head slot `{row['head_slot']}` is not in heads.toml")
    if action == "done":
        if "outcome" not in row:
            _refuse(where, "closes the task and carries no outcome")
    elif "outcome" in row:
        _refuse(where, f"carries an outcome but its action is `{action}`")
    if "outcome" in row and row["outcome"] not in OUTCOMES:
        _refuse(where, f"outcome `{row['outcome']}` is neither `go` nor `no-go`")
    if not isinstance(row["added"], datetime.date):
        _refuse(where, "`added` is not a TOML local date")
    if row["added_by"] not in ADDED_BY:
        _refuse(where, f"added_by `{row['added_by']}` is not one of {list(ADDED_BY)}")
    # `stop_loop` IS THE OWNER'S ACTION AND NO MODEL'S, ruled 2026-08-19.
    #
    # **THE GUARD THAT WAS SUPPOSED TO COVER THIS IS INERT.** R3 admission replays a
    # candidate table against `dev/pod/replay-corpus.jsonl`, and that file is 0 bytes:
    # `replay.py --count` prints「EMPTY. replay() returns ADMIT for every table and R3
    # guards nothing until the first record lands.」The emptiness is a documented day-one
    # state (`replay.py:41-44`), but it means any model could land a row that halts the
    # whole programme with nothing checking it. Two model paths reach here: a maintainer
    # proposal through `harvest_batch()`, and a mathematician's `[[branch]]` block through
    # `admit_rows()`, which stamps `added_by = "mathematician"` at :649.
    #
    # **AND SEEDING THE CORPUS WOULD NOT HAVE CLOSED IT.** R3 rejects a table that MOVES a
    # frozen record; a `stop_loop` row keyed on a class no record carries moves nothing and
    # is admitted either way.
    #
    # A model that wants a halt has a channel with teeth: `dev/pod/stop-request.toml`,
    # which rule (d) refuses unless it carries a claim, a reason and a `file:line`
    # (amendment A19). This refusal costs nothing today: both live `stop_loop` rows carry
    # `added_by = "owner"`.
    if row["action"] == "stop_loop" and row["added_by"] != "owner":
        _refuse(where, "action `stop_loop` halts the whole programme, so only the owner "
                       f"may add such a row and this one is `{row['added_by']}`. A model "
                       "declares a halt through dev/pod/stop-request.toml, which is "
                       "refused unless it carries checkable evidence (A19)")
    reason = row["reason"]
    if not isinstance(reason, str) or not reason.strip():
        _refuse(where, "`reason` is empty")
    if len(reason) > REASON_MAX:
        _refuse(where, f"`reason` is {len(reason)} characters, over the {REASON_MAX} cap")
    expired = row.get("expired", False)
    if not isinstance(expired, bool):
        _refuse(where, "`expired` is not true or false")
    if expired and "expired_at" not in row:
        _refuse(where, "is expired and carries no expired_at")
    if not expired and "expired_at" in row:
        _refuse(where, "carries expired_at but is not expired")
    if "expired_at" in row and not isinstance(row["expired_at"], datetime.date):
        _refuse(where, "`expired_at` is not a TOML local date")
    _check_when(row["when"], where, slots)
    out = dict(row)
    out["expired"] = expired
    return out


def check_table(rows, slots=None):
    """Table-wide refusals: a duplicate id, and two rows of ONE scope at one priority.

    THE PRIORITY REFUSAL KEEPS STEP 4 OF SECTION 4.4 AN ALARM. `id` ascending is a total
    order, so the sort always terminates; if two rows of the same scope could share a
    priority, the byte order of a name would silently decide a routing.
    """
    seen = {}
    for r in rows:
        if r["id"] in seen:
            _refuse(f"row `{r['id']}`", "is a duplicate id; ids are unique table-wide")
        seen[r["id"]] = r
    by = {}
    for r in rows:
        key = (r["scope"], r["priority"])
        if key in by:
            _refuse(f"row `{r['id']}`",
                    f"shares priority {r['priority']} with `{by[key]}` at scope "
                    f"`{r['scope']}`")
        by[key] = r["id"]
    return rows


def load_table(path=None, slots=None):
    """Every row of `dev/pod/table.toml`, checked. It returns a LIST of row dicts.

    The loader refuses an unknown key, so a typo never becomes a silent no-match row, and
    it refuses a schema or a vocabulary it does not know, so a table written for a later
    fact set is never routed by this router.
    """
    path = TABLE if path is None else Path(path)
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except OSError as e:
        raise TableError(f"{path} is unreadable: {e}") from e
    except tomllib.TOMLDecodeError as e:
        raise TableError(f"{path} does not parse: {e}") from e
    meta = data.get("meta")
    if not isinstance(meta, dict):
        _refuse(str(path), "carries no [meta] table")
    if meta.get("schema") != SCHEMA:
        _refuse(str(path), f"schema is {meta.get('schema')!r} and this loader reads "
                           f"{SCHEMA}")
    if meta.get("vocab") != VOCAB:
        _refuse(str(path), f"vocab is {meta.get('vocab')!r} and this loader reads "
                           f"`{VOCAB}`")
    extra = [k for k in meta if k not in ("schema", "vocab")]
    if extra:
        _refuse(str(path), f"[meta] carries the unknown key `{extra[0]}`")
    unknown = [k for k in data if k not in ("meta", "row")]
    if unknown:
        _refuse(str(path), f"carries the unknown top-level key `{unknown[0]}`")
    rows = [check_row(r, slots) for r in data.get("row", [])]
    return check_table(rows, slots)


# ---------------------------------------------------------------- the writer


def _toml_scalar(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, datetime.date):
        return v.isoformat()
    if isinstance(v, float):
        return repr(float(v))
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v, ensure_ascii=False)
    raise TableError(f"cannot write {v!r} into TOML")


def _toml_value(v, indent):
    if not isinstance(v, list):
        return _toml_scalar(v)
    items = [_toml_scalar(x) for x in v]
    one = "[" + ", ".join(items) + "]"
    if len(one) + indent <= 92:
        return one
    pad = "\n" + " " * (indent + 1)
    return "[" + ("," + pad).join(items) + "]"


def dump_table(rows) -> str:
    """The whole file, as text. ONE emitter, so a re-write of an unchanged table is
    byte-identical and a review diff shows only the rows that moved."""
    out = [HEADER.rstrip("\n"), "", "[meta]", f"schema = {SCHEMA}",
           f"vocab = {json.dumps(VOCAB)}", ""]
    for row in rows:
        out.append("[[row]]")
        for k in ROW_KEYS:
            if k == "when" or k not in row:
                continue
            out.append(f"{k} = {_toml_value(row[k], len(k) + 3)}")
        out.append("")
        out.append("  [row.when]")
        when = row["when"]
        for k in WHEN_KEYS:
            if k in when:
                out.append(f"  {k} = {_toml_value(when[k], len(k) + 5)}")
        out.append("")
    return "\n".join(out).rstrip("\n") + "\n"


def write_table(rows, path=None):
    """Temporary file, fsync, rename, fsync the directory. Section 5.3's write order.

    A HALF-WRITTEN TABLE IS THE ONE FAILURE THIS ORDER REMOVES. `admit_rows()` runs the
    replay BEFORE the write, so a rejected edit never reaches the file; a crash inside the
    write would otherwise leave a file that the loader refuses, and the loop then cannot
    route anything at all.
    """
    path = TABLE if path is None else Path(path)
    text = dump_table(rows)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
    return path


#: The last `git add`/`git commit` stderr (or exception text). `commit_task()` stores a
#: slice on the record as `commit_note` so a `commit: refused` close can be diagnosed.
GIT_COMMIT_ERROR = ""


def git_commit(paths, message, root=None):
    """R8: commit by EXPLICIT PATH, and never push. It returns True on a commit.

    A FAILURE IS NOT FATAL, and section 4.1 property 4 is why: a failed commit does not
    park the task. The close stands; `retry_refused_commits()` tries again on the next
    tick. `pod stop` commits the tracked table and the log, not a task home.

    **A FAILED COMMIT USED TO LEAVE THE PATHS STAGED.** MEASURED 2026-08-20 on
    LJ-1.404: `commit_task()` recorded `commit: refused` at 11:04:45, the three
    deliverable files stayed in the index, and the next human commit (`f898e3b`) swept
    them in with a spec-surface message. The reset that unmixed that commit left the
    files untracked and the DONE close with no `pod: LJ-1.404 done` line. On refuse this
    function unstages the paths it added. The error text is in `GIT_COMMIT_ERROR`.
    """
    global GIT_COMMIT_ERROR
    GIT_COMMIT_ERROR = ""
    root = ROOT if root is None else Path(root)
    rel = [str(Path(p).resolve().relative_to(Path(root).resolve())) for p in paths]
    added = False
    try:
        add = subprocess.run(["git", "add", "--"] + rel, cwd=root,
                             capture_output=True, text=True)
        if add.returncode != 0:
            GIT_COMMIT_ERROR = (add.stdout + add.stderr).strip()
            return False
        added = True
        done = subprocess.run(["git", "commit", "-m", message, "--"] + rel, cwd=root,
                              capture_output=True, text=True)
        err = (done.stdout + done.stderr).strip()
        if done.returncode == 0 or "nothing to commit" in err.lower():
            GIT_COMMIT_ERROR = ""
            return True
        GIT_COMMIT_ERROR = err
        return False
    except OSError as e:
        GIT_COMMIT_ERROR = str(e)
        return False
    finally:
        if added and GIT_COMMIT_ERROR:
            try:
                subprocess.run(["git", "reset", "-q", "HEAD", "--"] + rel, cwd=root,
                               capture_output=True, text=True)
            except OSError:
                pass


# ---------------------------------------------------------------- the router


def matches(when, rec):
    """One `[row.when]` block against one WHOLE record. Every key is AND-ed.

    IT READS THE WHOLE RECORD AND NOT THE FACTS OBJECT, because `concurrency` sits at the
    top level and guards the seconds keys. `rec.get("concurrency")` is a GUARD and never a
    matcher: no key names it, a record that states no process count carries null, and the
    seconds keys then fail rather than raise. A hand-copied `report` record is exactly
    that case, and section 4.5.2 forbids guessing a process count.

    IT COMPARES AND IT NEVER VALIDATES. `rec` must have come from
    `replay.check_record()`, which is the ONE boundary a record enters through. A record
    that skipped that boundary can carry a string where a number belongs, `>=` then raises
    `TypeError`, and the unattended loop stops with a traceback nobody reads.
    """
    f = rec["facts"]                         # the six. Nothing else is a fact.
    g = fnmatch.fnmatchcase
    ch = f["changed_files"]
    lines = f.get(FACT_KEY_A10)              # fact 7, A10. Absent on a six-fact record.
    op = f.get(FACT_KEY_A23)                 # fact 8, A23. Absent on a seven-fact record.
    one = rec.get("concurrency") == 1
    for k, v in when.items():
        if k == "exit_code":                 ok = f["exit_code"] == v
        elif k == "exit_code_in":            ok = f["exit_code"] in v
        elif k == "exit_code_absent":        ok = (f["exit_code"] is None) == v
        elif k == "error_class":             ok = f["error_class"] == v
        elif k == "error_class_in":          ok = f["error_class"] in v
        elif k == "obligations_delta_min":   ok = f["obligations_delta"] >= v
        elif k == "obligations_delta_max":   ok = f["obligations_delta"] <= v
        elif k == "changed_files_any":       ok = any(g(p, q) for p in ch for q in v)
        elif k == "changed_files_none":      ok = not any(g(p, q) for p in ch for q in v)
        elif k == "changed_files_all_within": ok = all(any(g(p, q) for q in v) for p in ch)
        elif k == "changed_files_count_min": ok = len(ch) >= v
        elif k == "changed_files_count_max": ok = len(ch) <= v
        elif k == "seconds_min":             ok = one and f["seconds"] >= v
        elif k == "seconds_max":             ok = one and f["seconds"] <= v
        elif k == "heap_wall":               ok = f["heap_wall"] == v
        elif k == "obligations_open_min":
            ok = op is not None and op >= v
        elif k == "obligations_open_max":
            ok = op is not None and op <= v
        elif k == "seconds_per_line_min":
            ok = one and bool(lines) and f["seconds"] / lines >= v
        elif k == "seconds_per_line_max":
            ok = one and bool(lines) and f["seconds"] / lines <= v
        else:
            raise KeyError(k)                # R1. The loader caught it first.
        if not ok:
            return False
    return True                              # an empty block is refused by the loader


def sort_key(row):
    """Section 4.4's ONE total order. `id` is unique, so step 4 always terminates."""
    return (0 if row["action"] == "stop_loop" else 1,            # A3
            0 if row["scope"].startswith(SCOPE_TASK) else 1,     # AD8
            row["priority"], row["id"])


def hits(table, rec):
    """Every row this record matches, in router order. The digest reads it for shadowing.

    SHADOWING IS REPORTED AND NEVER REFUSED (section 4.4). The digest re-runs this list
    over every record in the window and prints how often a row lost, so a row that never
    wins in 30 days is a maintainer signal and needs no extra log field.
    """
    out = [r for r in table
           if not r["expired"]
           and (r["scope"] == "system" or r["scope"] == SCOPE_TASK + rec["task"])
           and matches(r["when"], rec)]
    out.sort(key=sort_key)
    return out


def route(table, rec):
    """Returns (row_id, action), or (None, None). No judgement, no fallback row.

    NO MATCH IS A DESIGNED OUTCOME, not an error: R5 parks the task and three parked tasks
    stop the loop. A fallback row would turn every unmodelled return into a routing that
    nobody wrote.
    """
    got = hits(table, rec)
    if not got:
        return (None, None)                  # NO MATCH -> AD14 parks
    return (got[0]["id"], got[0]["action"])


# ---------------------------------------------------------------- the admission


def branch_block(brief) -> str:
    """The ONE fenced block whose info string is `toml pod-branches`, as text.

    Everything outside the block is prose and is never parsed (AD9). Pre-flight P1 refuses
    a brief with no block or with two, so a raise here means the brief reached admission
    without its pre-flight.
    """
    text = Path(brief).read_text(encoding="utf-8")
    found = BRANCH_FENCE.findall(text)
    if len(found) != 1:
        raise TableError(f"{brief}: {len(found)} `toml pod-branches` blocks, not one")
    return found[0]


def branch_notes(block: str) -> list[str]:
    """The trailing comment on each `[[branch]]` line, in order. Section 4.1 fills a row's
    `reason` from the branch HEADING, and this is the only heading a TOML branch has:
    `tomllib` drops every comment, so the text is read before it is parsed."""
    return [(m.group("note") or "").strip() for m in BRANCH_HEAD.finditer(block)]


def branches_of(brief) -> list[dict]:
    """Every `[[branch]]` of one brief, with its heading note attached as `_note`.

    An unknown branch key is a REFUSAL. A brief that writes `scope` or `added` on a branch
    believes it controls a field that admission owns, and the quiet alternative is a field
    the author wrote and nothing reads.
    """
    block = branch_block(brief)
    try:
        data = tomllib.loads(block)
    except tomllib.TOMLDecodeError as e:
        raise TableError(f"{brief}: the branch block does not parse: {e}") from e
    got = data.get("branch")
    if not isinstance(got, list) or not got:
        raise TableError(f"{brief}: the branch set is empty")
    if [k for k in data if k != "branch"]:
        raise TableError(f"{brief}: the branch block carries a key outside [[branch]]")
    notes = branch_notes(block)
    out = []
    for n, b in enumerate(got):
        unknown = [k for k in b if k not in BRANCH_KEYS]
        if unknown:
            raise TableError(f"{brief}: branch {n + 1} carries the unknown key "
                             f"`{unknown[0]}`")
        for k in ("id", "priority", "action", "when"):
            if k not in b:
                raise TableError(f"{brief}: branch {n + 1} has no `{k}`")
        row = dict(b)
        row["_note"] = notes[n] if n < len(notes) else ""
        out.append(row)
    return out


def namespaced_id(code: str, branch_id: str) -> str:
    """`[LJ-1.386]`'s `go` becomes `task-lj-1-386-go`. Section 4.2.

    THE RENAME RUNS AT ADMISSION AND NOWHERE ELSE. A branch id is a bare word inside one
    brief, so two briefs both writing `go` would collide in a table whose ids are unique
    table-wide. A brief never writes the namespaced form.
    """
    return "task-" + code.lower().replace(".", "-") + "-" + branch_id


def namespace(code, branch, added=None, slots=None):
    """One brief branch, as a table row. Admission fills the four fields a branch lacks."""
    reason = (branch.get("_note") or "").strip()
    if not reason:
        # The brief wrote no heading note. The row still needs a reason, so it states what
        # can be checked: which brief the row came from. It never states a purpose.
        reason = f"branch `{branch['id']}` of {code}, admitted from the brief"
    row = {"id": namespaced_id(code, branch["id"]),
           "scope": SCOPE_TASK + code,
           "priority": branch["priority"],
           "action": branch["action"],
           "added": added or datetime.date.today(),
           "added_by": "mathematician",
           "reason": reason[:REASON_MAX],
           "expired": False,
           "when": dict(branch["when"])}
    if "head_slot" in branch:
        row["head_slot"] = branch["head_slot"]
    if "outcome" in branch:
        row["outcome"] = branch["outcome"]
    return check_row(row, slots)


def rows_of_scope(table, code):
    """Every row this task owns, in table order, expired rows included."""
    return [r for r in table if r["scope"] == SCOPE_TASK + code]


def _same_rows(old, new):
    """Idempotence, with `added` excluded, and the exclusion is disclosed.

    Section 4.1 property 1 says a second instance re-writes nothing when the branch block
    is unchanged. `added` is today's date, so a retry on the NEXT day would differ in that
    one field and rewrite the tracked table for nothing. The clock moved; the brief did
    not, and only the brief decides a routing.
    """
    strip = [{k: v for k, v in r.items() if k != "added"} for r in old]
    return strip == [{k: v for k, v in r.items() if k != "added"} for r in new]


def _brief_head_slot(brief):
    """The brief's `head_slot:` line, or `coder`. Local so this module does not
    import `pod` or `preflight` (both already import this file)."""
    try:
        text = Path(brief).read_text(encoding="utf-8")
    except OSError:
        return "coder"
    head = re.search(r"(?im)^##\s*HEAD\b(.*?)(?=^##\s|\Z)", text, re.S)
    if not head:
        return "coder"
    m = re.search(r"(?m)^[ \t]*head_slot[ \t]*:[ \t]*(.+?)[ \t]*$", head.group(1))
    return m.group(1).strip() if m else "coder"


#: THE LAST ADMISSION REFUSAL IN WORDS, or None. `admit_rows()` clears it on entry and
#: sets it on every refusal; rule (f) reads it to fill the park's `detail`.
#:
#: **IT IS A MODULE GLOBAL AND NOT A THIRD ARGUMENT, and that is measured rather than
#: preferred.** `scripts/tests/test_pod_loop.py` patches `admit_rows` with two-argument
#: stubs, so widening the signature turned a real admission into a `TypeError` that
#: rule (f) swallows as「refused」: three suites went red and every dispatch stopped.
#: It is the same trap `_NoLaunch.launch()` documents with `**kw`. A stub that never
#: touches this global simply leaves it None, which is exactly the old behaviour.
LAST_REFUSAL = None


def admit_rows(code, brief):
    """Append this brief's branches as task rows. Return True on ADMIT.

    ON A REFUSAL IT SETS `LAST_REFUSAL` above. The park rule (f) writes used to carry
    `reason: "admission"` and nothing else, because every refusal below is swallowed into
    a bare `False`. MEASURED 2026-08-19: LJ-1.388 parked on admission with `detail: None`,
    and the sentence that would have explained it was `check_balance()`'s, which names the
    error class the corpus lacks.

    FOUR PROPERTIES, and rule (f) calling this after the pre-flight and before `launch()`
    is what gives them (section 4.1):

    1. IT IS IDEMPOTENT. A second instance re-writes nothing when the branch block is
       unchanged. A CHANGED brief replaces that code's rows, which is a remove plus an
       add, so the replay's third rule already guards it.
    2. R3 RUNS ON IT, because the replay runs before the write. R3 holds at admission
       exactly as it holds for a maintainer batch.
    3. A FAILURE NEVER HALF-WRITES. On a REJECT, or on any refusal, this returns False,
       rule (f) parks with `reason: "admission"`, and NO row enters the table. Rule (a2)
       retries on the next table edit.
    4. THE COMMIT IS SEPARATE FROM THE WRITE. A failed commit leaves the rows uncommitted
       in the tracked file, and `pod stop` commits them.
    5. A MATHEMATICIAN BRIEF WRITES NO ROW. The slot is RESIDENT (2026-08-20) and is
       fed by refill, not by the table. Owner 2026-08-21: `admit_rows` returns True
       and leaves the table untouched.
    """
    # THE IMPORT IS DEFERRED, and the reason is one rule with one home. `replay()` calls
    # `route()`, which lives here, and `admit_rows()` calls `replay()`, which lives in
    # `scripts/pod/replay.py`. A module-level import either way is a cycle, and copying
    # one of the two functions into the other file would give one rule two homes (W5).
    import replay as replay_mod             # noqa: PLC0415
    global LAST_REFUSAL                     # noqa: PLW0603. See the constant's comment
    LAST_REFUSAL = None
    try:
        if _brief_head_slot(brief) == "mathematician":
            # Resident mathematician: no task rows. Refill and POD-MATH are not
            # admitted here either. Owner 2026-08-21.
            return True
        slots = head_slots()
        rows = [namespace(code, b, slots=slots) for b in branches_of(brief)]
        old = load_table(TABLE, slots)
        # ONLY THE BRIEF'S OWN ROWS ARE THIS FUNCTION'S TO REBUILD. AD2 lets the
        # maintainer add a task-scoped row from a measured record (the
        # sys-critic-upheld-no-go shape, at task scope: e.g. task-lj-1-440-
        # stop-stated), and `namespace()` always stamps `added_by: "mathematician"`
        # on a brief-derived row, so that field is the one reliable seam between
        # the two. MEASURED 2026-08-21: without this filter, a re-dispatch (an
        # escalate re-admits the SAME brief) rebuilt this scope from the brief
        # alone, which silently proposed DELETING the maintainer's row; R3
        # correctly refused that deletion (it was moving live corpus records),
        # and the refusal parked the task on "admission" FOR EVER, since the next
        # retry hit the identical rebuild and the identical refusal.
        brief_rows = [r for r in rows_of_scope(old, code)
                      if r.get("added_by") == "mathematician"]
        if _same_rows(brief_rows, rows):
            return True                      # IDEMPOTENT. Attempt 2 writes nothing.
        new = [r for r in old
               if r["scope"] != SCOPE_TASK + code
               or r.get("added_by") != "mathematician"] + rows
        check_table(new, slots)
        records = replay_mod.corpus()
        verdict, moved = replay_mod.replay(old, new, records)    # R3, section 4.5.1
        if verdict != "ADMIT":
            LAST_REFUSAL = (
                f"R3 REJECT: the rows move {len(moved)} corpus record(s): "
                + "; ".join(f"{m[0]} {m[1]}/{m[2]} -> {m[3]}/{m[4]}" for m in moved[:4]))
            return False
        write_table(new)                     # tmp -> fsync -> rename -> fsync(dir)
    except (TableError, OSError) as e:
        # A `KeyError` from `matches()` is NOT caught. R1 says the loader caught an
        # unknown key first, so a raise there is an alarm and never a routine path.
        LAST_REFUSAL = f"{type(e).__name__}: {e}"[:400]
        return False
    git_commit([TABLE], "pod: admit " + code)                # R8, explicit path
    return True


def expire_rows(code, at=None):
    """Retire every live row of one task. It returns the number of rows it retired.

    EXPIRY IS EXEMPT FROM R3, and here is the reason. The router drops an expired row, so
    expiry DOES move every record that row used to win. R3 forbids a MAINTAINER from
    moving traffic; it does not forbid a row from dying with its task. The replay uses the
    SAME expiry state on both sides, so an expiry can never hide inside a table edit.

    Two events trigger it and both are mechanical: the task reaches `done` under AD13
    (rule (c)'s DONE limb), or its directory moves under `agents/tasks/archive/`
    (rule (a1)). A `system` row never expires by time; the owner removes it.
    """
    slots = head_slots()
    old = load_table(TABLE, slots)
    at = at or datetime.date.today()
    new, n = [], 0
    for r in old:
        if r["scope"] == SCOPE_TASK + code and not r["expired"]:
            r = dict(r, expired=True, expired_at=at)
            n += 1
        new.append(r)
    if not n:
        return 0
    write_table(new)                         # A ROW IS NEVER DELETED. Clause W4.
    git_commit([TABLE], "pod: expire " + code)
    return n


# ---------------------------------------------------------------- the command line


def _print_rows(rows, scope=None):
    for r in sorted(rows, key=sort_key):
        if scope and r["scope"] != scope:
            continue
        mark = "EXPIRED " if r["expired"] else ""
        keys = ",".join(sorted(r["when"]))
        print(f"{mark}{r['id']:38s} {r['scope']:22s} p{r['priority']:<5d} "
              f"{r['action']:20s} {keys}")


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 2
    import replay as replay_mod             # deferred, for the cycle named in admit_rows
    try:
        if argv[0] == "--check":
            rows = load_table()
            print(f"dev/pod/table.toml: {len(rows)} rows, "
                  f"{sum(1 for r in rows if r['expired'])} expired, "
                  f"{len(replay_mod.corpus())} corpus records")
            return 0
        if argv[0] == "--rows":
            _print_rows(load_table(), argv[1] if len(argv) > 1 else None)
            return 0
        if argv[0] == "--route" and len(argv) > 1:
            # THREE REFUSALS, AND EACH ONE WAS A TRACEBACK. An absent file ended in
            # `FileNotFoundError`, a file that is not JSON ended in `JSONDecodeError`, and
            # a record with a string-valued fact ended in `TypeError` inside `matches()`.
            # The loop runs unattended, so each one is a message and exit 1 instead.
            try:
                raw = Path(argv[1]).read_text(encoding="utf-8")
            except OSError as e:
                raise TableError(f"{argv[1]} is unreadable: {e}") from e
            try:
                data = json.loads(raw)
            except json.JSONDecodeError as e:
                raise TableError(f"{argv[1]} does not parse as JSON: {e}") from e
            rec = replay_mod.check_record(data, argv[1])
            row_id, action = route(load_table(), rec)
            if row_id is None:
                print("NO MATCH")
                return 1
            print(f"{row_id} {action}")
            return 0
    except TableError as e:
        print(f"REFUSED {e}", file=sys.stderr)
        return 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    # ONE MODULE OBJECT, AND A REAL REFUSAL ESCAPED WITHOUT IT. Running this file as a
    # script names it `__main__`. `main()` then imports `replay`, which does its own
    # `import table` and builds a SECOND copy of this module, whose `TableError` is a
    # DIFFERENT class. `except TableError` inside `main()` therefore missed every refusal
    # raised in `replay.py`, and `--route` printed a traceback where it had a message:
    # measured 2026-08-17 on a record with a string-valued fact. Delegating to the
    # imported copy gives both files one class. `sys.path` already carries this directory.
    import table as _table                   # noqa: PLC0415
    sys.exit(_table.main(sys.argv[1:]))
