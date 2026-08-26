#!/usr/bin/env python3
"""The loader of `dev/pod/heads.toml`: the five heads, the limits and the two tiers.

WHY THIS FILE EXISTS. Section 6.1 of `dev/memos/LJ-4-pod-program-design.md` names this
loader and names no file for it. Day 2 delivered `dev/pod/heads.toml` and its read-back
rule; it did not deliver the loader, and `head_slots()` at `scripts/pod/table.py:193`
says in its own docstring that it is NOT that loader. So the rule had no owner. This file
is the owner. `table.head_slots()` stays a second READER of the slot names, which its
docstring already admits: two readers of one file are admissible, two owners are not.

THE MEASURED FAILURE IT ANSWERS. Before `dev/pod/heads.toml` a model name, an effort
level and a deadline lived in three places: a skill document, a policy module and one
literal in the dispatcher. `dev/memos/LJ-4-pod-program-design.md:1826-1836` measures the
consequence: after section 7.1 row 21 retires `scripts/dispatch/dispatch_policy.py`, the
dispatcher falls back to a hard literal and starts a CODEX agent on a deepseek model for
every dispatch that omits `--harness`.

NO FIELD HAS A SILENT DEFAULT. A missing field is a refusal. A misspelt field is a
refusal. A model outside `legal.models` is a refusal. An effort outside `legal.efforts`
is a refusal. A default here would be a number nobody ruled, and the whole point of the
file is that the owner rules every number in it. `max_concurrency` is the ONE optional
field (amendment A27) and its absence is not a default: it is the word UNLIMITED, which
is what every slot carried before A27 and what four of the five carry today.

A SLOT MAY CARRY MORE THAN ONE MODEL, amendment A27, and this loader reads both
spellings: one inline table, or an ARRAY of inline tables. `load_heads()["heads"][slot]`
is a LIST in both cases, so no reader branches on the shape it happened to get.

WHAT THIS MODULE DOES NOT DO. It never dispatches, it never reads a brief and it never
decides which head a task gets. That is why the CAP lives here and the COUNT does not:
this module refuses a malformed `max_concurrency` and `pick_head_config()` in
`scripts/pod/pod.py` is the one place that counts live tasks and picks a config.
`scripts/pod/pod.py` rule (f) resolves the slot ONCE, at dispatch, and writes `model`,
`effort`, `role` and `heads_sha256` into the transition log line. AD26 says nothing
re-reads this file for a running task.

Usage:
  heads.py --check         load the file and print every slot, limit and tier
  heads.py --slot <name>   print every config of one slot, one per line
  heads.py --sha256        print the digest the transition log records
Exit status: 0 clean, 1 a refusal, 2 usage error.
"""

from __future__ import annotations

import hashlib
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
HEADS = ROOT / "dev" / "pod" / "heads.toml"

#: The six limits of section 6.1. Every one is required and none has a default.
#:
#: `parked_max` joined them on 2026-08-19, owner's ruling, raised from a hardcoded 3 to 7.
#: It was a bare literal in TWO places in `pod.py`, rule (d)'s test and the status line, so
#: the number the owner read and the number the program obeyed could drift apart. Lowered
#: to 5 on 2026-08-23 (`dev/pod/heads.toml`); the live value is read here, never retyped.
LIMIT_KEYS = ("tick_seconds", "exclusive_max_load1", "agda_deadline_s",
              "worker_deadline_s", "attempt_max", "parked_max")

#: The four fields every `[heads]` config carries. None has a default.
SLOT_KEYS = ("model", "effort", "harness", "sandbox")

#: The ONE optional field in this whole file, amendment A27. An ABSENT `max_concurrency`
#: means UNLIMITED, which is exactly what every slot carried before A27, so a slot written
#: as one inline table means today what it meant yesterday. A PRESENT one is an integer of
#: 1 or more and it caps the tasks that may hold this slot ON THIS MODEL at one time.
#:
#: THE COUNTING IS NOT THIS MODULE'S. This loader validates the number and stops there;
#: `pick_head_config()` in `scripts/pod/pod.py` counts the live tasks and picks a config.
#: The docstring above already rules that this module never decides which head a task
#: gets, and a cap is that decision by another name.
SLOT_OPTIONAL = ("max_concurrency",)

#: The tier keys amendment A14 restored from `dev/LESSONS.md` C-12. The names are
#: `dev/pod/heads.toml`'s own, which its comment at `:89-92` discloses: the design names
#: the two tiers and their numbers and names NO key for them.
TIER_KEYS = {"wide": ("slots", "heap"), "heavy": ("slots", "heap"),
             "shared": ("max_heap_sum_gb", "free_memory_pct_for_extra",
                        "per_process_backstop_gb", "system_free_floor_pct")}


class HeadsError(Exception):
    """`dev/pod/heads.toml` is unreadable or a field is missing, misspelt or illegal.

    EVERY RAISE IS A REFUSAL WITH A REASON. The caller never falls back to a literal,
    because a literal is exactly the defect measured at
    `dev/memos/LJ-4-pod-program-design.md:1826-1836`.
    """


_CACHE: dict[str, tuple[int, dict]] = {}


def _refuse(msg: str):
    raise HeadsError(f"dev/pod/heads.toml: {msg}")


def _require(table, keys, where):
    for k in keys:
        if k not in table:
            _refuse(f"{where} carries no `{k}`")


def load_heads(path=None, cache=True) -> dict:
    """The whole file, checked. It returns a frozen dict and it guesses nothing.

    The return carries `version`, `legal`, `limits`, `heads`, `tiers` and `sha256`. The
    digest is over the RAW BYTES, so the transition log records the exact file that
    resolved a head; AD26 needs the file that ran and not the file that stands today.

    **THE CACHE KEYS ON `(path, mtime)`, NEVER ON `path` ALONE.** MEASURED 2026-08-26: a
    plain path-keyed cache returned a heads.toml ruling landed and committed 3 hours
    earlier as though it had never happened, because `dev/pod/README.md:115-118`
    documents "edit the row, and the next dispatch uses it" with no reload step, and
    every production caller of `configs()`/`head()` takes the `cache=True` default. Five
    real dispatches (`[LJ-1.656]`'s retry, `[LJ-1.657]` through `[LJ-1.660]`, `[LJ-1.662]`)
    ran on the stale config before this was caught. An `mtime` check costs one `stat()`,
    far cheaper than the reparse it guards, and a process that never touches the file
    again pays that one `stat()` per call and nothing else.
    """
    p = HEADS if path is None else Path(path)
    key = str(p)
    try:
        mtime = p.stat().st_mtime_ns
    except OSError:
        mtime = None
    if cache and mtime is not None:
        cached = _CACHE.get(key)
        if cached is not None and cached[0] == mtime:
            return cached[1]
    try:
        raw = p.read_bytes()
    except OSError as e:
        _refuse(f"is unreadable: {e}")
    try:
        data = tomllib.loads(raw.decode("utf-8"))
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        _refuse(f"does not parse: {e}")

    if data.get("version") != 1:
        _refuse(f"declares version {data.get('version')!r}, and this loader reads 1")

    legal = data.get("legal")
    if not isinstance(legal, dict):
        _refuse("carries no [legal] table")
    _require(legal, ("efforts", "models"), "[legal]")
    efforts, models = legal["efforts"], legal["models"]
    for name, value in (("efforts", efforts), ("models", models)):
        if not isinstance(value, list) or not value or \
                not all(isinstance(x, str) for x in value):
            _refuse(f"[legal].{name} is not a non-empty list of strings")

    limits = data.get("limits")
    if not isinstance(limits, dict):
        _refuse("carries no [limits] table")
    _require(limits, LIMIT_KEYS, "[limits]")
    for k in LIMIT_KEYS:
        v = limits[k]
        if isinstance(v, bool) or not isinstance(v, (int, float)):
            _refuse(f"[limits].{k} is {v!r}, which is not a number")
        if v <= 0:
            _refuse(f"[limits].{k} is {v!r}, and every limit is positive")

    heads = data.get("heads")
    if not isinstance(heads, dict) or not heads:
        _refuse("carries no [heads] table")
    slots = {}
    for slot, value in heads.items():
        # A27. A SLOT IS ONE INLINE TABLE OR A NON-EMPTY ARRAY OF THEM, and the array is
        # a STRICT SUPERSET: an array of one means what the single table meant. The
        # single-table spelling is kept and not merely tolerated, because four of the
        # five slots have exactly one head and an array around each of them would be
        # ceremony that hides which slot really carries a choice.
        rows = [value] if isinstance(value, dict) else value
        if not isinstance(rows, list) or not rows:
            _refuse(f"[heads].{slot} is neither a table nor a non-empty array of tables")
        seen = []
        for i, row in enumerate(rows):
            where = (f"[heads].{slot}" if len(rows) == 1
                     else f"[heads].{slot} config {i + 1}")
            if not isinstance(row, dict):
                _refuse(f"{where} is not a table")
            _require(row, SLOT_KEYS, where)
            for k in row:
                if k not in SLOT_KEYS and k not in SLOT_OPTIONAL:
                    _refuse(f"{where} carries `{k}`, which is not one of "
                            f"{', '.join(SLOT_KEYS + SLOT_OPTIONAL)}")
            if row["model"] not in models:
                _refuse(f"{where} names model {row['model']!r}, which is not in "
                        f"legal.models")
            if row["effort"] not in efforts:
                _refuse(f"{where} names effort {row['effort']!r}, which is not in "
                        f"legal.efforts")
            cap = row.get("max_concurrency")
            if cap is not None:
                # A BOOLEAN IS AN `int` IN PYTHON, and `max_concurrency = true` would
                # otherwise load as a cap of one. The `[limits]` block above refuses a
                # boolean for the same reason and this is the same trap.
                if isinstance(cap, bool) or not isinstance(cap, int):
                    _refuse(f"{where} names max_concurrency {cap!r}, which is not an "
                            f"integer")
                if cap < 1:
                    _refuse(f"{where} names max_concurrency {cap!r}, and a cap below 1 "
                            f"is not `unlimited`: it is a head no task can ever reach. "
                            f"OMIT the field to mean unlimited")
            # THE LIVE COUNT IS KEYED ON THE SLOT AND THE MODEL, because `role` and
            # `model` are the two fields rule (f) writes onto the task at the dispatch
            # (AD26). Two configs of one slot on ONE model are therefore two caps the
            # dispatcher cannot tell apart, and it would spend both on the same tasks.
            if row["model"] in seen:
                _refuse(f"[heads].{slot} names model {row['model']!r} twice, and the "
                        f"dispatcher counts a live head by its slot and its model")
            seen.append(row["model"])
        slots[slot] = [dict(r) for r in rows]

    tiers = data.get("tiers")
    if not isinstance(tiers, dict):
        _refuse("carries no [tiers] table, and A14 restored C-12's two tiers")
    for name, keys in TIER_KEYS.items():
        row = tiers.get(name)
        if not isinstance(row, dict):
            _refuse(f"carries no [tiers.{name}] table")
        _require(row, keys, f"[tiers.{name}]")

    # THE MIXED WORST CASE, checked here rather than trusted. A14 holds the sum of the
    # per-slot heap caps at or under `max_heap_sum_gb`. The check is arithmetic and the
    # file states both terms, so a future edit that widens a tier is caught at load and
    # not on the machine that runs out of memory.
    #
    # TWO SUMS, and an opus-5 review found this checked only the first. EACH TIER
    # ALONE, at every one of its own slots full, must fit the cap on its own -- that is
    # the loop below. BUT A TIER FILLING EVERY SLOT NEVER HAS TO FIT ALONGSIDE ANOTHER
    # TIER doing the same: `launcher.py`'s `agda_heap_sum_over()` refuses a dispatch
    # the moment the RUNNING total plus one more holder would cross the cap, so the
    # only cross-tier state ever actually reached is ONE holder from each tier at
    # once (`dev/pod/heads.toml [tiers.shared]`'s own comment names this as the design
    # target), never every slot of every tier simultaneously. Checking the FULL
    # cross-product here would refuse configs the runtime dispatcher already keeps
    # safe -- WIDE's own two slots at 2 GB alongside HEAVY's own one slot at 4 GB is
    # a real, load-bearing config this file must accept, and 2*2 + 1*4 = 8 is already
    # above a 6 GB cap. One holder per tier is the sum that must fit.
    cap = tiers["shared"]["max_heap_sum_gb"]
    one_each = 0
    for name in ("wide", "heavy"):
        gb = _heap_gb(tiers[name]["heap"])
        if gb is None:
            _refuse(f"[tiers.{name}].heap is {tiers[name]['heap']!r} and states no -M cap")
        if gb * tiers[name]["slots"] > cap:
            _refuse(f"[tiers.{name}] asks {tiers[name]['slots']} slots at {gb} GB, which "
                    f"is above [tiers.shared].max_heap_sum_gb of {cap}")
        one_each += gb
    if one_each > cap:
        _refuse(f"one holder from EACH tier at once already budgets {one_each} GB, "
                f"which is above [tiers.shared].max_heap_sum_gb of {cap}. This is the "
                f"mixed worst case the runtime dispatcher actually reaches "
                f"(`launcher.py`'s `agda_heap_sum_over()`), not the per-tier one above")

    # `heads` MAPS A SLOT TO A LIST, ALWAYS, and never to a single row. One shape for
    # both spellings is what stops a reader branching on the type it happened to get; the
    # readers that want exactly one head call `head()`, which refuses a slot that carries
    # a choice rather than picking the first and calling it the default.
    out = {"version": 1, "legal": dict(legal), "limits": dict(limits),
           "heads": slots,
           "tiers": {k: dict(v) for k, v in tiers.items()},
           "sha256": hashlib.sha256(raw).hexdigest()}
    if cache and mtime is not None:
        _CACHE[key] = (mtime, out)
    return out


def _heap_gb(flags: str):
    """The `-M<n>g` term of one caliber, in whole gigabytes, or None.

    It reads the RTS flag and never a comment, because the caliber that binds is the one
    the process gets. Only the `g` suffix is admitted: `-M8192m` would need a unit table
    and this repository writes one form.
    """
    for term in str(flags).split():
        if term.startswith("-M") and term.endswith("g"):
            body = term[2:-1]
            if body.isdigit():
                return int(body)
    return None


def limits(path=None) -> dict:
    """The five limits. `pod.py` reads `tick_seconds`, `worker_deadline_s` and
    `attempt_max`; `accept.py` reads `agda_deadline_s`; `admits()` reads
    `exclusive_max_load1`."""
    return load_heads(path)["limits"]


def configs(slot: str, path=None, cache=True) -> tuple[dict, ...]:
    """EVERY config of one slot, complete, in the file's own order. A27.

    A slot written as one inline table returns a tuple of one, so a caller written before
    A27 sees no difference except the container. Each entry carries the four `SLOT_KEYS`,
    a `max_concurrency` that is an integer or None, and `pi_provider` when the harness is
    `herdr-pi`.

    THE ORDER IS THE FILE'S AND IT IS LOAD-BEARING. `pick_head_config()` breaks a tie
    between two capped configs by it, so the owner ranks two heads by editing the array.
    """
    data = load_heads(path, cache=cache)
    heads = data["heads"]
    if slot not in heads:
        _refuse(f"has no [heads].{slot}; the slots are {', '.join(sorted(heads))}")
    return tuple(_complete(dict(row), slot, data) for row in heads[slot])


def _complete(row: dict, slot: str, data: dict) -> dict:
    """One config with its derived fields filled in. It never guesses one."""
    # `max_concurrency` IS ALWAYS PRESENT IN THE RETURN AND IS None WHEN UNCAPPED, so no
    # caller writes `row.get(...)` and no caller can read an absent cap as a zero.
    row.setdefault("max_concurrency", None)
    # THE PROVIDER IS DERIVED HERE AND NOWHERE ELSE. `legal.pi_provider` had zero
    # consumers until 2026-08-18: the launcher passed a module constant, so both
    # `glm-5.3` heads dispatched on `deepseek`. heads.toml records what that costs,
    # and the cost is invisible: `pi` warns, echoes the prompt, and exits `done` in
    # ten seconds having written nothing, which every guard reads as a healthy run.
    if row["harness"] == "herdr-pi":
        table = data["legal"].get("pi_provider")
        if not isinstance(table, dict):
            _refuse("carries no [legal.pi_provider] table, which every herdr-pi slot needs")
        if row["model"] not in table:
            _refuse(f"[legal.pi_provider] has no entry for {row['model']}, which "
                    f"[heads].{slot} runs on herdr-pi")
        row["pi_provider"] = str(table[row["model"]])
    return row


def head(slot: str, path=None, model: str | None = None, cache=True) -> dict:
    """ONE config of one slot. It REFUSES rather than returning a default, always.

    An unknown slot is a refusal, because a default head is a model nobody ruled.

    **A SLOT THAT CARRIES A CHOICE AND A CALL THAT NAMES NO MODEL IS ALSO A REFUSAL**,
    amendment A27. Returning the first entry would be a silent default of exactly the
    kind this file exists to forbid, and it would spend an uncapped vendor while a capped
    one sat idle. `pick_head_config()` in `scripts/pod/pod.py` makes that choice and then
    names the model it chose here.
    """
    rows = configs(slot, path, cache=cache)
    if model is None:
        if len(rows) != 1:
            _refuse(f"[heads].{slot} carries {len(rows)} model configs "
                    f"({', '.join(r['model'] for r in rows)}) and this call named none. "
                    f"The dispatcher picks one (A27); nothing else may guess")
        return dict(rows[0])
    for row in rows:
        if row["model"] == model:
            return dict(row)
    _refuse(f"[heads].{slot} carries no config on model {model!r}; it carries "
            f"{', '.join(r['model'] for r in rows)}")


def slots_of_tier(tier: str = "wide", path=None) -> int:
    """The concurrent Agda writer count of one tier, A14."""
    tiers = load_heads(path)["tiers"]
    if tier not in tiers or "slots" not in tiers[tier]:
        _refuse(f"has no [tiers.{tier}].slots")
    return int(tiers[tier]["slots"])


def sha256(path=None) -> str:
    """The digest the transition log records. AD26 keys a running task to this value."""
    return load_heads(path)["sha256"]


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 2
    try:
        data = load_heads()
        if argv[0] == "--sha256":
            print(data["sha256"])
            return 0
        if argv[0] == "--slot" and len(argv) > 1:
            # ONE LINE PER CONFIG, so a slot that carries a choice shows the choice. It
            # prints through `configs()` and never `head()`, because `head()` refuses a
            # multi-config slot on purpose and a diagnostic must not be the one caller
            # that cannot look.
            for row in configs(argv[1]):
                print(" ".join(row[k] for k in SLOT_KEYS)
                      + (f" max_concurrency={row['max_concurrency']}"
                         if row["max_concurrency"] is not None else ""))
            return 0
        if argv[0] == "--check":
            print(f"dev/pod/heads.toml: {len(data['heads'])} slots, "
                  f"{len(data['limits'])} limits, {len(data['tiers'])} tiers, "
                  f"sha256 {data['sha256'][:8]}")
            for slot in sorted(data["heads"]):
                for i, row in enumerate(data["heads"][slot]):
                    name = slot if i == 0 else ""
                    cap = row.get("max_concurrency")
                    print(f"  {name:26s} {row['model']:22s} {row['effort']:7s} "
                          f"{row['harness']:14s} {row['sandbox']:12s} "
                          f"{'uncapped' if cap is None else f'max {cap}'}")
            for k in LIMIT_KEYS:
                print(f"  limit {k:22s} {data['limits'][k]}")
            for name in sorted(data["tiers"]):
                print(f"  tier  {name:22s} {data['tiers'][name]}")
            return 0
    except HeadsError as e:
        print(f"REFUSED {e}", file=sys.stderr)
        return 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
