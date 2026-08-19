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
file is that the owner rules every number in it.

WHAT THIS MODULE DOES NOT DO. It never dispatches, it never reads a brief and it never
decides which head a task gets. `scripts/pod/pod.py` rule (f) resolves the slot ONCE, at
dispatch, and writes `model`, `effort`, `role` and `heads_sha256` into the transition log
line. AD26 says nothing re-reads this file for a running task.

Usage:
  heads.py --check         load the file and print every slot, limit and tier
  heads.py --slot <name>   print one slot as `model effort harness sandbox`
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
#: the number the owner read and the number the program obeyed could drift apart.
LIMIT_KEYS = ("tick_seconds", "exclusive_max_load1", "agda_deadline_s",
              "worker_deadline_s", "attempt_max", "parked_max")

#: The four fields every `[heads]` slot carries.
SLOT_KEYS = ("model", "effort", "harness", "sandbox")

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


_CACHE: dict[str, dict] = {}


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
    """
    p = HEADS if path is None else Path(path)
    key = str(p)
    if cache and key in _CACHE:
        return _CACHE[key]
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
    for slot, row in heads.items():
        if not isinstance(row, dict):
            _refuse(f"[heads].{slot} is not a table")
        _require(row, SLOT_KEYS, f"[heads].{slot}")
        for k in row:
            if k not in SLOT_KEYS:
                _refuse(f"[heads].{slot} carries `{k}`, which is not one of "
                        f"{', '.join(SLOT_KEYS)}")
        if row["model"] not in models:
            _refuse(f"[heads].{slot} names model {row['model']!r}, which is not in "
                    f"legal.models")
        if row["effort"] not in efforts:
            _refuse(f"[heads].{slot} names effort {row['effort']!r}, which is not in "
                    f"legal.efforts")

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
    cap = tiers["shared"]["max_heap_sum_gb"]
    for name in ("wide", "heavy"):
        gb = _heap_gb(tiers[name]["heap"])
        if gb is None:
            _refuse(f"[tiers.{name}].heap is {tiers[name]['heap']!r} and states no -M cap")
        if gb * tiers[name]["slots"] > cap:
            _refuse(f"[tiers.{name}] asks {tiers[name]['slots']} slots at {gb} GB, which "
                    f"is above [tiers.shared].max_heap_sum_gb of {cap}")

    out = {"version": 1, "legal": dict(legal), "limits": dict(limits),
           "heads": {k: dict(v) for k, v in heads.items()},
           "tiers": {k: dict(v) for k, v in tiers.items()},
           "sha256": hashlib.sha256(raw).hexdigest()}
    if cache:
        _CACHE[key] = out
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


def head(slot: str, path=None) -> dict:
    """One slot's four fields. It REFUSES an unknown slot rather than returning a
    default, because a default head is a model nobody ruled."""
    data = load_heads(path)
    heads = data["heads"]
    if slot not in heads:
        _refuse(f"has no [heads].{slot}; the slots are {', '.join(sorted(heads))}")
    row = dict(heads[slot])
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
            row = head(argv[1])
            print(" ".join(row[k] for k in SLOT_KEYS))
            return 0
        if argv[0] == "--check":
            print(f"dev/pod/heads.toml: {len(data['heads'])} slots, "
                  f"{len(data['limits'])} limits, {len(data['tiers'])} tiers, "
                  f"sha256 {data['sha256'][:8]}")
            for slot in sorted(data["heads"]):
                row = data["heads"][slot]
                print(f"  {slot:26s} {row['model']:18s} {row['effort']:7s} "
                      f"{row['harness']:14s} {row['sandbox']}")
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
