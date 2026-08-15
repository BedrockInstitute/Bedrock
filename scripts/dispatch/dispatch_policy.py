#!/usr/bin/env python3
"""THE DISPATCH POLICY. One switch, two tables, one clock, one place to edit.

WHAT THIS IS. DD17 says which head runs a dispatch. From 2026-08-13 it has TWO
versions, and exactly one of them is in force. `VERSION_IN_FORCE` below is the
switch. Edit that one line and every consumer follows: the checker that reads a
brief's `tier:` line, the default harness `dispatch.py` picks, and the table the
inspection command prints.

THE PRECEDENCE, and it is the first thing to read in this file:

  * The owner's pinned `VERSION_IN_FORCE` ALWAYS WINS. A pinned value is a
    ruling, and a tool that silently overrides a ruling is worse than no tool.
  * `VERSION_IN_FORCE = "auto"` delegates to the clock, which picks the mode
    from DeepSeek's peak and off-peak windows in Beijing time. The clock
    decides ONLY when the owner has not pinned a mode.

The clock rule came from the owner's instruction of 2026-08-14: DeepSeek
prices peak and off-peak, the off-peak price is half the peak price, peak is
Beijing time 09:00 to 12:00 and 14:00 to 18:00, and the dispatch mode follows
that clock. OFF-PEAK, deepseek is half price and `pi-subagent-mode` leads.
PEAK, deepseek is dear and the in-harness Opus is not billed on that clock, so
`in-harness-subagent-mode` leads.

INSPECT IT WITH ONE COMMAND, and never by reading code:

    python3 scripts/dispatch/dispatch_policy.py

It prints the version in force, its full table, why it is in force, the
condition that reverts it, and, when the clock selected the version, the
window it is in and the next boundary.

THE HONEST LIMIT, AND IT IS THE MOST IMPORTANT LINE IN THIS FILE.

**This switch CANNOT force the orchestrator to use the right head.** An
in-harness Opus subagent never passes through `.claude/skills/codex-dispatch/
dispatch.py`, so no value here can start it, stop it, or redirect it. The same
gap already cost this project two mandatory rules on `[LJ-1.11]`, and PLAN DD18
and DD25 both record it.

What the switch DOES do, and this is all it does:

  1. It DRIVES the default harness `dispatch.py` uses when no `--harness` is
     given. That is authoritative, because that code path reads this file.
  2. It DRIVES what `scripts/dispatch/check-dispatch-policy.py` accepts in a `tier:`
     line. That makes a wrong choice DETECTABLE by an audit.
  3. It DRIVES what the inspection command prints.

Everything else is convention, enforced by the audit and by nothing else. A
switch that looked authoritative over the orchestrator would be false safety,
which `AGENTS.md` names as worse than no rule at all.

THE OVERRIDE IS TEMPORARY. The field records the date it was set and the
condition that reverts it, because a switch that records only its position
loses why it is there. The owner sets a mode by word, and each mode is named
for the head it LEADS with, so the name says what it does.

THE VENDOR DATA IS NOT HERE, AND THAT IS THE DD19 LINE. `dev/vendors.toml`
holds which vendor is in force, its model ID, whether `pi` is wired to it, and
its price bands. THIS FILE holds the head tables, the two modes, the invariant
and the mode logic. `AGENTS.md` names this file the ONLY home of the tables,
and no vendor row restates one. Read the two sentences together: the config
says WHEN a vendor is dear, and `CLOCK_STATES` below says WHICH MODE each price
band selects.

THE CLOCK BELONGS TO THE VENDOR, from the owner's instruction of 2026-08-15.
The peak and off-peak clock exists because DEEPSEEK prices that way, so the
clock runs only while the vendor in force declares price bands. A vendor that
bills one flat price gives the clock no basis, and `auto` then resolves to that
vendor's `default_mode`. A pin in `VERSION_IN_FORCE` still beats both.

DELETE `dev/vendors.toml` AND NOTHING BREAKS. `BUILTIN_VENDOR` below then
supplies the data this file carried before the config existed.
"""

from __future__ import annotations

import sys
import tomllib
from dataclasses import dataclass
from datetime import datetime, time, timedelta, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# THE SWITCH. One of two values, and the order of power is visible here.
#   a mode name ("pi-subagent-mode", "in-harness-subagent-mode"): a
#     PIN. The owner set it by word. It wins over the clock, always.
#   "auto": the clock picks the mode from the Beijing-time peak windows
#     below. The owner's instruction of 2026-08-14 made the clock the rule;
#     a mode named here overrides it.
# ---------------------------------------------------------------------------

AUTO = "auto"
VERSION_IN_FORCE = "pi-subagent-mode"

# The pin's own provenance. A position without a reason is a position nobody
# can retire.
#
# WHAT THIS PIN REPLACED: `auto`, set 2026-08-14, which delegated the mode to
# deepseek's peak and off-peak clock. That reason is recorded below and it is
# not a judgement on any head. It stopped applying when the vendor changed:
# `dev/vendors.toml` now names `zai`, a SUBSCRIPTION with no hourly bands, so
# the clock it delegated to has no basis left to read.
SET_ON = "2026-08-15"
SET_BY = "the repository owner"
REASON = ("The owner's instruction of 2026-08-15: pi is now on the zai "
          "subscription rather than deepseek, and the owner will name the "
          "mode DAILY from the token consumption they can see and the "
          "orchestrator cannot. So the mode is pinned by word rather than "
          "derived, and this pin says pi leads. The outgoing state was "
          "`auto`, whose own reason was deepseek's peak and off-peak "
          "pricing: OFF-PEAK deepseek was half price and pi led; PEAK it was "
          "dear and the in-harness Opus, not billed on that clock, led. That "
          "reason retired with the vendor and never reflected on a head.")
REVERT_CONDITION = ("The owner names a mode by word, daily. Set "
                    "VERSION_IN_FORCE to `pi-subagent-mode` or "
                    "`in-harness-subagent-mode` and change nothing else. "
                    "Setting it back to `auto` delegates to the vendor again, "
                    "which means the clock for a banded vendor and "
                    "`default_mode` for a flat one; with `zai` in force that "
                    "is `pi-subagent-mode` today, but it is derived rather "
                    "than ruled and the owner's daily word is the rule now.")

# ---------------------------------------------------------------------------
# THE VENDOR. `dev/vendors.toml` is its ONE home, and this file holds no vendor
# data except the compatibility floor below.
# ---------------------------------------------------------------------------
#
# WHY A CONFIG FILE, from the owner's instruction of 2026-08-15: the model that
# `pi-subagent-mode` runs on must be switchable between vendors without an edit
# to this file. A vendor row is DATA. A head table is POLICY. DD19 forbids a
# rule being canonical twice, so the two never restate each other.
#
# THE CAVEAT IS THE OWNER'S OWN. `pi` is wired to deepseek and to nothing else
# today. A vendor is DECLARABLE before `pi` can run it, and `pi_wired` records
# which is which. `require_vendor_wired()` refuses LOUDLY when an unwired vendor
# is in force and a head must start, because a silent default is the shape a
# wrong choice hides in (`dev/LESSONS.md` C-43).

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

CONFIG_PATH = find_root(__file__) / "dev" / "vendors.toml"


@dataclass(frozen=True)
class Vendor:
    """One vendor's data.

    A BANDED vendor prices by the hour: it declares `windows` and `base_state`,
    and it drives the clock. A FLAT vendor prices the same at every hour: it
    declares `default_mode`, and the clock does not run for it at all. The two
    kinds are exclusive, and the loader refuses a row that is both or neither.
    """

    name: str
    model: str
    pi_provider: str
    pi_wired: bool
    base_state: str | None
    windows: tuple[tuple[int, int, int, int, str], ...]
    default_mode: str | None
    source: str

    @property
    def banded(self) -> bool:
        """True when this vendor prices by the hour, so the clock has a basis."""
        return bool(self.windows)


# THE COMPATIBILITY FLOOR, AND IT IS NOT A SECOND HOME. This holds the data this
# file carried as literals before `dev/vendors.toml` existed: the model from the
# old vendor seam, and the two Beijing windows the owner set on 2026-08-14. It is
# read ONLY when the config file is absent, so deleting the config cannot break a
# dispatch. When the config exists it wins whole, and no field of this default
# merges into it.
BUILTIN_VENDOR = Vendor(
    name="deepseek",
    model="deepseek-v4-pro",
    pi_provider="deepseek",
    pi_wired=True,
    base_state="off-peak",
    windows=((9, 0, 12, 0, "peak"), (14, 0, 18, 0, "peak")),
    default_mode=None,
    source="the built-in default, because dev/vendors.toml is absent",
)

_KNOWN_FIELDS = ("model", "pi_provider", "pi_wired", "base_state", "windows",
                 "default_mode")
_KNOWN_WINDOW_FIELDS = ("state", "start", "end")


def _reject(path, what: str) -> SystemExit:
    """Every vendor refusal, in one shape.

    It names the file, the fault and the fix. A refusal a reader cannot act on
    is only a crash. `SystemExit` is this file's established loud idiom: it is
    what `in_force()` already raises on an unreadable switch, and a consumer
    that wraps the import in `except Exception` does NOT swallow it.
    """
    return SystemExit(f"dispatch_policy: {path}: {what}")


def _hhmm(path, value, where: str) -> tuple[int, int]:
    """A `"HH:MM"` string as (hour, minute), Beijing time."""
    if not isinstance(value, str):
        raise _reject(path, f'{where} must be a string like "09:00", not '
                            f'{value!r}.')
    parts = value.split(":")
    if len(parts) != 2 or not all(p.isdigit() and len(p) == 2 for p in parts):
        raise _reject(path, f'{where} must read "HH:MM" with two digits in each '
                            f'half, not {value!r}.')
    hour, minute = int(parts[0]), int(parts[1])
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        raise _reject(path, f"{where} is {value!r}, which is not a real time of "
                            f"day.")
    return hour, minute


def _vendor_from(path, name: str, row: object, source: str) -> Vendor:
    """One `[vendors.<name>]` table as a `Vendor`, or a loud refusal."""
    if not isinstance(row, dict):
        raise _reject(path, f"`[vendors.{name}]` must be a table.")
    extra = sorted(set(row) - set(_KNOWN_FIELDS))
    if extra:
        raise _reject(path, f"`[vendors.{name}]` declares unknown field(s) "
                            f"{', '.join(extra)}. The fields this loader reads "
                            f"are {', '.join(_KNOWN_FIELDS)}. A field nothing "
                            f"reads is never ignored in silence.")

    model = row.get("model")
    if not isinstance(model, str) or not model.strip():
        raise _reject(path, f"`[vendors.{name}]` must declare `model`, the model "
                            f"ID this vendor runs, as a non-empty string.")
    provider = row.get("pi_provider")
    if not isinstance(provider, str) or not provider.strip():
        raise _reject(path, f"`[vendors.{name}]` must declare `pi_provider`, the "
                            f"provider name `pi` needs, as a non-empty string.")
    wired = row.get("pi_wired")
    if not isinstance(wired, bool):
        raise _reject(path, f"`[vendors.{name}]` must declare `pi_wired` as true "
                            f"or false. It records whether `pi` can really run "
                            f"this vendor today, and it has no default.")

    windows_raw = row.get("windows", [])
    if not isinstance(windows_raw, list):
        raise _reject(path, f"`[vendors.{name}]` `windows` must be a list of "
                            f"tables.")
    banded = bool(windows_raw)
    base_state = row.get("base_state")
    default_mode = row.get("default_mode")

    if banded and default_mode is not None:
        raise _reject(path, f"`[vendors.{name}]` declares both `windows` and "
                            f"`default_mode`. A banded vendor drives the clock "
                            f"and the clock picks the mode, so `default_mode` "
                            f"would never be read. Delete one of the two.")
    if not banded and default_mode is None:
        raise _reject(path, f"`[vendors.{name}]` declares no window, so the clock "
                            f"has no basis and `VERSION_IN_FORCE = 'auto'` has "
                            f"nothing to ask. Declare `default_mode`, the mode "
                            f"`auto` resolves to for this vendor. There is no "
                            f"silent fallback (C-43).")
    if not banded and base_state is not None:
        raise _reject(path, f"`[vendors.{name}]` declares no window, so it has one "
                            f"price band and `base_state` names nothing. Delete "
                            f"it.")
    if banded and base_state is None:
        raise _reject(path, f"`[vendors.{name}]` declares windows, so it must "
                            f"declare `base_state`, the band that holds outside "
                            f"every window.")
    if default_mode is not None and (not isinstance(default_mode, str)
                                     or not default_mode.strip()):
        raise _reject(path, f"`[vendors.{name}]` `default_mode` must be a "
                            f"non-empty string naming a mode.")
    if base_state is not None and (not isinstance(base_state, str)
                                   or not base_state.strip()):
        raise _reject(path, f"`[vendors.{name}]` `base_state` must be a non-empty "
                            f"string naming a price band.")

    parsed: list[tuple[int, int, int, int, str]] = []
    for i, win in enumerate(windows_raw, 1):
        where = f"`[vendors.{name}]` window {i}"
        if not isinstance(win, dict):
            raise _reject(path, f"{where} must be a table with `state`, `start` "
                                f"and `end`.")
        extra_w = sorted(set(win) - set(_KNOWN_WINDOW_FIELDS))
        if extra_w:
            raise _reject(path, f"{where} declares unknown field(s) "
                                f"{', '.join(extra_w)}. A window reads "
                                f"{', '.join(_KNOWN_WINDOW_FIELDS)}.")
        state = win.get("state")
        if not isinstance(state, str) or not state.strip():
            raise _reject(path, f"{where} must declare `state`, the price band it "
                                f"names, as a non-empty string.")
        sh, sm = _hhmm(path, win.get("start"), f"{where} `start`")
        eh, em = _hhmm(path, win.get("end"), f"{where} `end`")
        if (sh, sm) >= (eh, em):
            raise _reject(path, f"{where} ends at or before it starts "
                                f"({sh:02d}:{sm:02d} to {eh:02d}:{em:02d}). A "
                                f"window never crosses midnight. Write two "
                                f"windows instead.")
        if state.strip() == str(base_state).strip():
            raise _reject(path, f"{where} names the band `{state.strip()}`, which "
                                f"is already this vendor's `base_state`. The "
                                f"window would change nothing. Delete it.")
        parsed.append((sh, sm, eh, em, state.strip()))

    for first, second in zip(parsed, parsed[1:]):
        if (second[0], second[1]) < (first[2], first[3]):
            raise _reject(path, f"`[vendors.{name}]` windows must be ordered by "
                                f"start time and must not overlap. A window opens "
                                f"at {second[0]:02d}:{second[1]:02d}, before the "
                                f"one closing at {first[2]:02d}:{first[3]:02d}.")

    return Vendor(
        name=name,
        model=model.strip(),
        pi_provider=provider.strip(),
        pi_wired=wired,
        base_state=base_state.strip() if isinstance(base_state, str) else None,
        windows=tuple(parsed),
        default_mode=(default_mode.strip()
                      if isinstance(default_mode, str) else None),
        source=source,
    )


def load_vendor(path=None) -> Vendor:
    """The vendor the config puts in force.

    `path` defaults to `CONFIG_PATH`; the tests pass a probe file instead, so
    every branch below is reachable without moving the real config.

    AN ABSENT FILE GIVES `BUILTIN_VENDOR`, and that is the ONLY quiet path here.
    It is quiet because it is today's data, unchanged, which is what makes
    deleting the config safe. EVERY OTHER FAULT RAISES, and names the vendor.
    """
    p = Path(path) if path is not None else CONFIG_PATH
    if not p.exists():
        return BUILTIN_VENDOR
    try:
        data = tomllib.loads(p.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise _reject(p, f"cannot be read as TOML ({exc}). Fix it, or delete it "
                         f"and the built-in vendor `{BUILTIN_VENDOR.name}` "
                         f"applies.")
    extra = sorted(set(data) - {"in_force", "vendors"})
    if extra:
        raise _reject(p, f"declares unknown top-level key(s) {', '.join(extra)}. "
                         f"This file reads `in_force` and `[vendors.<name>]` "
                         f"only.")
    name = data.get("in_force")
    if not isinstance(name, str) or not name.strip():
        raise _reject(p, "must declare `in_force`, the name of the vendor in "
                         "force, as a non-empty string.")
    name = name.strip()
    vendors = data.get("vendors")
    if not isinstance(vendors, dict) or not vendors:
        raise _reject(p, "must declare at least one `[vendors.<name>]` table.")
    if name not in vendors:
        raise _reject(p, f"`in_force` names the vendor `{name}`, which has no "
                         f"`[vendors.{name}]` table. The declared vendors are: "
                         f"{', '.join(sorted(vendors))}. A vendor this file does "
                         f"not declare is never guessed (C-43).")
    return _vendor_from(p, name, vendors[name], f"{p}, `in_force = \"{name}\"`")


VENDOR = load_vendor()


def vendor() -> Vendor:
    """The vendor in force. Read it; never rebuild it from the config."""
    return VENDOR


def require_vendor_wired(v: Vendor | None = None) -> None:
    """Refuse when the vendor in force is one `pi` cannot run.

    THIS IS THE LOUD HALF OF PART 1. A vendor is DECLARABLE before `pi` is wired
    to it, which is what lets the owner open compatibility ahead of need. What
    must never happen is a dispatch that starts a head on a vendor nothing can
    run and finds out later. So the refusal fires at `default_harness()`, the one
    call `dispatch.py` makes before it launches, and EVERY head that call can
    return runs on the vendor's model.

    IT DOES NOT FIRE INSIDE `head()` OR `tier_token()`, deliberately. Those two
    judge FROZEN RECORDS as well as live dispatches, and a record must stay
    readable whatever the config says today (C-41).
    """
    v = v or VENDOR
    if v.pi_wired:
        return
    raise SystemExit(
        f"dispatch_policy: the vendor in force is `{v.name}`, and its row says "
        f"`pi_wired = false`. `pi` is NOT wired to `{v.name}`, so no head can "
        f"start on the model `{v.model}`. Source: {v.source}. Set `in_force` to "
        f"a wired vendor in {CONFIG_PATH}, or wire `pi` to `{v.name}` and set "
        f"`pi_wired = true` in the same row. This is a refusal, not a reminder: "
        f"a declaration is not a wiring.")


# ---------------------------------------------------------------------------
# THE CLOCK, AND IT BELONGS TO THE VENDOR.
# ---------------------------------------------------------------------------
#
# THE OWNER'S INSTRUCTION, 2026-08-15. The peak and off-peak clock exists
# because DEEPSEEK prices that way. So the clock runs only while the vendor in
# force declares price bands. A FLAT vendor gives it no basis, and `auto` then
# resolves to that vendor's `default_mode` instead. A pin beats both.
#
# THE WINDOWS ARE THE VENDOR'S, and `dev/vendors.toml` holds them. They are in
# BEIJING time, which the rule states. The conversion from UTC is explicit in
# `beijing_now()`: Beijing is UTC+8 with no daylight saving, so the offset is a
# constant and a machine in any zone gets the same answer.
#
# THE WINDOWS ARE HALF-OPEN [start, end) at minute resolution. A minute belongs
# to the window that STARTED at its hour: 11:59 is peak, 12:00 is off-peak;
# 17:59 is peak, 18:00 is off-peak. The boundary instant itself belongs to the
# window that is starting, so 09:00:00 and 14:00:00 are peak and 12:00:00 and
# 18:00:00 are off-peak.
#
# CLOCK_STATES IS POLICY AND IT STAYS HERE. The config says WHEN a vendor is in
# a band. This table says WHICH MODE the band selects, which is a decision about
# HEADS. That is the DD19 line, and `dev/vendors.toml` states the same line from
# the other side. A vendor with a third band adds one row here and two in the
# config.

# The mode each clock state selects. The two states and the two modes are the
# whole economics: off-peak deepseek is half price, peak it is dear.
CLOCK_STATES: dict[str, str] = {
    "peak": "in-harness-subagent-mode",
    "off-peak": "pi-subagent-mode",
}

# THE RETIRED VIEW, kept because it costs one line. `PEAK_WINDOWS` was this
# file's window table until the vendor config took it. It now reads the vendor's
# peak band only, so a reader of the old name still gets the old answer.
# MEASURED 2026-08-15: no file outside this one reads it.
PEAK_WINDOWS: tuple[tuple[int, int, int, int], ...] = tuple(
    (sh, sm, eh, em) for sh, sm, eh, em, st in VENDOR.windows if st == "peak")

BEIJING_TZ = timezone(timedelta(hours=8))


def beijing_now(now: datetime | None = None) -> datetime:
    """Beijing wall-clock time for an instant.

    THE CONVERSION IS EXPLICIT, because the rule is stated in Beijing time
    and a machine in another zone must get the same answer. The input is
    converted from its own zone (UTC when none is given) to UTC+8; the
    machine's local zone is never read.
    """
    t = now or datetime.now(timezone.utc)
    return t.astimezone(BEIJING_TZ)


def _no_clock() -> SystemExit:
    """The refusal that anything asking the clock gets from a flat vendor.

    It is a refusal and never a fallback. A clock that answered `off-peak` for
    a vendor with no bands would be inventing a price, and the mode would follow
    the invention (C-43).
    """
    v = VENDOR
    return SystemExit(
        f"dispatch_policy: the vendor in force is `{v.name}`, which declares no "
        f"price window, so the clock has no basis and must not be read. The peak "
        f"clock exists because a vendor prices by the hour, and `{v.name}` does "
        f"not. Under `VERSION_IN_FORCE = {AUTO!r}` the mode is that vendor's "
        f"`default_mode`, which is `{v.default_mode}`, and a pin still beats "
        f"both. Source: {v.source}.")


def _state_at(hour: int, minute: int) -> str:
    """The vendor's price band at a Beijing wall-clock time."""
    if not VENDOR.banded:
        raise _no_clock()
    hm = (hour, minute)
    for sh, sm, eh, em, state in VENDOR.windows:
        if (sh, sm) <= hm < (eh, em):
            return state
    return str(VENDOR.base_state)


def clock_state(now: datetime | None = None) -> str:
    """The vendor's price band from the Beijing wall clock at `now`.

    For a two-band vendor such as deepseek that is `peak` or `off-peak`, which
    is what it has always been. A vendor with three bands returns the third name
    here, and `CLOCK_STATES` maps it.
    """
    bj = beijing_now(now)
    return _state_at(bj.hour, bj.minute)


def clock_mode(now: datetime | None = None) -> str:
    """The mode the clock selects at `now`."""
    state = clock_state(now)
    if state not in CLOCK_STATES:
        # The loader already refuses an unknown band at import. This is the last
        # line of defence, so the failure names the band instead of raising a
        # bare KeyError.
        raise SystemExit(
            f"dispatch_policy: the vendor `{VENDOR.name}` is in the price band "
            f"`{state}`, and `CLOCK_STATES` has no row for it. Add the row that "
            f"says which mode that band selects.")
    return CLOCK_STATES[state]


def _boundaries(day) -> list[tuple[datetime, str]]:
    """Today's band boundaries, plus tomorrow's first, so the list is never
    empty. The state named is the state AFTER the boundary.

    THE BOUNDARY SET IS EVERY WINDOW START AND EVERY WINDOW END, and the state
    after each one is read back off the windows. Two adjacent bands therefore
    share one boundary instead of producing two, which is what makes a third
    band cost nothing here.
    """
    if not VENDOR.banded:
        raise _no_clock()
    marks = sorted({time(sh, sm) for sh, sm, _, _, _ in VENDOR.windows}
                   | {time(eh, em) for _, _, eh, em, _ in VENDOR.windows})
    out = [(datetime.combine(day, t, tzinfo=BEIJING_TZ),
            _state_at(t.hour, t.minute)) for t in marks]
    first = marks[0]
    out.append((datetime.combine(day + timedelta(days=1), first,
                                 tzinfo=BEIJING_TZ),
                _state_at(first.hour, first.minute)))
    return out


def next_boundary(now: datetime | None = None) -> tuple[datetime, str]:
    """(the next instant the clock state changes, the state after it)."""
    bj = beijing_now(now)
    future = [(t, s) for t, s in _boundaries(bj.date()) if t > bj]
    return min(future, key=lambda x: x[0])


def current_window(now: datetime | None = None) -> tuple[datetime | None, datetime, str]:
    """(start, end, state) of the window `now` falls in, Beijing time.
    The start is the last boundary at or before now, the end the next one,
    and the state is constant between them."""
    bj = beijing_now(now)
    bs = _boundaries(bj.date())
    past = [(t, s) for t, s in bs if t <= bj]
    future = [(t, s) for t, s in bs if t > bj]
    start = past[-1][0] if past else None
    end = future[0][0]
    return start, end, clock_state(bj)


# ---------------------------------------------------------------------------
# THE TWO TABLES. This is their ONE home. Nothing restates them.
# ---------------------------------------------------------------------------
#
# A HEAD has two parts under this policy:
#   harness   what runs the agent. `herdr` is the pane server; `in-harness` is
#             an Opus subagent inside the orchestrator's own session, which
#             dispatch.py cannot start.
#   agent     which coding agent runs inside it: `pi`, `codex`, or `opus 5`.
#
# THE CASES:
#   default             an ordinary dispatch of any kind.
#   adversarial         a negative return's review (DD25), or any adversarial
#                       review. THE CRITIC IS NEVER THE SAME HEAD AS THE
#                       AUTHOR, which is why the two tables swap this row and
#                       the default row. `.claude/skills/codex-dispatch/
#                       SKILL.md` states the same rule.
#   fallback            the head to use when the case's own head is unavailable.

# THE VENDOR SEAM MOVED, 2026-08-15 (`[LJ-1.288]`). It was this line, and the
# comment here said a vendor swap is one edit to a literal string. THAT IS NO
# LONGER TRUE, and the sentence is corrected rather than deleted: a vendor swap
# is now one edit to `in_force` in `dev/vendors.toml`, and this file holds no
# vendor literal outside `BUILTIN_VENDOR`. Every mode, table and comment
# elsewhere here names a HEAD (`pi`, `codex`, `opus 5`), never the vendor behind
# it. `[LJ-1.285]` took the vendor name off the mode identifiers for the same
# reason.
#
# MODEL AND PI_PROVIDER STAY AS MODULE NAMES, because consumers read them:
# `scripts/dispatch/check-dispatch-policy.py:191` tests a governed document for the model
# string. The NAMES did not change; only where their values come from did.
#
# THERE IS ONE MODEL HERE AND THAT IS DELIBERATE. Pass any other model with
# `dispatch.py --model`; nothing in this file has an opinion about which.
MODEL = VENDOR.model

# The provider name `pi` needs for the vendor in force. It is exposed so the
# dispatcher can read it instead of carrying its own copy; the vendor name
# belongs to the config, not to a caller.
PI_PROVIDER = VENDOR.pi_provider

# THE MODEL RULE IS REVOKED, 2026-08-15, by the repository owner, in their own
# words: the flash rule and its code are deleted and the rule is void from now
# on, because pure natural-language work is nearly always started BY THE OWNER,
# who will say so, and no automatic judgement is needed.
#
# WHAT WAS HERE. `FLASH = "deepseek-v4-flash"` and
# `model_for(runs_agda) -> MODEL if runs_agda else FLASH`, ruled 2026-08-14 by
# the same owner. It hung on `dispatch.py`'s existing `--agda` flag, so it cost
# no new declaration.
#
# WHY THE REVOCATION COSTS NOTHING, MEASURED 2026-08-15 before it was made:
# `model_for` had NO CALLER anywhere in the repository. `dispatch.py` hardcoded
# `DEFAULT_MODEL = "deepseek-v4-pro"` at :82 and never consulted it, no document
# stated the rule (zero hits for `flash` in AGENTS.md, dev/ORCHESTRATION.md and
# dev/PLAN.md), and no checker enforced it. It was a rule written as code that
# nothing executed, which AGENTS.md calls a wish, and worse than a wish because
# code reads as enforced.
#
# FROZEN BRIEFS THAT CITE IT STAY AS THEY ARE. Several say "the model rule gives
# flash and I take it". A brief is a record and a record is never rewritten
# (C-41). Those dispatches really were made under the rule, and the sentence was
# true on the day.

#: THE RETIRED NAMES, and they must keep resolving. `normal` and `override` said
#: WHICH ONE WAS THE EXCEPTION and never WHICH HEAD LEADS, so a reader had to
#: open this file to learn what either meant. The owner renamed them
#: 2026-08-14, by the head each one leads with.
#:
#: **52 frozen briefs carry `override` on their tier line.** A brief is a
#: record and a record is never rewritten, so the old names resolve here
#: forever. `dev/LESSONS.md` C-41 is the law: a retired name that stops
#: resolving turns every citation of it into a dangling pointer, and one that
#: resolves to the WRONG thing is worse still.
#:
#: `deepseek-subagent-mode` RETIRED 2026-08-15 (`[LJ-1.285]`), renamed to
#: `pi-subagent-mode`: the owner's instruction was to take the vendor name off
#: a structural concept, because staying on one vendor was never guaranteed and
#: a name tied to one vendor costs a repository sweep when the vendor changes.
#: **MEASURED 2026-08-15: 189 occurrences across 166 frozen files under
#: `agents/` carry `deepseek-subagent-mode` on their tier line**, so it
#: resolves here forever, the same as `override`. `normal` is re-pointed to the
#: new name so it still resolves in one hop.
ALIASES: dict[str, str] = {
    "normal": "pi-subagent-mode",
    "override": "in-harness-subagent-mode",
    "deepseek-subagent-mode": "pi-subagent-mode",
}


def canonical(version: str) -> str:
    """The live name for a version, whether it is written new or retired."""
    v = version.strip().lower()
    return ALIASES.get(v, v)


POLICY: dict[str, dict] = {
    "pi-subagent-mode": {
        "summary": "The steady state. pi leads, codex backs it up, Opus reviews.",
        "cases": {
            "default": {
                "harness": "herdr",
                "agent": "pi",
                "model": MODEL,
                "tier_token": "pi",
            },
            "adversarial": {
                "harness": "in-harness",
                "agent": "opus 5",
                "model": "",
                "tier_token": "opus",
            },
            "fallback": {
                "harness": "herdr",
                "agent": "codex",
                "model": MODEL,
                "tier_token": "codex",
            },
        },
        "note": ("THE DEFAULT IS pi, NOT codex, and that is a real change to "
                 "DD17 rather than a restatement of it. DD17 as first written "
                 "made codex the default for EVERY dispatch. [LJ-1.126] made "
                 "pi viable on 2026-08-13 by landing streaming and resume."),
    },
    "in-harness-subagent-mode": {
        "summary": "Opus leads while the owner's weekly allowance permits it.",
        "cases": {
            "default": {
                "harness": "in-harness",
                "agent": "opus 5",
                "model": "",
                "tier_token": "opus",
            },
            "adversarial": {
                "harness": "herdr",
                "agent": "pi",
                "model": MODEL,
                "tier_token": "pi",
            },
            "fallback": {
                "harness": "herdr",
                "agent": "codex",
                "model": MODEL,
                "tier_token": "codex",
            },
        },
        "note": ("TEMPORARY. The reason is quota, never quality. The two "
                 "tables swap the default row and the adversarial row, "
                 "because the invariant under both versions is that THE "
                 "CRITIC IS NEVER THE SAME HEAD AS THE AUTHOR."),
    },
}

# The invariant that survives both versions, stated once so a third version
# cannot be written without it.
INVARIANT = "The critic must not be the author."

# The `tier:` tokens a brief may legally carry. `fable` is DD17's emergency
# breakthrough tier: it sits outside both tables, needs its trigger named in
# the brief, and is never a default.
EMERGENCY_TOKEN = "fable"
LEGAL_TOKENS = ("opus", "pi", "codex", EMERGENCY_TOKEN)

# How a head maps onto `dispatch.py --harness`. `in-harness` has NO mapping,
# and that absence is the honest limit above: dispatch.py cannot start an Opus
# subagent, so a case whose head is in-harness has no harness at all.
HARNESS_FOR_AGENT = {"pi": "herdr-pi", "codex": "herdr"}


# --------------------------------------------------------------------------- api


def auto_mode() -> str:
    """What `auto` resolves to, and it answers the one question a vendor config
    opens.

    A BANDED vendor gives the clock a basis, so the clock decides, exactly as it
    did before this file had a config. A FLAT vendor gives the clock no basis, so
    the mode is that vendor's declared `default_mode`.

    THERE IS NO THIRD PATH AND NO SILENT ONE. A flat vendor that names no
    `default_mode` is refused when the config loads, so this function cannot
    reach a state where it must guess (C-43).
    """
    if VENDOR.banded:
        return clock_mode()
    return canonical(str(VENDOR.default_mode))


def in_force() -> str:
    """The mode in force. A pinned mode wins; `auto` delegates to the vendor,
    which means the clock for a banded vendor and `default_mode` for a flat one.
    A pin written as a RETIRED name resolves through `ALIASES` too (C-41), so
    the switch works even if someone pins it by the old word. Raises when the
    switch holds an unknown value, because a policy nobody can read must stop
    rather than pick one."""
    if VERSION_IN_FORCE == AUTO:
        return auto_mode()
    v = canonical(VERSION_IN_FORCE)
    if v not in POLICY:
        raise SystemExit(
            f"dispatch_policy: VERSION_IN_FORCE is {VERSION_IN_FORCE!r}, which "
            f"is not one of {', '.join(sorted(POLICY))} and not {AUTO!r}. Fix "
            f"the switch in {__file__}.")
    return v


def table(version: str | None = None) -> dict:
    """The policy table for a version. A retired name resolves through
    `ALIASES` (C-41) before the lookup, so a caller may pass the old word."""
    return POLICY[canonical(version) if version else in_force()]


def head(case: str, version: str | None = None) -> dict:
    """The head for one case under one version."""
    return table(version)["cases"][case]


def tier_token(case: str, version: str | None = None) -> str:
    return head(case, version)["tier_token"]


def default_harness(version: str | None = None) -> str | None:
    """What `dispatch.py` uses when no `--harness` is given.

    THIS IS AUTHORITATIVE, because dispatch.py reads it.

    The rule: dispatch.py can only run a head whose harness is `herdr`. Under
    `normal` the default case is herdr plus pi, so that is the answer. Under
    `override` the default case is an in-harness Opus subagent, which this tool
    cannot start at all; the nearest head it CAN run is the fallback, herdr
    plus codex. So an override-era dispatch that reaches dispatch.py with no
    `--harness` is by definition NOT the default case, and the fallback is the
    honest default for it.

    THE VENDOR IS CHECKED FIRST, and this is the point where an unwired vendor
    stops a dispatch. Every head this function can return runs on the vendor's
    model, so the answer would be a head nothing can start.
    """
    require_vendor_wired()
    d = head("default", version)
    if d["harness"] == "in-harness":
        d = head("fallback", version)
    return HARNESS_FOR_AGENT.get(d["agent"])


def expected_tier_tokens(case: str, version: str | None = None) -> set[str]:
    """The tokens a brief of this case may legally carry.

    The fallback is always legal: a head can be unavailable on any day, and a
    brief that says so is not a policy breach. The emergency tier is legal
    everywhere for the same reason, and DD17 makes its trigger the brief's job
    to name.
    """
    return {tier_token(case, version), tier_token("fallback", version),
            EMERGENCY_TOKEN}


def _window_lines() -> list[str]:
    """One line per price band the vendor declares, in declaration order.

    A TWO-BAND VENDOR PRINTS ONE LINE, and it is the line this file printed
    before it had a config: `peak windows (Beijing): 09:00 to 12:00, 14:00 to
    18:00`. A three-band vendor prints two lines, and nothing else changes.
    """
    order: list[str] = []
    for *_rest, state in VENDOR.windows:
        if state not in order:
            order.append(state)
    return [f"  {state} windows (Beijing): "
            + ", ".join(f"{sh:02d}:{sm:02d} to {eh:02d}:{em:02d}"
                        for sh, sm, eh, em, st in VENDOR.windows if st == state)
            for state in order]


def _harness_line(version: str) -> str:
    """The default-harness answer, or the vendor refusal that replaces it.

    THE INSPECTION COMMAND MUST STILL PRINT when the vendor is unwired. A reader
    who has just set an unrunnable vendor needs to SEE why, and a traceback is
    not a reading. The refusal still fires at every dispatch path.
    """
    try:
        return (default_harness(version)
                or "(none: the default head is in-harness)")
    except SystemExit as exc:
        return f"REFUSED. {exc}"


def render(version: str | None = None) -> str:
    """Render the policy. `None` or `'auto'` renders what is in force; a mode
    name renders that mode's table with the (NOT the switch's value) marker
    when it is not the pin. A retired name resolves through `ALIASES` (C-41)
    and renders under its live name."""
    explicit = version is not None and version != AUTO
    v = version or in_force()
    if v == AUTO:
        v = in_force()
    v = canonical(v)
    t = POLICY[v]
    lines = [
        f"DISPATCH POLICY: `{v}` is IN FORCE"
        + ("" if not explicit else "   (NOT the switch's value)"),
    ]
    if VERSION_IN_FORCE == AUTO and VENDOR.banded:
        state = clock_state()
        start, end, _ = current_window()
        boundary, after_state = next_boundary()
        win = (f"{start:%H:%M} to {end:%H:%M}" if start
               else "(before today's first boundary)")
        lines += [
            f"  selected by the clock, not by a ruling "
            f"(VERSION_IN_FORCE = {AUTO!r})",
            f"  clock: {state.upper()} now. Beijing "
            f"{beijing_now():%Y-%m-%d %H:%M}, window {win}",
        ]
        lines += _window_lines()
        lines += [
            f"  next boundary: {boundary:%Y-%m-%d %H:%M} Beijing, "
            f"{after_state} begins, mode becomes "
            f"`{CLOCK_STATES[after_state]}`",
            f"  set {SET_ON} by {SET_BY}",
            f"  reason: {REASON}",
            f"  revert: {REVERT_CONDITION}",
        ]
    elif VERSION_IN_FORCE == AUTO:
        lines += [
            f"  selected by the vendor's `default_mode`, not by a ruling and "
            f"not by a clock (VERSION_IN_FORCE = {AUTO!r})",
            f"  vendor: `{VENDOR.name}` declares no price window, so the clock "
            f"has no basis and does not run",
            f"  default_mode: `{VENDOR.default_mode}`",
            f"  vendor source: {VENDOR.source}",
            f"  set {SET_ON} by {SET_BY}",
            f"  reason: {REASON}",
            f"  revert: {REVERT_CONDITION}",
        ]
    else:
        lines += [
            f"  set {SET_ON} by {SET_BY}",
            f"  reason: {REASON}",
            f"  revert: {REVERT_CONDITION}",
        ]
        if VERSION_IN_FORCE != AUTO:
            beaten = (f"the clock, which would select `{clock_mode()}` "
                      f"({clock_state()} now)" if VENDOR.banded else
                      f"the vendor default, which would select "
                      f"`{VENDOR.default_mode}` (`{VENDOR.name}` declares no "
                      f"price window, so there is no clock)")
            lines.append(
                f"  a PIN: `{VERSION_IN_FORCE}` is pinned and wins over "
                f"{beaten}")
    # THE MODEL COLUMN IS 18 WIDE OR THE MODEL, whichever is wider. 18 was a
    # literal until `[LJ-1.288]`, and it fitted `deepseek-v4-pro` exactly. A
    # vendor with a longer model ID would have pushed the `tier:` column out of
    # line. The floor of 18 keeps deepseek's table identical to the day before.
    mw = max(18, *(len(h["model"]) for h in t["cases"].values()))
    lines += [
        "",
        f"  {t['summary']}",
        "",
        f"  {'case':<14} {'harness':<12} {'agent':<8} {'model':<{mw}} tier:",
        f"  {'-' * 14} {'-' * 12} {'-' * 8} {'-' * mw} -----",
    ]
    for case, h in t["cases"].items():
        lines.append(f"  {case:<14} {h['harness']:<12} {h['agent']:<8} "
                     f"{h['model'] or '-':<{mw}} {h['tier_token']}")
    lines += [
        "",
        f"  INVARIANT, both versions: {INVARIANT}",
        f"  {t['note']}",
        "",
        f"  dispatch.py default harness under this version: "
        f"{_harness_line(v)}",
        "",
        "  THE LIMIT. This switch cannot force the orchestrator's choice. An",
        "  in-harness Opus dispatch never passes through dispatch.py. The",
        "  switch drives the default harness, the checker, and this printout,",
        "  and makes a wrong choice DETECTABLE. It does not make one",
        "  impossible.",
    ]
    return "\n".join(lines)


def _bands(v: Vendor) -> list[str]:
    """Every price band this vendor has, windows first and the base last."""
    order: list[str] = []
    for *_rest, state in v.windows:
        if state not in order:
            order.append(state)
    if v.base_state and v.base_state not in order:
        order.append(v.base_state)
    return order


def _validate_vendor_against_policy(v: Vendor | None = None) -> None:
    """The cross-checks the loader cannot make on its own.

    THE LOADER RUNS BEFORE `CLOCK_STATES` AND `POLICY` EXIST, so the checks that
    need them run here, once, when the module finishes loading. These are the
    checks that HOLD THE DD19 LINE. The config may NAME a band or a mode; this
    file decides whether that name is real, because what a band selects and what
    a mode is are both policy.
    """
    v = v or VENDOR
    for state in _bands(v):
        if state not in CLOCK_STATES:
            raise SystemExit(
                f"dispatch_policy: the vendor `{v.name}` names the price band "
                f"`{state}`, and `CLOCK_STATES` has no row for it. The known "
                f"bands are {', '.join(sorted(CLOCK_STATES))}. A new band needs "
                f"a row saying which mode it selects, and that row is a decision "
                f"about heads, so it belongs in this file and never in the "
                f"config. Source: {v.source}.")
    if v.default_mode is not None and canonical(v.default_mode) not in POLICY:
        raise SystemExit(
            f"dispatch_policy: the vendor `{v.name}` names `default_mode = "
            f"{v.default_mode!r}`, which is not a mode. The modes are "
            f"{', '.join(sorted(POLICY))}, and a retired name resolves through "
            f"ALIASES (C-41). Source: {v.source}.")


def render_vendor(v: Vendor | None = None) -> str:
    """The vendor view, printed by `dispatch_policy.py --vendor`.

    IT IS A SEPARATE COMMAND ON PURPOSE. The default printout is the POLICY, and
    `[LJ-1.288]` kept it line for line as it was, so that the vendor config is
    provably a change of shape and not a change of policy.
    """
    v = v or VENDOR
    out = [
        f"VENDOR IN FORCE: `{v.name}`",
        f"  source: {v.source}",
        f"  model: {v.model}",
        f"  pi provider: {v.pi_provider}",
        "  pi wired: " + ("yes" if v.pi_wired
                          else "NO. Every dispatch through this policy is "
                               "refused, by design"),
    ]
    if v.banded:
        out.append("  this vendor prices by the hour, so the clock runs")
        out += _window_lines()
        out.append(f"  outside every window: {v.base_state}")
        out.append("  each band selects: "
                   + ", ".join(f"{b} -> `{CLOCK_STATES[b]}`"
                               for b in _bands(v)))
    else:
        out.append("  this vendor prices one flat rate, so the clock does not "
                   "run and has no basis")
        out.append(f"  `auto` resolves to: `{v.default_mode}`")
    out += [
        "",
        "  THE DD19 LINE. This file holds the head tables, the two modes, the",
        "  invariant and the mode logic. `dev/vendors.toml` holds the vendor",
        "  rows printed above. Neither one restates the other.",
    ]
    return "\n".join(out)


def main() -> int:
    which = sys.argv[1] if len(sys.argv) > 1 else None
    if which in ("-h", "--help"):
        print("usage: dispatch_policy.py [auto|pi-subagent-mode|"
              "in-harness-subagent-mode|--vendor]")
        print("  no argument: print the mode the clock selects now")
        print("  --vendor: print the vendor in force, from dev/vendors.toml")
        print("  a retired name (deepseek-subagent-mode, normal, override) "
              "resolves through ALIASES, C-41")
        return 0
    if which == "--vendor":
        print(render_vendor())
        return 0
    if which and which != AUTO:
        which = canonical(which)
    if which and which != AUTO and which not in POLICY:
        print(f"unknown version {which!r}; known: auto, "
              f"{', '.join(sorted(POLICY))}", file=sys.stderr)
        return 2
    print(render(which))
    return 0


# THE CONFIG IS CHECKED WHEN THE MODULE LOADS, never at the first dispatch. A
# config fault that waits for a dispatch is a fault that lands in a launch log
# at the worst moment. C-48: a tool that can read a condition must refuse on it.
_validate_vendor_against_policy()


if __name__ == "__main__":
    sys.exit(main())
