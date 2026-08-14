# LJ-1.207 report: auto-switch the dispatch mode on DeepSeek's peak clock

## THE RULE, IN TWO LINES

The owner's pinned `VERSION_IN_FORCE` always wins. When it is `"auto"`, the
clock selects the mode from the Beijing-time peak windows, and the printout
shows the window in force and the next boundary.

**RIGHT NOW the mode is `in-harness-subagent-mode`.** MEASURED 2026-08-14
16:15: `scripts/dispatch_policy.py` printed `clock: PEAK now. Beijing
2026-08-14 16:15, window 14:00 to 18:00`. Beijing time is in the peak window
14:00 to 18:00, so the clock selects the in-harness mode, because deepseek is
dear in peak and the in-harness Opus is not billed on that clock. The next
boundary is 18:00 Beijing, when off-peak begins and the mode becomes
`deepseek-subagent-mode`.

## THE PRECEDENCE, QUOTED FROM THE CODE

The module docstring states the order first, so one read shows it
(`scripts/dispatch_policy.py:12-15`):

> THE PRECEDENCE, and it is the first thing to read in this file:
>
>   * The owner's pinned `VERSION_IN_FORCE` ALWAYS WINS. A pinned value is a
>     ruling, and a tool that silently overrides a ruling is worse than no tool.
>   * `VERSION_IN_FORCE = "auto"` delegates to the clock, which picks the mode
>     from DeepSeek's peak and off-peak windows in Beijing time. The clock
>     decides ONLY when the owner has not pinned a mode.

The switch block restates it beside the value (`scripts/dispatch_policy.py:
67-68`):

> PIN. The owner set it by word. It wins over the clock, always.

And `in_force()` implements the order (`scripts/dispatch_policy.py:336-345`):

> The mode in force. A pinned mode wins; `auto` delegates to the clock.
> ...
>     if VERSION_IN_FORCE == AUTO:
>         return clock_mode()
>     ...
>     return VERSION_IN_FORCE

MEASURED: with `VERSION_IN_FORCE = "deepseek-subagent-mode"` during peak,
`in_force()` returns `deepseek-subagent-mode`, and the render prints
`a PIN: ... is pinned and wins over the clock, which would select
`in-harness-subagent-mode` (peak now)` (`scripts/dispatch_policy.py:436-438`).
The pin wins in both directions: a pinned in-harness mode wins off-peak too
(pinned by the boundary test, `scripts/tests/test_dispatch_clock.py:120-127`).

## THE SIX BOUNDARY CASES, AND THE SIDE EACH FALLS ON

The windows are half-open `[start, end)` at minute resolution, documented at
`scripts/dispatch_policy.py:105-111`: a minute belongs to the window that
STARTED at its hour, and the boundary instant belongs to the window that is
starting. All six are pinned in `scripts/tests/test_dispatch_clock.py:59-64`
and verified MEASURED by running that test (34 checks passed):

| Beijing time | state | mode the clock selects |
|---|---|---|
| 08:59 | off-peak | `deepseek-subagent-mode` |
| 09:00 | peak | `in-harness-subagent-mode` |
| 12:00 | off-peak | `deepseek-subagent-mode` |
| 13:59 | off-peak | `deepseek-subagent-mode` |
| 14:00 | peak | `in-harness-subagent-mode` |
| 18:00 | off-peak | `deepseek-subagent-mode` |

The convention is pinned at second level too, so it cannot drift: 11:59:59 is
peak, 12:00:00 is off-peak, 17:59:59 is peak, 18:00:00 is off-peak
(`scripts/tests/test_dispatch_clock.py:74-81`).

## BEIJING TIME, NOT LOCAL TIME

The conversion is explicit in `beijing_now()` (`scripts/dispatch_policy.py:
130-139`): Beijing is UTC+8 with no daylight saving, so the offset is a
constant, and the input instant is converted from its own zone, never from
the machine's local zone. MEASURED: the test feeds the same instant as
09:00+05:00, 04:00 UTC and 12:00+08:00 and demands the same Beijing time and
the same state (`scripts/tests/test_dispatch_clock.py:91-95`). The machine
that ran the acceptance reads +08, but the conversion never reads it.

## THE INVARIANT, CONFIRMED NOT ASSUMED

DD17's invariant under both modes is that the critic is never the same head
as the author, and the two tables swap exactly the default row and the
adversarial row. The clock flips the default, so it must flip the adversarial
row with it. The test CONFIRMS it by equality, not by prose
(`scripts/tests/test_dispatch_clock.py:136-143`): for each mode the default
agent differs from the adversarial agent, and each mode's default row EQUALS
the other mode's adversarial row. MEASURED: all four checks passed. The
emergency tier is untouched: `fable` stays a legal token in every case and no
clock state can make it a default (`scripts/tests/test_dispatch_clock.py:
148-150`).

## A DISPATCH IN FLIGHT KEEPS ITS MODE

`dispatch.py` reads the policy once, when its process starts
(`.claude/skills/codex-dispatch/dispatch.py:111-112`), so a launch that
crosses a boundary keeps the harness that was correct at launch. The checker
judges a brief by the mode the brief NAMES, never by today's switch
(`scripts/check-dispatch-policy.py:220-230`): `chosen = P.canonical(m.group(1))
if m else version`. A frozen brief names its mode, so the clock cannot redden
it. MEASURED: zero post-epoch briefs carry a tier line with no version name,
so the `else version` fallback (the only clock-dependent path) reads nothing
today; the two pre-existing defects below both name `deepseek-subagent-mode`
on their tier lines and are judged by it.

## THE ACCEPTANCE TABLE

1. **Copied aside.** `scripts/dispatch_policy.py` is copied to
   `agents/tasks/LJ-1-207/lj-1.207-dispatch-policy.py.before` and the skill
   to `agents/tasks/LJ-1-207/lj-1.207-dispatch-herdr-SKILL.md.before`.
2. **`python3 scripts/dispatch_policy.py`** prints the version, the
   provenance, the clock selection, the window, the next boundary and the
   full table (MEASURED, exit 0). Both mode tables render by argument:
   `python3 scripts/dispatch_policy.py deepseek-subagent-mode` and
   `... in-harness-subagent-mode` (MEASURED, exit 0). `--help` and an unknown
   version exit 0 and 2 as before (MEASURED).
3. **`python3 scripts/check-dispatch-policy.py`**: IDENTICAL defect set
   before and after, exactly two defects, both pre-existing and both live
   dispatches that name `deepseek-subagent-mode` on their own tier lines:
   `agents/tasks/LJ-1-204/LJ-1.204.md:3` and `agents/tasks/LJ-1-208/
   LJ-1.208.md:3`. The clock reddened nothing. The footer line names the
   in-force mode, which is now the clock's pick (`against the
   in-harness-subagent-mode policy`); the judgment is unchanged.
4. **Six briefs through `dispatch.py check`**, identical before and after
   (MEASURED, run once before the edit and once after): LJ-1.157 refused
   with exit 1 (the control: no DD4, missing rule bundle), and LJ-1.203,
   LJ-1.205, LJ-1.206, LJ-1.200, LJ-1.201 each `well formed` with exit 0.
5. **The six boundary times are pinned** in `scripts/tests/
   test_dispatch_clock.py`, which passes 34 checks (MEASURED, exit 0).

`python3 -m py_compile scripts/dispatch_policy.py` and `python3 -m py_compile
scripts/tests/test_dispatch_clock.py` both pass after every edit (MEASURED).
No em dash appears in any file this task wrote or edited (MEASURED by grep).

## WHAT THE CLOCK CHANGES IN THE TOOL

`dispatch.py`'s no-`--harness` default follows the clock through
`default_harness()` (MEASURED 2026-08-14 16:15): off-peak it is `herdr-pi`
(the deepseek default), peak it is `herdr` (the codex fallback, because the
in-harness default head cannot be started by dispatch.py). A dispatch that
needs pi or codex during peak passes `--harness` explicitly. INFERRED: the
mode stays fixed for a dispatch's whole process lifetime, because
`dispatch.py` reads the policy at import.

## ARCHIVE USED

- `scripts/dispatch_policy.py`, read whole before edit (317 lines). Sites:
  the switch and provenance `:52-68` (old numbering), the two tables, the
  swap of default and adversarial rows, `ALIASES` and `canonical()` for the
  retired names, `model_for()` for the model rule, `default_harness()` for
  the in-harness fallback semantics, `render()` and `main()` for the print
  contract, the honest-limit block. Taken: the whole shape, preserved.
- `scripts/check-dispatch-policy.py`, read whole. Sites: the judged-by-the-
  named-version rule and its 2026-08-14 measurement `:220-230`; the epoch
  `:81`; the single-source model-string test; the refusal list. Taken: the
  guarantee that a clock change cannot redden a brief that names its mode.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole (529 lines). Sites:
  the modes section and both tables; the six-step switch checklist from DD17;
  the tier-line form; the in-harness-mode section. Taken: the checklist is
  kept true and the clock is added beside it as the auto path.
- `agents/tasks/LJ-1-203/lj-1.203-report.md`, read whole. Sites: the
  two-kind split of `dispatch.py` `:18-78`; no herdr feature can carry a
  refusal `:170-173`; the proposal `:319-330`. Taken: the refusals are
  project law and this task weakens none; a clock is not a refusal and
  belongs in the policy file, not in dispatch.py.
- `dev/PLAN.md` DD0 `:258`, DD17 `:268`, DD25 `:274`, and DD24 `:273`, read.
  Taken: DD17's six-step switch checklist and the invariant; DD0's rule that
  the owner's word binds the task it names; DD25's adversarial head comes
  from the switch. None edited.
- `dev/ORCHESTRATION.md` sections 1 to 3, read `:1-241`. Taken: the policy
  file is the one home of the tables and the head is never restated here;
  the enforcement points. None edited.
- `scripts/tests/test_agents_tree.py`, read for the test style (self-running
  check scripts). Taken: the FAIL/PASSED shape.

## LITERATURE USED

Not this task's subject. No literature bears on a clock rule.

## DD4, ANSWERED

The clock is written generic in the WINDOWS, not in the two modes. One table,
`PEAK_WINDOWS` (`scripts/dispatch_policy.py:115-120`), and one table,
`CLOCK_STATES` (`:122-127`). A second provider with different windows, or a
change to DeepSeek's hours, is one edit to `PEAK_WINDOWS` and nothing else;
the boundary test pins the current table so the edit is a deliberate act. The
two ends (the modes) share every other line of the file, and the clock
flips both the default row and the adversarial row by construction, which the
test confirms by equality.
