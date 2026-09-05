# LJ-1.336: wave 2 of the generic port, the dirty seven

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS IS OVERDUE

**Wave 1 landed and survived an adversarial review, and wave 2 was never
funded.**

- **`[LJ-1.306]` ported the CLEAN 23 `Agree` modules generic at ZERO changed
  lines**, one 45-line scaffold, `agents/tasks/LJ-1-306/GenAgree.agda`, exit 0.
- **`[LJ-1.308]` reviewed it at the emergency tier and UPHELD the zero**, by a
  stronger method than the target used: 0 deletes, 0 replaces, 146 of 146 exact
  runs. **It also found and ran 26 checks the target had missed, all green.**
- **`[LJ-1.302]` priced the dirty seven's ambient ties at about 100 lines,
  because「the ties are ONE debt, not sixteen」**, and built one at 51.

**Nothing has touched the dirty seven since. This task does wave 2.**

## THE QUESTION

**Port the seven dirty `Agree` modules generic, and measure what they cost
against the clean 23's zero.**

**「Dirty」means the module names committed deliveries in its types.**
`[LJ-1.308]` measured that FIVE of the「clean」23 were also not clean in that
sense, and **cured it at 27 non-blank lines copied verbatim, 0 changed.** **Read
that cure first: it is the shape your seven probably want.**

## WHAT IS ALREADY MEASURED, and you re-derive each (C-44)

- **The scaffold is ONE for all 23**, 45 load-bearing non-blank lines. **Does it
  serve the seven, or do they need a second?** **That is the first thing to
  measure and it decides the price.**
- **`[LJ-1.302]` built the ambient tie supply for ONE dirty module at 51 lines**
  and argued the seven share one debt. **Test that: is the second module's tie
  supply free, or another 51?**
- **`[LJ-1.307]` measured the family as ONE shape, about fifteen things, thirty
  spellings**, and that nine modules carry no mathematics of their own.

## WHAT NOT TO ASSUME

**`[LJ-1.331]` REFUTED the `RowTies` compression for SECONDS**, measured: one
record field exhausts 8 GB where the same hypothesis is free as a module
parameter, and law **C-55** records why. **Do not fold telescopes into records
in this port.** **Keep the parameter form the delivered code uses.**

**And `[LJ-1.322]` measured that this file's cost is NOT concentrated**: the
largest single definition is 2.6 percent. **So do not expect a seconds win from
the port and do not chase one.** **The port's value is LINES and genericity.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL SEVEN PORT.** Report the changed-line count against wave 1's zero, the
  scaffold's growth, and the tie supply's actual cost. STOP.
- **THE SCAFFOLD DOES NOT STRETCH.** **Name what the seven need that the 23 did
  not, at `file:line`, and price a second scaffold.**
- **THE TIES ARE NOT ONE DEBT.** **`[LJ-1.302]`'s claim is the load-bearing one
  and refuting it re-prices the route.** **Say so with the second module's
  measured cost.**
- **A MODULE WILL NOT PORT.** Name it and what it needs. **Six of seven is a
  real result.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.** **C-51 and C-55 are
  the two medicines this family has already earned.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-336/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-306/GenAgree.agda` and `agents/tasks/LJ-1-302/`; you may
  not change them.
- **`src/L/GCH.lagda.md` was RESTATED and `src/L/BoundedSubset.lagda.md` had a
  cure landed, both yesterday.** **Read the CURRENT files.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  A sibling may be live. Take ONE slot and report the load beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RUN A NEGATIVE CONTROL.** **`[LJ-1.308]` upheld wave 1 partly because a
  control existed; break a ported module deliberately and show Agda refuses at
  the exact point.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-336/lj-1.336-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Six of my last eight briefs carried a claim an agent measured FALSE.** **The
one at risk here: 「the ties are ONE debt」.** **It is `[LJ-1.302]`'s claim from
ONE built module, and P-l says a judgement at one site is a hypothesis at
another.** **Measure the second module before you price the seven.**

## THE RULES

**P-l, C-44, C-42, C-45, C-40, C-51, C-55, C-53, C-22, C-32, C-36, C-39.**
I-5. **D-1, D-10, D-26. DD0, DD4, DD8, DD13, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**This task IS DD4's own work at its largest site**: thirty near-identical
modules made generic once. **`[LJ-1.306]` measured its axis as
L-against-ambient, the Def tower's internal axis, and said the AC end gains
nothing. Re-derive that for the seven** and note `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-306/lj-1.306-report.md`, read WHOLE**, and its
  `GenAgree.agda`. Wave 1 is your pattern.
- **`agents/tasks/LJ-1-308/lj-1.308-report.md`**, the review that upheld it and
  found the five not-clean modules with their 27-line cure.
- **`agents/tasks/LJ-1-302/lj-1.302-report.md`**, the one built tie supply and
  the ONE-debt claim you must test.
- **`agents/tasks/LJ-1-307/lj-1.307-report.md`**, the family's partition.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route's `Condensation` was 885 lines with no `Agree` family at all.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.308]` measured that Devlin states
ZERO agreement lemmas because the bridge is paid ONCE in Chapter I, as a
language-level translation, while Bedrock proves it per NOTION.** **Say in one
line whether the generic port moves this development toward his shape or merely
compresses ours.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-306/lj-1.306-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-336/` only.

## RETURN

**Lead with ONE line: how many of the seven ported, and how many lines changed
against wave 1's zero.** Then whether one scaffold served. Then the second
module's tie supply cost, which tests the ONE-debt claim. Then your negative
control. Then the DD4 axis for the seven. **Mark every negative MEASURED or
INFERRED.**
