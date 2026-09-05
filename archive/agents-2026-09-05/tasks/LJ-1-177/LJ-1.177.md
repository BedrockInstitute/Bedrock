# LJ-1.177: cure the `*Agree` masters' second term, so the wing ends inside DD24

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**DD24 judges the WHOLE GCH wing against a bar fixed when the AC trophy landed.
The wing sits above that bar today, and only a CURE moves it down.**

`[LJ-1.155]` measured that the three `*Agree` masters carry a **second dominant
term** and that its cure is **WING-LOCAL**. That is the one cure shape that
improves the ratio, because it moves the numerator and leaves the denominator
alone.

**Find that term, cure it, and measure what the wing's aggregate does.**

## HOW TO READ DD24, RULED BY THE OWNER 2026-08-14

**DD24 is the whole rule, and the readings layered on it were the
orchestrator's own. Fundamentally:**

1. **The GCH bar was FIXED when the AC trophy landed. It does not drift.**
2. **EVERY GCH module uses that one number, new or old alike.**
3. **INTERMEDIATE DEBT IS ALLOWED**, because only the WHOLE GCH side, at the
   end, is judged against the bar.

**So this task is NOT debt collection and nothing here is urgent because of a
running total.** It is the work that decides whether the wing ENDS inside the
bar. **The wing is above the bar and a cure is what lowers it.**

## WHAT IS MEASURED, and every row is somebody else's measurement

| finding | source |
|---|---|
| the three `*Agree` masters carry a second term, and its cure is **WING-LOCAL** | `[LJ-1.155]` |
| a cure in SHARED machinery makes the ratio WORSE: AC gained 41.7 percent, the wing 7.9, and 1.56x went to 1.91x | `[LJ-1.147]`, `dev/ledger.toml:2712-2727` |
| the first term, cured: a folded type named out of a pattern split cost 2,526 ms, 65 percent of the master's worst definition | `[LJ-1.145]` |
| P-x and P-w are **REFUTED at this site, MEASURED**, and are not to be revisited | `[LJ-1.145]` |
| the instrument's band is **at least ±12.8 percent** | `[LJ-1.148]` |
| generic measured **8.4 times CHEAPER** than fixed at a neighbouring site | `[LJ-1.159]:263` |

**`[LJ-1.173]` landed 30 lines in these four masters today. Re-measure rather
than quote the table above.**

## THE INSTRUMENT, AND THIS IS THE PART TO GET RIGHT

**`[LJ-1.173]` spent most of a long leg discovering that its own +6 s was
noise.** Four fields measured cheaper than one, which is impossible if either
delta is real. It then found the band already printed by the repo's own tool:
`check-ratio.py` emits `noise band: at least +-12.8%, MEASURED [LJ-1.148]`.

**So: a delta inside the band is NOT a small measurement. It is no
measurement.** Do not extrapolate from one. **If your cure's effect is inside
the band, say exactly that and do not multiply it.**

**A cure worth funding here moves double figures of seconds**, because that is
the size of the wing's gap to the bar.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CURED.** You find the term, cure it, and the wing's aggregate falls by an
  amount OUTSIDE the band. Report the before and after with run counts. STOP.
- **FOUND BUT DEAR.** The term is real and its cure costs more than it saves, or
  needs a rewrite nobody funded. **Name it and price it. STOP.**
- **INSIDE THE BAND.** Your cure's effect cannot be separated from noise.
  **Say so plainly and report the distribution you measured.** That is a
  complete answer: it would mean the wing is intrinsically this expensive and
  the gap is structural.
- **SHARED, NOT LOCAL.** If the cure turns out to live upstream, **STOP before
  applying it** and say what it would do to the baseline. `[LJ-1.147]` made
  every master faster and the verdict worse, and that is DD4 working exactly as
  ruled with DD24 reading worse for it.

## WHAT YOU MUST NOT DO

- **DO NOT DELETE A LINE TO IMPROVE THE RATIO.** P-q measured 315 lines removed
  buying 11.8 s, and DD24's own row refuses the shrinking denominator.
- **Do not revisit P-x or P-w at this site.** Both REFUTED, MEASURED.
- **Do not touch `src/L/Coding/Graph.lagda.md`.** 21 consumers are green on its
  seal.
- **A sibling may be curing the `envK-*` fields in these same masters. Check
  `git status` before you edit and coordinate through me, never by editing
  around it.** If the tree is dirty in your target, **report that and stop
  rather than building on an uncommitted state you did not make.**
- **A probe goes in `agents/tasks/LJ-1-177/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Siblings
  are running. **Report the load beside every absolute figure, discard a
  warm-up, and take at least three kept runs for any figure a decision rests
  on.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「There is no second term」 is MEASURED
only if you profiled and say how deep you went.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.159]:263` measured generic at 8.4 times CHEAPER than fixed**, and `:50`
states it as DD4 costing nothing at that site and paying 8.4 times. **That is
the strongest DD4 result this project holds and it is one file away from your
target.** If your cure has a generic form, price both and say which you took.

**And say whether the cure is SHARED or WING-LOCAL for every candidate**, not
only the one you take. A SHARED cure speeds the AC side too, and `[LJ-1.147]`
measured that this makes the ratio WORSE, so the column decides whether a cure
helps at all.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-155/lj-1.155-report.md`**, read WHOLE. **It measured the
  second term and the WING-LOCAL verdict. It is the reason this task exists.**
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`** and its four probes, read
  WHOLE. **The method that worked: `--profile=internal`, then a verbatim
  transplant of the worst definition, then a bisection inside it.**
- `agents/tasks/LJ-1-147/lj-1.147-report.md`: the shared cure and the ratio
  finding.
- **`agents/tasks/LJ-1-159/lj-1.159-report.md`**, read WHOLE. **86.85 s cured
  for 13 lines, and the 8.4 factor.**
- `agents/tasks/LJ-1-173/lj-1.173-report.md` PARTS FIVE onward: today's 30
  lines, and the noise lesson.
- **`archive/dev/TASKS-archived.md`.** The retired route also had a condensation
  chapter. **Take SHAPE, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-155/lj-1.155-report.md` FIRST, then the three `*Agree`
masters.

## SCOPE (write)

`agents/tasks/LJ-1-177/` for probes. **A cure that measures well may land in the
`*Agree` masters, and ONLY after you have reported the measurement to me.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **P-t.** An average hides the term; a rate over thousands of lines is an
  average.
- **P-q.** Lines removed do not buy seconds.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-s, P-m, P-l, P-y, P-w, C-12, C-22, C-36, C-38 as extended, C-39, C-40.**
- **DD8, DD24, D-1, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. Verify a per-module figure
  with `.venv/bin/python scripts/check-ratio.py --module <file> --runs N`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the wing's aggregate before and after, with run counts, and say
whether the change is outside the band.** Then the term you found and where.
Then SHARED or WING-LOCAL for every candidate. Then the wing's gap to the bar,
re-measured. Then
the DD4 answer. **Mark every negative MEASURED or INFERRED.**
