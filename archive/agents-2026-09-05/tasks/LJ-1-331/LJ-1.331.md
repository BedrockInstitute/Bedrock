# LJ-1.331: the `RowTies` probe, funded by its own gate

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE GATE FIRED, and this task is what it funds

**`[LJ-1.320]`'s ruling set the gate BEFORE the measurement (D-1):**

> **Sum the charges over the `KFacts` consumers and the thirty `Agree` modules.
> At 15 s or more, fund a `RowTies` PROBE, not the build. Under 15 s, REFUSE
> the compression for seconds.**

**`[LJ-1.322]` measured it: 36.60 s, and 26.6 percent of a 137,453 ms Total.**
**The six `KFacts` consumers alone reach 15.54 s and pass on their own.**
**BOTH figures are LOWER BOUNDS**, because the profiler truncates at 10 ms
(MEASURED across ten of this project's profiles).

**So the probe is funded, and the BUILD is not. Do not build `RowTies`.**

## AND EVERY OTHER SECONDS ROUTE IS NOW DEAD

**`[LJ-1.322]` returned ALL THREE MISS on the ranked mechanisms:**

- **Rank 1 is REFUTED WITH THE SIGN BACKWARDS.** `--no-syntactic-equality` made
  the file **at least 13.1 times SLOWER**: 1,840.76 s unfinished against a
  same-session control of 140.57 s. **The shortcut is CARRYING this file, not
  costing it.**
- **Rank 2 misses:** 16.25 percent against a 30 percent threshold.
- **Rank 3 is UNMEASURABLE:** exit 42, a type error inside the very region it
  was meant to help.

**And the cost is NOT concentrated: the largest single definition is 2.6
percent**, the opposite of the 99.2-percent site this project cured before.
**So a one-definition cure has no target here, MEASURED.**

**That leaves the `Agree` family's 26.6 percent as the only seconds line with a
funded gate behind it.**

## THE QUESTION

**Would replacing the thirty `Agree` modules' repeated telescopes with a
`RowTies` record cut the SECONDS, and by how much?**

**`[LJ-1.307]` measured the lines side: about 990 lines of repeated telescope,
and a `KFacts`-style record states thirty-one ties in 35 lines where a telescope
spells sixty.** **Nobody has measured the seconds side, and its own 15-to-20 s
band is marked INFERRED by its author.**

## THE WARNING THE ARCHIVE CARRIES, and it is against this task

**A telescope lift was already tried on a `Condensation` and made it WORSE:
204.7 s to 308.8 s**, `dev/LESSONS.md` P-l's own table, `[T102]` argued from
resemblance and `[T106]` refuted it.

**That was the retired route's 885-line module, so no figure transfers. The
argument's SHAPE transfers exactly**, and it is the shape of the estimate you
are testing. **P-l is the law: an expected figure anchored on a comparable
elsewhere is a hypothesis, not a price.**

**So build the miniature and measure. Do not argue from resemblance in either
direction.**

## WHAT TO BUILD

**The smallest decisive miniature: take ONE `Agree` module, in a COPY, and
re-spell its telescope as a record. Measure both.**

**Pick the module by the profile, not by convenience.** `[LJ-1.322]`'s A1 run is
at `agents/tasks/LJ-1-322/runs/a1.out` with 127 charged rows for the family.
**Read the RAW file** (C-53) **and take a module in the charged middle: not the
single most expensive, which may be atypical, and not a cheap one, which
measures nothing.** **Say which you picked and why.**

**Then measure:**

1. **The copy, verbatim, as a baseline.** Same-session, same content.
2. **The copy with the record.** Same session, immediately after.
3. **The delta, and whether it is bigger than the session's own noise.**
   `[LJ-1.322]` measured four flagless checks of one content spreading only
   **1.35 percent**, so that is your noise floor.

**If the delta is inside the noise, say so. That is a REFUTATION and it closes
the last seconds line.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE RECORD CUTS SECONDS BEYOND THE NOISE.** Report the delta and
  extrapolate to thirty modules **with the basis named** (DD8). **Then the
  build is priced and a landing brief can be written.** STOP.
- **THE RECORD CHANGES NOTHING.** **REFUTED, and the seconds line closes
  entirely.** Say it plainly.
- **THE RECORD MAKES IT WORSE.** **Then the archive's warning repeats at a new
  site and that is a LESSON with two measurements.** Say so.
- **THE MODULE WILL NOT COMPILE AS A COPY.** Name what it needs and stop; a
  copy that will not stand alone measures nothing.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## THE MEASUREMENT DISCIPLINE, and this chain wrote it

**C-53:** read from the RAW `.out`, never a report's excerpt, and **state the
Total, the `Miscellaneous` share and a same-run charged control with every
definitions figure.** **`[LJ-1.322]` measured `Miscellaneous` at 58.3 percent on
this very file.**

**C-50:** profile before you cure. **C-52:** name the discriminating property.

**THE MACHINE MAY NOT BE QUIET.** `[LJ-1.322]` found background processes at 80
to 90 percent and marked every figure INDICATIVE. **Check `uptime` and the
process list, mark accordingly, and rely on the SAME-SESSION delta rather than
on any absolute figure.**

## WHAT YOU MUST NOT DO

- **DO NOT BUILD `RowTies` ITSELF.** The gate funds a PROBE. **One module, in a
  copy.**
- **LAND NOTHING.** Write and run only in `agents/tasks/LJ-1-331/`. **`src/` is
  forbidden** (I-5).
- **DO NOT STOP OR DISTURB `[LJ-1.306]`'s port.** The ruling says so explicitly.
- **Do not edit another task directory.** You may READ
  `agents/tasks/LJ-1-322/runs/`, `agents/tasks/LJ-1-307/` and
  `agents/tasks/LJ-1-306/`; you may not change them.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling is live.** Take ONE slot and report the load beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RESTORE the interface cache with one flagless check when you finish**, and
  **leave no undeclared file in `_build/`**.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-331/lj-1.331-report.md` in your FIRST five
  minutes** and write each figure in as it lands (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line` or a run's own output path. Write ASD-STE100. Mark
  every negative **MEASURED** or **INFERRED**, in those words.

## THE PREMISES OF MINE MOST LIKELY TO BE WRONG

**`[LJ-1.322]` found TWO false premises in my last brief and both mattered:**

1. **I said an existing `Condensation` profile could save a run.** **REFUTED:
   across all 200 `.out` files in `agents/tasks/`, not one profiles that file.**
2. **I passed on the ruling's fallback naming `satGraphB`, `twelveB` and
   `closedBS` as the cost carriers.** **REFUTED: all five matching rows charge
   258 ms of 137,453, which is 0.19 percent.** **A cure brief against those
   names would have targeted one five-hundredth of the run.**

**Assume this brief carries another. C-44 binds it as hard as any agent's
claim.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**`[LJ-1.322]` MEASURED and corrected the wording:** `src/L/Condensation.lagda.md`
is in **NEITHER trophy closure**, but it IS a declared `gch_wing` member
(`dev/ledger.toml:3106`), **so a cure serves the GCH wing's SECONDS ACCOUNT and
not the trophy statement**, and P-y runs favorably: every second saved improves
the DD24 ratio.

**AND THERE IS A LINES QUESTION UNDER YOURS.** `[LJ-1.307]` asked whether the
thirty modules are one thing or thirty and answered PARTLY. **If the record
cuts seconds, it probably cuts lines too, and DD13 then wants both figures
together.** **Report the lines delta of your one module beside the seconds
delta**; it costs one `wc`.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-322/lj-1.322-report.md`, read WHOLE, and its raw
  `runs/a1.out`.** It funds you and it is the only profile of this file that
  has ever existed.
- **`agents/tasks/LJ-1-307/lj-1.307-report.md`**, the lines side and the
  `KFacts` pattern it proposes.
- **`agents/tasks/LJ-1-306/lj-1.306-report.md`**, the generic port, which must
  not be disturbed.
- **`dev/LESSONS.md` P-l's table**, the telescope lift that made a
  `Condensation` worse. **Read the FULL entry.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`agents/tasks/LJ-1-317/lj-1.317-report.md`** carries the proof-assistant
corpus, including what is documented about record eta and large interfaces.
**Say in one line whether the literature predicts a record helps or hurts
here**, and note that its own rank 3 arm was UNMEASURABLE. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-322/runs/a1.out` FIRST, raw, to pick your module.

## SCOPE (write)

`agents/tasks/LJ-1-331/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, DD8, P-l, C-44, C-50, C-52, C-53.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-49, C-51, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-36, C-39, C-40, C-42, C-45.** I-5. **D-10, D-26.**
- **DD0, DD4, DD13, DD18, DD24.**

## RETURN

**Lead with ONE line: does the record cut seconds beyond the noise, and by how
much.** Then which module you picked and why, from the raw profile. Then the
two same-session figures and the session's noise floor. Then the extrapolation
to thirty, with its basis. Then the lines delta beside it. Then whether the
machine was quiet. **Mark every negative MEASURED or INFERRED.**
