# LJ-1.276: LAND step 6 as a new master, because the wall was the layout

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK, Beijing
window 12:00 to 14:00.

## GOAL

**Land step 6's whole block as a NEW MASTER under `src/`.** **This is a
LANDING, not a probe. The deliverable is a green master in `src/`.**

**The risk is already measured out.** `[LJ-1.275]` typechecked the identical
805-line block in a new master, three times, at the standard `-M8g` cap:

| | inside `L.Condensation` | in a new master |
|---|---:|---:|
| the full 805-line block | **HEAP WALL** | **GREEN, exit 0, 465.59 s, n=3** |
| the 362-line env supply | 2.378 s/line | **1.267 s/line** |

**`agents/tasks/LJ-1-275/runs/series.log:4`, `:6` and `:11`** hold the three
runs: 465.63, 463.46 and 467.68 seconds, spread 0.9 percent.

**So the question is not WHETHER it typechecks. It is what the delivered master
should be called, what it should export, and what its consumers need.**

## THE SOURCE, and it is a proven probe rather than a sketch

**`agents/tasks/LJ-1-275/SupplyFullNew.lagda.md` is the green arm.** It is a
new module that IMPORTS `L.Condensation` and carries the whole block.

**Read it whole before you write anything.** **Take its content, not its
name**: it is called `LJ-1-275.SupplyFullNew` because it was a probe.

## THE PATH IS FIXED AND IT IS MINE, not yours

**`src/L/Coding/EnvSupply.lagda.md`, module `L.Coding.EnvSupply`.**

**I choose it rather than delegating it, for two reasons.** The reading order in
`src/Everything.lagda.md` is mine to wire, so the name is mine to settle. **And
a sibling is landing `src/L/Coding/Injection.lagda.md` in the same directory
right now, so an agent-chosen name is a collision waiting to happen.**

**It sits beside `Environment.lagda.md` and `EnvSet.lagda.md`, which it is NOT:
say in your report what distinguishes the three**, because a reader who
confuses them will import the wrong one.

## WHAT YOU DECIDE, and say why in the report

**1. WHAT IT EXPORTS.** **P-k: a read lemma is stated where its consumers use
it.** **Name the consumers.** **Step 6 exists to supply `[LJ-1.7]`'s
`module Whole`; `agents/tasks/LJ-1-267/lj-1.267-report.md` maps its seven
parameters.**

**2. WHAT `src/Everything.lagda.md` NEEDS.** **NEVER touch that file. I wire
it.** **Name the exact line I must add, and where in the reading order.**

## THE MEASUREMENT YOU OWE, and it is short because the hard one is done

**Report the delivered master's OWN cold elapsed time and its line count, and
its rate against the 0.010514 bar.** **One cold run is enough**: the n=3 figure
exists at `[LJ-1.275]`. **If your figure differs from 465.59 s by more than 10
percent, say so and stop**, because something differs from the arm that was
measured.

**And verify `L.Condensation` did NOT change.** **Re-run it and report its
elapsed time.** **`[LJ-1.275]`'s whole claim is that the chapter gains zero
lines and zero seconds. Prove it at the landing.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS GREEN.** Report the name, the exports, the `Everything` line, the
  two timings. STOP.
- **IT LANDS BUT `L.Condensation` MOVED.** **That is a finding.** Report both
  timings and stop before wiring.
- **IT DOES NOT TYPECHECK AS A MASTER.** **`[LJ-1.275]` proved the content
  compiles under `--cubical --safe --guardedness` in a new module. If a MASTER
  refuses what a probe accepted, name the difference** (C-36). **A master is
  `.lagda.md` with an OPTIONS header inside a fence; a probe is `.agda`. That
  difference is the first thing to check.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Report a heap exhaustion as
  a wall. NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **NEVER touch `src/Everything.lagda.md`.** I wire it after auditing.
- **Do not edit `src/L/Condensation.lagda.md` or any other existing master.**
  **The whole point of this landing is that no existing master gains a line.**
  **If you believe an existing master must change, STOP and say why.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-266/` or `LJ-1-275/`.** **Both are frozen
  records. Read them and copy from them; write nothing into them.**
- **Do not touch `agents/tasks/LJ-1-277/`.** **A SIBLING IS LIVE THERE, landing
  A2 into `src/L/Coding/Injection.lagda.md`.** **Your write territory and its
  write territory must not overlap.** **Yours is
  `src/L/Coding/EnvSupply.lagda.md` and nothing else under `src/`.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**C-49, written from this exact block today.** **A heap wall and a rate can be
properties of the LAYOUT rather than the content.** **This landing IS that
law's payoff. Do not put the content anywhere near `L.Condensation`.**

**P-t. An average hides the term.** **`[LJ-1.275]` measured that 443 of the 805
lines check at 1.09x the bar and the 362-line env block carries 98.9 percent of
the seconds.** **If you must split the master, that line is where it splits.**

**C-40. A new master has consumers the moment it exists.**

**`exit 0` IS NOT A SUPPLY** (C-45). **A green master is not a supplied
hypothesis. Say which of `[LJ-1.7]`'s parameters this landing SUPPLIES and
which it only BUILDS.**

**C-32. A cure invalidates every downstream measurement.**

**C-44. A brief's claim is unchecked until you check it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.275]` measured this block NEUTRAL on DD4's own AC-against-GCH axis, so
its seconds are paid ONCE.** **`[LJ-1.258]` measured that its fifteen fields
are all stated over `(K, Ktr)` and none is per-tower.**

**So write the master GENERIC in the same way, and say in your report what
would have to change for the J tower to re-instantiate it.** **NAME YOUR
AXIS** (C-46): this phase mixed Def-against-J with L-against-ambient, and DD4's
own axis is neither.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-275/SupplyFullNew.lagda.md`, read WHOLE. The green
  arm and the content you are landing.**
- **`agents/tasks/LJ-1-275/lj-1.275-report.md`**: why it is green here and not
  there, and the per-block split.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`**: **how a landing was done in
  this campaign, including the re-run that PROVED it was a landing and not a
  copy.** **Do the same.**
- `agents/tasks/LJ-1-267/lj-1.267-report.md`: `[LJ-1.7]`'s seven parameters.
- `agents/tasks/LJ-1-254/`, `LJ-1-257/`, `LJ-1-258/`, `LJ-1-259/`, `LJ-1-261/`:
  the probes the block was assembled from.
- **`archive/dev/TASKS-archived.md`.** **The retired route landed masters too.
  Take SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
row this master serves.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-275/SupplyFullNew.lagda.md` FIRST, whole.

## SCOPE (write)

`src/L/Coding/EnvSupply.lagda.md`, new, and `agents/tasks/LJ-1-276/` for your
report and any working file. **No existing master. Never
`src/Everything.lagda.md`.** **Do not create any other file under `src/`.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l.** A statement may be ABOUT a concrete stage without dragging that
  stage's presentation into its type.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35.** Union representations are meta-poisoned.
- **R-38.** A consumer's alias of a transparent imported operation is a birth
  site.
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly.
- **I-5.** Inner-world truncation branches carry written types.
- **C-12.** Agda runs under a hard heap cap.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **C-32, C-36, C-40, C-44, C-45, C-49. D-1, D-26. DD0, DD8, DD23, DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `.venv/bin/python scripts/lint-agda.py --check` on what you write.
- **`lint-agda.py` binds a MASTER**: the OPTIONS header, the using-list
  discipline, import necessity and the forbidden constructs. **The probe you
  copy from was exempt; your master is not.** **Expect to trim the using
  lists.**
- **DD23 freezes mathematical prose.** **Write code and its own comments only.**
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the delivered line count and the cold elapsed seconds.** Then `L.Condensation`'s re-run time, to show it did not move. Then
the exact `src/Everything.lagda.md` line I must add. Then what the master
exports and who consumes it. Then which of `[LJ-1.7]`'s parameters this
SUPPLIES rather than BUILDS. Then the DD4 answer with its axis. **Mark every
negative MEASURED or INFERRED.**
