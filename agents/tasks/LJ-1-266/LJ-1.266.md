# LJ-1.266: what does step 6 cost in SECONDS inside Condensation?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**Every step 6 figure in this phase is LINES. Not one is the SECONDS those
lines cost inside the master they land in.** **DD24 is a seconds rule.**

**And the master they land in is the expensive one.** `[LJ-1.218]` measured:

| | seconds | rate |
|---|---:|---:|
| `src/L/Condensation.lagda.md` alone | **132.28** | **0.0198**, 1.9x the bar |
| the four Condensation masters | 151.90 | 0.0195 |
| **the other eight wing masters together** | 33.5 | **0.0081, UNDER the bar** |

**Eight of twelve already pass. The wing's cost problem is ONE CHAPTER, and
step 6's roughly 400 lines land in it.**

**Measure the marginal seconds BEFORE the landing, not after.**

## THE METHOD, and it is a paired design

**Copy `src/L/Condensation.lagda.md` into your task directory.** **Add the
green step 6 content to the copy.** **Cold-run the copy and the unmodified
control under the SAME bound, alternating, and report both elapsed times
before you interpret either** (`[LJ-1.215]`'s law).

**The probes that hold the green content:**

| file | what it holds |
|---|---|
| `agents/tasks/LJ-1-254/ProbeLJ1254.agda` | `envSetK`, `sucK`, `union∈Lset-suc` |
| `agents/tasks/LJ-1-255/ProbeLJ1255.agda` | the five `envK-*`, collapsed at `[LJ-1.257]` to 67 lines |
| `agents/tasks/LJ-1-257/ProbeLJ1257.agda` | the four `envInK-*` and `someEnv` |
| `agents/tasks/LJ-1-258/ProbeLJ1258.agda` | twelve of the fifteen, four groups |
| `agents/tasks/LJ-1-259/ProbeLJ1259.agda` | `envConsK` and the three `consK-*` |
| `agents/tasks/LJ-1-261/ProbeLJ1261Merge.agda` | the finite-supremum merge |

**Use the COLLAPSED form of the five `envK-*`**, not `[LJ-1.255]`'s five
copies: `[LJ-1.257]` measured 67 lines against 85 and `[LJ-1.256]` measured
that the copies are avoidable. **A seconds figure taken on the unfactored form
would price something nobody will land.**

## THE ONE NUMBER THIS TASK OWES

**The MARGINAL seconds per line of the added content, and the resulting rate
for `Condensation.lagda.md` as a whole.**

**Then say which of two worlds we are in:**

- **BELOW 0.0198.** The added lines IMPROVE the chapter's rate, and landing
  them moves the wing toward the bar rather than away.
- **ABOVE 0.0198.** The 60.0 s gap grows on the day of the landing, and by how
  much.

**Nobody knows which, and the two call for opposite plans.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH RUN AND THE MARGINAL RATE IS MEASURED.** Report the control's elapsed
  time FIRST, then the treated copy's, then the marginal rate and the new
  whole-file rate. STOP.
- **THE COPY WILL NOT TYPECHECK.** **That is a finding, not a failure.** **Name
  the term** (C-36). **The probes are green in isolation; a probe that will not
  compose into its master is exactly what a landing gate is for.**
- **THE DIFFERENCE SITS INSIDE THE NOISE.** **`check-ratio.py`'s ±12.8 percent
  is a ONE-MODULE BETWEEN-SERIES figure by its own words at `:72-76`;
  within-series spread is 0.5 to 4.0 percent.** **Use a within-series paired
  design and REVERSE THE ORDER in a second series to cancel drift**, as
  `[LJ-1.209]` did. **If it still sits inside the band, say so: that is a real
  answer and it means the landing is free.**
- **A WALL.** **`Condensation.lagda.md` is 132 s cold on its own. Budget for
  it.** **A single `agda` invocation past 30 MINUTES is a wall**: interrupt,
  report the ELAPSED SECONDS, bisect.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** **COPY `Condensation.lagda.md` into
  `agents/tasks/LJ-1-266/` and edit the copy.** **Nothing lands in `src/`, and
  a probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Coding/Key.lagda.md`.** **`[LJ-1.263]` is editing it
  right now.** **If your copy needs its three L-rows, take them from
  `agents/tasks/LJ-1-254/`, `LJ-1-259/` and `LJ-1-261/` instead.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not re-measure the wing aggregate.** `[LJ-1.218]` did, and a
  between-series band cannot resolve this.
- **A probe goes in `agents/tasks/LJ-1-266/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, take at least
  three kept runs per arm.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## WHY THE ANSWER CHANGES THE PLAN

**DD24 permits intermediate debt because only the whole wing at the end is
judged** (owner, 2026-08-14). **So the order of work depends on one thing: does
landing make the gap bigger or smaller?**

**C-32 says every cure invalidates the measurements downstream of it, so
compressing a moving tree is wasted work.** **That argues for landing first.**
**But if step 6's lines land at 1.9x the bar or worse, the debt compounds and
the argument reverses.** **You are the measurement that settles it.**

## EIGHT RULES THIS CHAIN EARNED

**A LINE LEVER AND A SECONDS LEVER ARE DIFFERENT LEVERS** (P-q). **Every step 6
figure so far is a line figure.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44).

**`exit 0` IS NOT A SUPPLY** (C-45). **Here: a green probe is not a green
master.**

**A CURE MEASURED AT ONE SITE IS A HYPOTHESIS AT ANOTHER** (P-l).

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.258]` measured that none of its fifteen fields is per-tower and that
all are stated over `(K, Ktr)`.** **So the seconds you measure are paid ONCE
for both towers, not twice.** **Say whether that holds for the whole added
block**, and **NAME YOUR AXIS**: `[LJ-1.262]` measured that this phase mixes
Devlin's Def-against-J with the port's L-against-ambient, and no figure says
which.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-218/lj-1.218-report.md`**, read WHOLE: the per-master
  distribution and the 82-percent-on-65-percent finding.
- **`agents/tasks/LJ-1-209/lj-1.209-report.md`**: the within-series paired
  design that resolved an 83 ms effect, which is your method.
- **`agents/tasks/LJ-1-214/lj-1.214-report.md`**: where the chapter's 8.2 s
  lives, so you do not confuse your delta with it.
- `agents/tasks/LJ-1-254/`, `LJ-1-255/`, `LJ-1-257/`, `LJ-1-258/`, `LJ-1-259/`,
  `LJ-1-261/`: the green content.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-218/lj-1.218-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-266/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **P-q.** A line lever and a seconds lever are different levers.
- **P-t.** An average hides the term.
- **P-m.** The check-cost rate is a content-class certificate, and
  instantiation is the expensive class.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **P-s, P-i, P-k, P-y, R-40, R-34. C-12, C-22, C-36, C-39, C-40, C-42, C-44,
  C-45. I-5. DD0, DD8, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the control's elapsed seconds, THEN the treated copy's, THEN the
marginal rate per line.** Then the new whole-file rate against 0.0198 and
against the 0.010514 bar. Then which of the two worlds we are in. Then the
noise handling and the reversed second series. Then the DD4 answer with its
axis. **Mark every negative MEASURED or INFERRED.**
