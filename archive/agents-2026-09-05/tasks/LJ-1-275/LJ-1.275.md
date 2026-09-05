# LJ-1.275: the DD25 adversarial review of `[LJ-1.266]`'s heap wall

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row **and** the
only head the invariant permits. **I ran `scripts/dispatch_policy.py` before
writing this line**: `in-harness-subagent-mode` is IN FORCE, clock-selected,
PEAK now, Beijing window 09:00 to 12:00.

**The adversarial row under this mode is `pi`, and `pi` wrote the target.**
DD17's invariant binds over the table: **the critic is never the same head as
the author.** So the review takes `opus`.

## GOAL

**`[LJ-1.266]` returned the hardest negative of this phase and DD25 fires:
attack it before I act on it.**

**Its measurement, and the method is sound on its face:**

| arm | elapsed (mean, cold, n=3) | lines | marginal |
|---|---:|---:|---:|
| control, `Condensation.lagda.md` copied | **137.36 s** | 6,718 | — |
| fact, plus the twelve fields and the env closure | **147.64 s** | 7,007 | **0.036 s/line** |
| env, plus `envSetK`, `sucK` and the rest | **998.21 s** | 7,080 | **2.38 s/line** |
| full, plus the finite-supremum merge | **HEAP WALL at `-M8g`** | 7,523 | **does not typecheck** |

**The consequence, if it stands: the step 6 landing plan is dead as designed.**
The env supply is 226x the DD24 bar, and the full block does not typecheck at
the standard cap at all.

**Do not soften this. If it is right, say it is right.** A review that AGREES
buys confidence in a number the campaign is about to re-plan around.

## WHAT YOU ATTACK, and it is the NEGATIVE, not the task

DD25's four questions, in order.

**1. IS THE REFUSAL CORRECT ON ITS OWN NUMBERS?** **Re-derive the arithmetic
from `agents/tasks/LJ-1-266/runs/series.log`.** **Check the line counts with
`.venv/bin/python scripts/ledger.py`, not by eye.** **The report claims a
three-arm rotation C-E-F repeated three times; check the log shows that.**

**2. IS THE MEASUREMENT SOUND?** **The noise handling looks careful and I want
it checked anyway.** **The report says no reversed second series was needed
because the effect is outside the within-series band. `[LJ-1.215]`'s law asks
for the reversal. Is skipping it justified at a 6.3x separation, or is that the
reasoning that hides a systematic?** **The load spiked to 88 during the
session. Say whether any KEPT run sits inside that spike.**

**3. DID THE BRIEF CAUSE THE OUTCOME? I wrote it, and I now think it did.**
**My brief said: copy `Condensation.lagda.md` and add the content to the
copy.** **So every arm measures step 6 elaborating INSIDE a 6,718-line
chapter.** **I never asked what it costs anywhere else.**

**4. IS THERE A CURE THE RETURN MISSED?** **Two candidates, and both are mine
to have missed.**

## THE TWO CURES, and question 4 is why this review is worth its cost

**CURE A: THE CONTENT MAY NOT BELONG IN THAT CHAPTER AT ALL.**

**`[LJ-1.268]` measured that Route A-prime lands as FIVE NEW MASTERS and
extends nothing, precisely so no over-the-bar master gains a line.** **Nobody
asked the same question of step 6.** **The measurement priced the one shape my
brief named, and P-l inverted is the law: a COST measured at one site is a
hypothesis at another.**

**So: measure the env supply in a NEW master that imports `Condensation` rather
than living inside it.** **You may run Agda for this. The Agda slots are free
now: `[LJ-1.266]` finished and released its slot.**

**This is the decisive experiment of this review.** **If the env supply costs
2.38 s/line inside the chapter and far less in a fresh master, the landing plan
changes and nothing about step 6's mathematics changes.** **If it costs the
same, the cost is intrinsic and the project must re-plan.** **Either answer is
worth the dispatch; say which, MEASURED.**

**CURE B: THE OWNER'S RULED CURE HAS NOT BEEN APPLIED.**

**`[LJ-1.214]` measured that the telescope component at `Deserialization`
carries 7,925 of the chapter's 8,236 ms, 96 percent.** **The owner ruled option
C: move the numeral fact OUT of the telescope type.** **That cure is UNPRICED
and UNAPPLIED.**

**So `[LJ-1.266]` measured the UNCURED chapter.** **Say whether the env
supply's cost plausibly runs through that same component**, at `file:line`,
**and whether option C would move it.** **Mark this INFERRED unless you
measure it.** **Do not apply option C: it is a design change and DD23 and the
owner's ruling govern it. You may PRICE it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE MEASUREMENT HOLDS AND CURE A FAILS.** **The cost is intrinsic. Say so.
  Then the project re-plans step 6 and this review saved it from re-planning on
  a wrong number.** STOP.
- **CURE A WORKS.** **Give the new master's marginal rate beside the 2.38, and
  say what the landing order becomes.** **The most valuable outcome here.**
- **THE MEASUREMENT IS WRONG.** **Give the corrected figure and what caused the
  error.**
- **THE HEAP WALL IS THE FINDING, not the timing.** **`-M8g` is C-12's cap and
  it is NEVER raised.** **If the full block cannot typecheck in any layout, say
  so: that is a harder fact than any rate and it re-prices the phase.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Report a heap exhaustion as
  a wall and never raise the cap.**

## WHAT YOU MUST NOT DO

- **ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  **Report the load beside every absolute figure.** **Discard a warm-up.**
- **Do not edit any master.** **Work in `agents/tasks/LJ-1-275/` on copies.**
  **A probe under `src/` is forbidden (I-5).**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-266/`.** **It is a frozen record. Read it,
  copy from it, and write nothing into it.**
- **Do not apply option C.** **Price it only.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THAT BIND THIS REVIEW

**P-l, INVERTED, and it is the centre.** **A cure measured at one site is a
hypothesis at another. So is a COST.** **The 2.38 s/line is a measurement of
one layout, not of the content.**

**P-q. A line lever and a seconds lever are different levers.**

**P-t. An average hides the term.** **2.38 s/line over 362 lines is an average.
WHICH lines?** **Bisect if you can afford it: the report gives the arm's
content list and the per-file sources.**

**P-m. The check-cost rate is a content-class certificate, and instantiation is
the expensive class.**

**C-32. A cure invalidates every downstream measurement.** **Option C is an
unapplied cure sitting upstream of this whole measurement.**

**C-12. One Agda process per agent. The cap is never raised.**

**C-44. A brief's claim is unchecked until you check it.**

**C-46, written today.** A rule with no metric still has an axis.

**C-36. A failed substitution is not a proof of impossibility.**
**C-42, C-43, C-45. I-5. D-1, D-10, D-26, D-29, D-30. DD0, DD8, DD24.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.258]` measured that none of its fifteen fields is per-tower and that
all are stated over `(K, Ktr)`, so the seconds are paid ONCE for both towers.**
**Check that against the env supply too**: if the expensive block is
tower-neutral, its seconds are paid once; if it is per-tower, they are paid
twice and the figure above is HALF the real cost.

**NAME YOUR AXIS.** `[LJ-1.272]` measured 12 of 62 DD4 figures carrying no
axis, and C-46 is the law. **Say whether you mean Def-against-J, L-against-
ambient, or DD4's own AC-against-GCH.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-266/lj-1.266-report.md`, read WHOLE. The target.**
- **`agents/tasks/LJ-1-266/runs/series.log`**: the raw runs. **Read the log,
  never the report's summary of it.**
- **`agents/tasks/LJ-1-214/lj-1.214-report.md`**: the telescope component and
  the 96 percent. **Cure B rests on it.**
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:45-48`**: five new masters, no
  extension. **Cure A's precedent.**
- **`agents/tasks/LJ-1-218/lj-1.218-report.md`**: the per-master seconds table.
- **`agents/tasks/LJ-1-209/lj-1.209-report.md`**: the within-series paired
  design and the reversal.
- **`archive/dev/TASKS-archived.md`.** **The retired route also hit heap walls.
  Take SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost or heap. Say so in one
line.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-266/lj-1.266-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-275/` only. **No master, no ledger, no plan, no other
task directory.**

## RETURN

**Lead with ONE word on the measurement: HOLDS or WRONG.** Then the three
re-derived figures. Then CURE A's result, MEASURED, with the new master's
marginal rate beside the 2.38. Then CURE B's price, and say if it is INFERRED.
Then whether my brief caused the outcome. Then the DD4 answer with its axis.
**Mark every negative MEASURED or INFERRED.**
