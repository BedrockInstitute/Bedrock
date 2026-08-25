# The context budget, measured, and the splitting rule it forces

**Owner's instruction, 2026-08-25: split a task so an agent finishes inside
about 130k of context.** This file measures where the context actually goes,
sets a budget I can compute BEFORE I dispatch, and gives the clause text the
owner needs if the rule is to bind a later holder of this slot.

**I cannot land the clause myself.** `dev/pod/instructions/` is a GUARDED DIR
(`scripts/pod/check-spec-surface.py`, `GUARDED_DIRS`), so a change there needs
a dated `Spec-surface-approved:` trailer, and my write scope is
`agents/tasks/POD-MATH/` in any case. Section 5 holds the text, ready to paste.
**The rule binds ME from now, without any of that.**

**The program has NO token accounting.** `grep -rn 'tokens' scripts/pod/*.py`
hits only `retrieve.py`'s text-scoring tokens and unrelated comments. So this
budget is agent discipline, computed by hand, and its enforcement is that I
write the arithmetic into the brief where the coder can refute it.

All sizes below are bytes on disk, converted at **4 bytes per token**. That
divisor is an approximation and every figure that uses it is marked `~`.

## 1. WHERE THE CONTEXT GOES

**The brief is not the problem.** Measured over the 245 post-cutover briefs and
the 238 reports:

| item | median | p90 | max |
|---|---|---|---|
| brief | 14,117 B (~3.5k tok) | 16,590 B | 22,498 B (~5.6k) |
| report the agent writes | 16,948 B (~4.2k tok) | 25,038 B | 36,169 B (~9k) |
| probe the agent writes | 5,590 B (~1.4k tok) | 17,826 B | 51,155 B |
| `runs/` output per task | 16,190 B (~4k tok) | 49,249 B | 1,830,719 B |

The fixed preamble is `dev/pod/instructions/coder.md` 6,313 B + `AGENTS.md`
4,350 B + `dev/pod/screen.toml` 3,134 B + `dev/pod/direction.md` 2,775 B =
**16,572 B, ~4.1k tokens**. With a median brief the floor is **~7.7k tokens**.

**The context goes into what the brief POINTS AT.**

| target | size | ~tokens if read whole |
|---|---|---|
| `src/L/Condensation.lagda.md` | 405,464 B, 7,435 lines | **~101k** |
| `src/L/Coding/Model.lagda.md` | 120,437 B | ~30k |
| `src/Everything.lagda.md` | 113,743 B | ~28k |
| `src/L/BoundedSubset.lagda.md` | 78,754 B | ~20k |
| one predecessor report | 16,948 B median | ~4.2k each |

**One bare reference to `Condensation.lagda.md` spends 78 percent of a 130k
budget in a single read.**

## 2. THE BUDGET, COMPUTED OVER EVERY POST-CUTOVER BRIEF

Definition. **NAMED READING** = the fixed preamble + the brief + every `src/`
master the brief references with NO `:line` anchor and over 40 kB (deduplicated,
because the agent reads it once) + every predecessor task's report and probe.
It excludes the agent's own probe, runs and report.

| statistic | value |
|---|---|
| median | ~36k tokens |
| p75 | ~56k |
| p90 | ~68k |
| max | ~142k |
| briefs over 50k | 78 of 245 |
| briefs over 60k | 42 of 245 |
| briefs over 80k | 10 of 245 |
| **briefs over 130k, before the agent writes one line** | **4 of 245** |

The four: `[LJ-1.615]` 142k, `[LJ-1.491]` 134k, `[LJ-1.522]` 131k,
`[LJ-1.525]` 130k. **All four are one bare `src/L/Condensation.lagda.md`.**
`[LJ-1.615]` is SHELVED.

**Of the 42 briefs over 60k, the dominant driver is the PREDECESSOR CHAIN in 34
and a bare `src/` master in 8.** The predecessor chain is the common defect and
the bare master is the spectacular one.

Worst predecessor chains: `[LJ-1.548]` 86k over 8 tasks, `[LJ-1.574]` 81k over
7, `[LJ-1.591]` 79k over 7. `[LJ-1.548]` is also the task of backlog item 27,
which stopped on a sibling it could not see.

## 3. THE SPLIT OF 130k I WILL WORK TO

| bucket | reserve | basis |
|---|---|---|
| preamble + brief | 10k | measured floor 7.7k, worst brief 9.8k |
| **named reading** | **60k ceiling** | what I control, and what I write in the brief |
| the agent's own probe, runs, edits and report | 50k | p90 probe 17.8 kB re-read across edit rounds, p90 runs 49.2 kB, p90 report 25 kB |
| margin | 10k | |

**60k of named reading is the number I enforce.** Under it, 203 of the 245
briefs already written would have passed unchanged and 42 would have been split.

## 4. THE RULES, EACH WITH THE MEASUREMENT THAT FORCES IT

**B1. NEVER reference a `src/` master over 40 kB without a line anchor.** Give
`file:start-end` and the term name. Today 275 of 2,098 `src/` references in
briefs are bare, and 37 briefs carry at least one bare reference to a master
over 40 kB. This rule alone moves the four 130k briefs to under 45k.

**B2. AT MOST THREE predecessor tasks per brief, each cited at a report SECTION
or line range, never at the directory.** Today the median is 4 and the max is 8.
A predecessor named as a directory is an invitation to read the whole task home.

**B3. Write the budget in the brief, with its arithmetic.**

    context_budget: ~42k named reading
      preamble+brief 8k | src/L/StageCardinal.lagda.md:260-300 0.4k
      | LJ-1.613 report §THE TWO 3k | LJ-1.625 report §THE FLOORS 2k

The coder can then refute it, and the next mathematician can see what I assumed.
**A budget over 60k means the obligation is too big. Split it, do not shrink the
citation list.**

**B4. A BISECTION IS ITS OWN TASK.** 33 post-cutover tasks hold more than 30
files under `runs/`; `[LJ-1.565]` holds 123 and `[LJ-1.545]` 118.
`[LJ-1.541]` tried the proof AND a seven-arm bisection in one dispatch, spent
20,313 s, and delivered neither. Task A attempts the term under a stated
wall-clock ceiling. Task B bisects, ONLY if A walls, and its obligation is the
bisection table.

**B5. One obligation per brief is already AD12. B3 is how I test that I obeyed
it.** An obligation whose named reading will not fit in 60k is more than one
obligation, whatever the `obligations` line says.

**B6. Do not pay for a predecessor's whole report to carry ONE type.** Quote the
type in the brief, cite it at `lj-1.NNN-report.md:LL`, and say "you do not need
to open the rest". The standing clause already forces the citation to be the
REPORT and not the brief; this makes it cheap as well as correct.

## 5. THE CLAUSE, READY FOR `dev/pod/instructions/mathematician.md`

Proposed text, if the owner wants this to bind later holders of the slot. It is
guarded, so it needs the owner's word and a `Spec-surface-approved:` trailer.

> **EVERY BRIEF CARRIES A `context_budget:` LINE AND ITS ARITHMETIC, AND THE
> CEILING IS 60k TOKENS OF NAMED READING.** Owner's ruling, 2026-08-25, on a
> measured distribution. Named reading is the preamble, the brief, every `src/`
> master referenced without a line anchor, and every predecessor report or probe
> the brief names. MEASURED over the 245 briefs of the LJ-1 campaign: median 36k,
> p90 68k, and FOUR briefs above 130k before the agent wrote a line, each of them
> one bare reference to `src/L/Condensation.lagda.md` (405,464 B, ~101k tokens).
> **Never reference a `src/` master over 40 kB without `:start-end`. Name at most
> THREE predecessor tasks, each at a report section or line range, never at the
> directory.** A budget over the ceiling means the obligation is more than one
> obligation: split it, and never shrink the citation list to fit.

## 6. WHAT THIS DOES NOT FIX

A task can still blow its context on its OWN work: a probe that grows past
17 kB and is re-read on every edit, or a run that prints a 1.8 MB log
(`[LJ-1.466]`). `dev/LESSONS.md` C-19 already says to read the exit code and
not the log tail. **I will state a run-output rule in the brief when the
obligation is bisection-shaped**, and it is the coder's clause, not mine, to
carry it generally. That is a question for the maintainer's backlog, not for me.
