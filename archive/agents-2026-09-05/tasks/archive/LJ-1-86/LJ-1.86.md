# LJ-1.86: is there a stage that contains AllCodes A?

tier: codex (default)

## GOAL

**One question.** `witK`'s repaired form needs `AllCodes A ∈ Lset lam`.
**Is there such a `lam`, provable in the delivered tree?**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`aed69e7`**. HEAD is green.

## WHAT IS SETTLED, machine-checked

- **`witK` as written is false** (`[LJ-1.84]`, `src/ProbeLJ184A.agda`): a
  junk member with the stage bound in its ARITY slot keeps a set closed and
  shaped while lifting its rank past the bound.
- **The premise `w ⊆ AllCodes A` kills that refutation** (`[LJ-1.85]`, red
  control `src/ProbeLJ185C.agda`), because a formula key always carries a
  numeral in the arity slot (`src/L/Coding/InL.lagda.md:252-253`).
- **A consumer supplies the premise**: the subformula closure that
  `hasWitnessAt` produces lies in `AllCodes A` member by member
  (`src/ProbeLJ185B.agda:58-68`, `src/L/Coding/CodeSet.lagda.md:365-373`).
- **The remaining gap is the stage condition**: `AllCodes A ∈ Lset lam`.
  `[LJ-1.85]` marked its absence INFERRED, not measured.

## THE QUESTION

**Is `AllCodes A ∈ Lset lam` provable for some `lam`, from what the tree
delivers?**

Two halves, and both matter:

1. **Is `AllCodes A` constructible at all?** It is defined by a formula over
   the carrier (`IsKeyOverAny`, `src/L/Coding/CodeSet.lagda.md:434-441`). If
   the tree's `Lset` construction gives definable subsets of a stage, the set
   should appear at a later stage. **Check what the delivered construction
   actually gives, at `file:line`.**
2. **Can the condensation proof CHOOSE that `lam`?** `[LJ-1.81]` established
   that `Adeq`'s bound `K'` is existentially quantified, so the proof picks
   it. **Say whether the same freedom reaches the stage in `witK`'s frame**,
   or whether `lam` is fixed by something upstream.

**If both halves hold, the gap closes and you say how.** If either fails,
that is the finding.

## WHAT I EXPECT, and it is INFERRED

`AllCodes A` is a set, so a large enough stage contains it, and the proof
chooses its own bound. **That reasoning is mine and it has been wrong three
times this phase**: `tagEq`, the `KFacts` closure family, and `witK` all
looked obviously fine and were false. **Check it; do not confirm it.**

## THE ABORT CRITERION, fixed in advance per D-1

- **A `lam` exists and the proof can choose it**: report the term at
  `file:line`, with what it rests on, and STOP. Do not carry the chain
  further.
- **`AllCodes A` is not constructible, or `lam` is fixed upstream**: STOP,
  write the term you could not write, and say where the obligation moves to.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ186*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none of the earlier ones killed. Each carried
`-M8g`: 48 GB of worst case on a 64 GB machine at load 19. **The owner caught
it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any statement.**
- **Do not assume a stage exists because a set is small.** The tree's `Lset`
  is a constructible hierarchy, not a cumulative one: **membership needs
  definability, not just rank.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the stage argument is generic**, so the J tower gets its own
bound the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.85-report.md`**, read WHOLE, and `src/ProbeLJ185B.agda`,
  `src/ProbeLJ185C.agda`. The premise, the red control and the supply point.
- `_build/lj-1.84-report.md` and `src/ProbeLJ184A.agda`, the refutation.
- `_build/lj-1.81-report.md`, why the bound is chosen by the proof.
- `src/L/Constructible.lagda.md` and `src/L/Ordinal/Stages.lagda.md`, the
  delivered stage machinery. **Read-only.**
- `src/L/Coding/CodeSet.lagda.md`, `AllCodes`. **Read-only.**
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin's proof chooses a bound and this is that step.**
`dev/literature/devlin-II5.md` Step C and
`_build/literature/dev2.txt:1372-1385`. **Say in two lines how Devlin gets a
stage large enough**, and whether the tree has the analogue. Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Coding/CodeSet.lagda.md:434-441` FIRST, then
`src/L/Constructible.lagda.md`'s stage construction, then
`_build/lj-1.85-report.md` section 1.

## SCOPE (write)

`src/ProbeLJ186*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.86-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.86-report.md` incrementally, skeleton first.

**Lead with whether a stage containing `AllCodes A` exists and is choosable**,
at `file:line`. Then, if not, the term you could not write and where the
obligation moves. **Mark every negative MEASURED or INFERRED.** Then how
Devlin gets his bound. Then the DD4 answer. Confirm every master is green or
untouched.
