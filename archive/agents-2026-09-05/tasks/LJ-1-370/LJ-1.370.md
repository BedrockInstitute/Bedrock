# LJ-1.370: retire `meet-suc`, on `[LJ-1.364]`'s fable ruling

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **BUILD.**

## THE RULING THAT FUNDS THIS

**`[LJ-1.364]` ruled RETIRE**, at maximum effort, on the owner's express
authorisation. **It priced the rewrite side, which DD13 requires and which
`[LJ-1.342]` refused to do.** Its words:

> **The rewrite side prices at ZERO.** The ideal chapter exists in the tree
> (`[LJ-1.342]`'s generic `predOf`/`carveAt` form); the successor fact
> consumers use is exported as `defStage-suc`,
> `src/L/Choice/Stage.lagda.md:313-315`; no consumer imports `meet-suc`; its
> one designed consumer is recorded structurally unable to call it,
> `src/L/Choice/Step.lagda.md:100-101`; and re-instantiation costs the same
> three lines if ever wanted. **The keep side holds three lines plus a
> sunk-cost warrant**, which is DD13's exact target.

**The literature agrees**: the orthodox development folds first-appearance
bookkeeping into definitions and exports no such lemma,
`dev/literature/j-hierarchy.md:54-60`.

**DO NOT RE-OPEN THE RULING.** **Do re-derive its facts** (C-44); the ruling
itself corrected three figures and a fourth error would not surprise me.

## THE THREE CORRECTIONS `[LJ-1.364]` MADE, and they bind you

**`[LJ-1.342]`'s recorded price was wrong in three ways, MEASURED:**

1. **It saves 3 lines, not 4.**
2. **`carveMeets` STAYS.** It is consumed at `src/L/Choice/Stage.lagda.md:301`.
   **`[LJ-1.342]`'s deletion clause is MEASURED FALSE.** **Deleting it would
   break a live consumer.**
3. **The edit sites are FOUR, not two**: `src/Everything.lagda.md:667` and
   `:997`, plus the naming sentences in `Stage` and in `Step`, **in both
   languages**.

## DD23, AND IT MAKES THIS CHEAPER

**`[LJ-1.364]` measured that the name is NOT held only by the catalogue: live
narrative sits at `src/L/Choice/Stage.lagda.md:260-268` and
`src/L/Choice/Step.lagda.md:100-112`.** **That prose predates DD23 and is
grandfathered.**

**DD23 forbids WRITING mathematical prose, not removing it.** **So where a
sentence exists only to name `meet-suc`, STRIKE it rather than rewrite it.**
**`[LJ-1.364]`: 「the restatement makes the compliant prose treatment a strike
rather than a rewrite」.** **Do not compose new prose to replace what you
remove. If a paragraph would be left saying nothing, remove the paragraph.**

## DD13: ARCHIVE, NEVER DELETE

**`meet-suc` goes to `archive/`, not to nothing.** **`dev/ARCHIVE.md` records
for each retired module what it is, why it left, where it was last green,
WHAT IT DID RIGHT (from measurement, not praise), and what would reopen it.**
**Write that row.** **Its「what would reopen it」is `[LJ-1.364]`'s own line:
re-instantiation costs the same three lines if ever wanted.**

**A single lemma is not a module, so say in your report where you put it and
why that honours DD13.** **If the honest answer is that a three-line lemma
needs no archive module and its text belongs in the `dev/ARCHIVE.md` row
itself, say so and do that.**

## THE ABORT CRITERION (D-1)

- **IT RETIRES GREEN.** Report the real line delta, every edit site, the
  archive row, and the check time past the floor. STOP.
- **A CONSUMER APPEARS.** **`[LJ-1.364]` measured none and `[LJ-1.342]` was
  wrong about `carveMeets`. If a consumer exists, STOP and report it: the
  ruling was made on「no consumer」plus a zero rewrite price, and a consumer
  changes the first half.**
- **THE STRIKE LEAVES PROSE THAT NO LONGER PARSES.** Report the paragraph and
  what you did.

## CONSTRAINTS

- **You MAY edit `src/L/Choice/Stage.lagda.md`, `src/L/Choice/Step.lagda.md`,
  `dev/ARCHIVE.md`, and create an `archive/` file if you rule one is needed.**
  **NEVER touch `src/Everything.lagda.md`; I wire it after auditing your
  work.** **Report the exact two edits it needs.**
- **`src/` takes NO new mathematical prose (DD23).** Strike, do not compose.
- **`[LJ-1.371]` is live and writes only in `agents/tasks/LJ-1-371/`.** No
  collision.
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap is TWO.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **Create `agents/tasks/LJ-1-370/lj-1.370-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `lint-agda.py --check` and `scripts/site/weave-i18n.py --check`. **No em
  dash.** Evidence is `file:line`. ASD-STE100. Mark every negative
  **MEASURED** or **INFERRED**.

## PREMISES

- **`meet-suc` has no code consumer**, at `src/L/Choice/Step.lagda.md:100-101`
  (`[LJ-1.364]`, MEASURED).
- **`carveMeets` IS consumed and must stay**, at
  `src/L/Choice/Stage.lagda.md:301` (`[LJ-1.364]`, MEASURED, correcting
  `[LJ-1.342]`).
- **`defStage-suc` already exports the successor fact consumers use**, at
  `src/L/Choice/Stage.lagda.md:313-315`.
- **The edit sites are four, and the saving is three lines.**

**Mark each VERIFIED or REFUTED at `file:line` in your return.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-five briefs carried a claim an agent measured
FALSE.** **The one at risk: every line number above is `[LJ-1.364]`'s, taken
this morning, and `[LJ-1.364]` itself found `[LJ-1.342]` wrong about a
deletion at exactly this site.** **Re-derive all four citations before you
edit anything.**

## THE RULES

**DD13 governs a retirement and it is priced from the REWRITE side; the price
is already paid, so your job is the archive discipline rather than the
argument.** **DD23: strike prose, never compose it.** **C-44: re-derive every
line.** **C-45, C-57, D-10, C-42, C-53, C-55, C-58, P-h, P-l, P-k, P-m, P-n,
R-35, R-38, R-40.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5.
**D-1, D-26.** **DD0, DD4, DD8, DD9, DD18, DD19, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**`L.Choice.Stage` is in the AC closure. Say whether it is in the GCH closure
too**, from `.venv/bin/python scripts/measure/ledger.py --reuse` rather than
from memory, **and report the closure for both ends after your edit.** **A
retirement that shrinks only one wing is a different DD4 fact from one that
shrinks both, and the row should say which.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route have a
  first-appearance successor lemma, and what became of it?** **A retired
  analogue is the closest comparable this retirement has.**
- **`archive/dev/TASKS-archived.md`**: **grep for the retired route's stage
  machinery**, taking SHAPE and never a claim.
- **`archive/dev/DECISIONS-archived.md`**: the archive regime, D20. **Cite the
  line that says retired code is archived and never deleted.**
- **`archive/dev/JOURNAL-archived.md`**: **WHY NOT in one line if nothing
  bears on a three-line lemma's retirement.**

## LITERATURE (DD18)

**`dev/literature/j-hierarchy.md:54-60`.** **`[LJ-1.364]` cited it as saying
the orthodox development exports no such lemma. VERIFY that, quote the line,
and say whether it supports the retirement or merely fails to oppose it.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Choice/Stage.lagda.md:255-320` FIRST, whole: it holds `meet-suc`,
`carveMeets` at `:301` and `defStage-suc` at `:313`, so it decides three of
the four premises at once.

## SCOPE (write)

`src/L/Choice/Stage.lagda.md`, `src/L/Choice/Step.lagda.md`,
`dev/ARCHIVE.md`, an `archive/` file if you rule one is needed, and
`agents/tasks/LJ-1-370/`.

## RETURN

**Lead with ONE line: does it retire green, and at what real line delta
against the ruling's 3.** Then every premise, VERIFIED or REFUTED. Then the
four edit sites and what you struck. Then the two `src/Everything.lagda.md`
edits for me. Then the archive row. Then the closure for both ends. **Mark
every negative MEASURED or INFERRED.**
