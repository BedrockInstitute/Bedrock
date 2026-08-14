# LJ-1.187: put every part of `dev/` in the place its KIND belongs

tier: pi (deepseek-subagent-mode). **The switch's default row, taken as the
table gives it.** `scripts/dispatch_policy.py` is the only place the tables live.

## GOAL

**`[LJ-1.186]` did this for the `DD` table and took it from 41,981 characters to
28,662 with nothing lost. The owner ordered the same treatment for the REST of
`dev/`.**

**Two defects, and they are one defect seen twice: BLOAT, and CONTENT IN THE
WRONG DOCUMENT.**

## THE DIVISION, and it is not mine

`AGENTS.md` states it, and `dev/PLAN.md` restates it in its own opening:

> **A fact belongs in exactly ONE place: a RULING is a row in `dev/PLAN.md`
> section 3, an EPISODE is an entry in `dev/JOURNAL.md`, a LAW is an entry in
> `dev/LESSONS.md`.**

Add the two the table names elsewhere: **a standing FIGURE belongs in
`dev/ledger.toml`**, whose header carries the caliber; and **a term rendering
belongs in `dev/glossary.toml`**.

**That division is this task's whole specification. Test every part of every
document against it.**

## THE OWNER'S OWN EXAMPLE, so you know the shape you are hunting

`dev/PLAN.md:460`, under `### Task index (one row per dispatch, section 6.0
rules 7 and 8)`.

**The first paragraphs are RULE**: the code is `LJ-<phase>.<step>`, what each
phase is, and that a phase is a barrier. **That defines the index and it stays.**

**What follows is EPISODE and it must move**: 「TWO PIECES OF EVIDENCE THE RULING
IS OWED, and the record on one of them was wrong until `[LJ-1.149]` read it」,
then a probe's exit code, its seconds, its line count, and four documents that
carried a false claim for four days.

**That is a journal entry sitting inside a section header's preamble.**

## SECTION 3 IS OFF LIMITS. THIS IS A HARD PROHIBITION

**DD0 was amended by the owner on 2026-08-14 and it now reads, in its title:**

> **`DD` rows are the owner's: edit one only when asked.**

**The owner asked for the REST of `dev/`, not for section 3.** `[LJ-1.186]`
already compressed it under a separate instruction.

**So: do not touch any `DD` row, do not touch section 3, and do not move
anything INTO it.** If you find content elsewhere that you believe is a RULING
and belongs in section 3, **name it in your report and leave it where it is.**
The owner rules it.

## WHAT TO DO

1. **Read every file under `dev/`**: `PLAN.md`, `JOURNAL.md`, `ORCHESTRATION.md`,
   `LESSONS.md`, `STYLE-agda.md`, `STYLE-i18n.md`, `ARCHIVE.md`, `GLOSSARY.md`,
   `README.md`. **Also `dev/memos/` and `dev/literature/`, at least far enough
   to say whether they hold misplaced content.**
2. **For every section, classify it**: RULE, EPISODE, LAW, FIGURE, or REFERENCE.
3. **Move what is misplaced**, to the document its kind names.
4. **Compress what is bloated**, by the same test `[LJ-1.186]` used: does a
   reader need this sentence to know what they must DO or NOT DO, or WHO
   ENFORCES it?

## THE HARD CONSTRAINT: NOTHING IS LOST

**Every sentence you move appears at its destination.** DD13's 「archive, never
delete」 applied to prose.

**PROVE IT with a table**: one line per move, the source at `file:line`, the
destination heading, and the characters before and after. **A remainder that
went nowhere is a defect, not a compression.**

## THE HARDER CONSTRAINT: THIS IS NEVER AMENDMENT

**You may not change what any rule REQUIRES, and you may not change a
measurement.** Not by a word, and not by rounding.

**If a passage cannot be classified without deciding something the document
leaves open, STOP on it, leave it, and name it.** A passage you left alone with
a reason is a better return than one you resolved.

## `dev/LESSONS.md` IS THE TRAP, and it is the largest file at 3,847 lines

**Its entries are MEASUREMENTS BY DESIGN and they BIND NEW CODE.** A lesson
carries its measurement, its provenance and when it bites, and **all of that is
the law, not decoration.** `scripts/rules.py` routes them and
`scripts/check-rule-ids.py` resolves every ID.

**So do NOT compress a lesson's measurement out of it.** What to look for there
is different: **an entry that is really an EPISODE with no measurement**, or a
passage that restates a `DD`.

**A rule that is canonical twice is a DD19 defect**, and `[LJ-1.183]` found one
this week: `dev/ORCHESTRATION.md` named the dispatch heads that
`scripts/dispatch_policy.py` owns. **Look for more of that shape.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **PLACED.** Report the moves, the compressions and everything you left alone.
  STOP.
- **A DOCUMENT IS ALREADY RIGHT.** **Say so plainly.** `[LJ-1.186]` found NINE
  of nineteen rows already pure rule, and that was a real result.
- **THE DIVISION DOES NOT DECIDE A PASSAGE.** Name it and stop on it.
- **A MOVE WOULD BREAK A CITATION.** Some passages are cited by `file:line` from
  briefs and reports, which are FROZEN records. **Report the citation you would
  break and leave the passage.** C-41: a citation that resolves to the wrong
  thing is worse than one that dangles.

## WHAT YOU MUST NOT DO

- **Do not touch `dev/PLAN.md` section 3 or any `DD` row.** See above.
- **Do not touch `AGENTS.md`.** DD19 requires the owner's ruling and a dated
  `AGENTS-diff-approved:` trailer, and this task has neither.
- **Do not touch any brief or any report** under `agents/`. Frozen records.
- **Do not touch `src/`, and do not run Agda.** A sibling may be building.
- **Do not renumber a lesson or a ruling. Do not retire one.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE TRAP THIS PROJECT PAID FOR FIVE TIMES ON 2026-08-14

**A search that excludes what it is looking for.** The orchestrator grepped for
`(override)` in parentheses when the real form was `` (version `override`, ...)
``, got five hits against a true 52, and acted on the five. It grepped a struck
ruling by its NUMBER when two more sites wrote its NAME.

**So sweep by SHAPE and never by one spelling, and say which searches you ran.**

## THE CLASSIFICATION I WANT ON EVERY JUDGEMENT

**RULE, EPISODE, LAW, FIGURE or REFERENCE, in those words**, for any passage
where the call was not obvious. **A borderline passage you KEPT is cheaper than
one you moved.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is a placement question about itself.** Its enforcement is repetition
in every brief, and `scripts/check-dd4-stated.py` now gates that a brief says
it. **If you find DD4's obligation restated anywhere outside its own row and
outside a brief, that is the canonical-twice defect and you report it.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-186/lj-1.186-report.md`**, read WHOLE. **The method you
  are extending, its per-row table, and its RULE-against-READING test.**
- **`dev/JOURNAL.md` WHOLE**, for the voice and structure you must match, and
  because its 2026-08-14 entry is where `[LJ-1.186]` put the `DD` remainder.
- `AGENTS.md`'s 「Where the rules live」 table, read WHOLE. **It is the
  specification.**
- `archive/dev/JOURNAL-archived.md` and `DECISIONS-archived.md`: how the retired
  series reads after the fact.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`AGENTS.md`'s rules table FIRST, then `agents/tasks/LJ-1-186/lj-1.186-report.md`.

## SCOPE (write)

Everything under `dev/` EXCEPT `dev/PLAN.md` section 3, plus
`agents/tasks/LJ-1-187/lj-1.187-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent.
- **DD0, DD13, DD19. D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36,
  C-37, C-39, C-40. I-5. P-l.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on everything you write, then
  `check-rule-ids.py`, `check-task-index.py`, `check-dd4-stated.py` and
  `check-archive-cited.py`.
- **No em dash in any language.** CJK prose takes full-width punctuation.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the number of misplaced passages you moved and the characters
compressed, per file.** Then the move table with destinations. Then every
passage you stopped on. Then any citation a move would have broken. Then the
canonical-twice defects. **Mark every judgement RULE, EPISODE, LAW, FIGURE or
REFERENCE.**
