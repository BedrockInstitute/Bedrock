# LJ-1.186: compress the `DD` series to the rule itself, and move the rest to the journal

tier: pi (deepseek-subagent-mode). **The switch's default row, taken as the
table gives it.** `scripts/dispatch_policy.py` is the only place the tables live.

## GOAL

**The owner ordered this on 2026-08-14: the `DD` series is bloating. Compress it
by MEANING. Leave the pure rule. Move the episodes and the evidence to
`dev/JOURNAL.md`.**

**MEASURED: 19 rows, 41,981 characters in the ruling column.** Five rows carry
most of it: DD5 at 7,904, DD17 at 5,269, DD4 at 4,180, DD18 at 4,077 and DD2 at
3,515.

## THE OWNER'S SECOND INSTRUCTION, and it is the one that gives you licence

> **Per DD0, the extended interpretation can be compressed away. Keep the
> fundamentalist core.**

**DD0 is the first row of the table. Read it first.** It rules that the owner's
temporary instructions are not an interpretation of the `DD` rules, and that the
orchestrator never derives a standing rule from a one-off owner instruction.

**Its consequence for you: a passage that READS a ruling, rather than STATING
it, is the orchestrator's own reading and it is what you are here to remove.**
The owner's words are the rule. Everything layered on top is commentary.

## THE TEST, one question per sentence

For every sentence in a ruling, ask: **does a reader need this to know what they
must DO or NOT DO, or to know WHO ENFORCES it?**

- **YES: it stays.** The obligation, the prohibition, the threshold, the
  enforcement point, the named exception with its conditions.
- **NO: it moves.** Why it was ruled, what it cost, who caught it, what was
  measured, what the rule replaced, what an earlier version got wrong, and every
  worked example.

**ENFORCEMENT POINTS STAY.** `AGENTS.md` says a rule that no machine enforces
must name its enforcement point, and that a row claiming more than its checker
delivers turns a rule into false safety. **So a row that says 「enforcement is
review only」 KEEPS that sentence.** It is part of the rule.

## THE HARD CONSTRAINT: NOTHING IS LOST

**Every sentence you take out of a row appears in `dev/JOURNAL.md`.** This is
DD13's 「archive, never delete」 applied to prose.

**PROVE IT.** Your report carries a table: one line per row, the characters
before, the characters after, and the journal heading that received the
remainder. **A row whose remainder went nowhere is a defect, not a compression.**

## THE HARDER CONSTRAINT: COMPRESSION IS NEVER AMENDMENT

**You may not change what any rule REQUIRES.** Not by a word.

**If you find a row whose rule you cannot state without deciding something the
row leaves open, STOP on that row, leave it untouched, and name it in your
report.** The owner rules it, never you and never me. **A row you left alone
with a reason is a better return than a row you resolved.**

**Do not renumber. Do not merge rows. Do not retire a row.** A number is never
reused and the consolidated codes still resolve.

## WHAT `dev/JOURNAL.md` GETS

**One dated entry, 2026-08-14, holding the remainder, organized by `DD` code.**
Read the file first and match its existing voice and structure.

**Each row's remainder keeps its citations at `file:line` and its task codes.**
The evidence is what makes the journal worth having; a summary of evidence is
worth nothing.

**And the row keeps a pointer back**, in the form the file already uses, so a
reader who wants the reasoning can find it in one step.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **COMPRESSED.** Report the before and after per row, the journal headings, and
  every row you left alone with its reason. STOP.
- **A ROW WILL NOT COMPRESS.** Some rows are already pure rule. DD1, DD22 and
  DD15 may be. **Say so and leave them.** A row that was already right is a
  finding.
- **THE RULE IS NOT SEPARABLE.** If a row's obligation only makes sense with its
  measurement inside it, **leave the measurement and say why**. `dev/LESSONS.md`
  entries are measurements by design; a `DD` row may legitimately carry one.
- **YOU CANNOT TELL RULE FROM READING.** Name the passage and stop on that row.

## WHAT YOU MUST NOT DO

- **Do not touch `AGENTS.md`.** DD19 requires the owner's ruling and a dated
  `AGENTS-diff-approved:` trailer, and this task has neither.
- **Do not touch any brief or any report.** They are frozen records.
- **Do not touch `src/`, and do not run Agda.** Two siblings are building and
  one is measuring seconds.
- **Do not touch `dev/LESSONS.md`.** Its entries are measurements and they bind
  new code. **A `DD` row's remainder goes to the JOURNAL, never to LESSONS**,
  even when it reads like a law. Proposing a law is a separate act with its own
  rule.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE TRAP THIS PROJECT HAS PAID FOR FOUR TIMES TODAY

**A search that excludes what it is looking for.** Four times on 2026-08-14 the
orchestrator grepped for a narrow form and acted on the count: `(override)` in
parentheses when the real form was `(version \`override\`, ...)`, five hits
against a true 52; a struck ruling by its NUMBER when two more sites wrote its
NAME.

**So when you sweep a row for a passage, sweep for the SHAPE and not for one
spelling.** Say which searches you ran.

## THE CLASSIFICATION I WANT ON EVERY JUDGEMENT

**RULE or READING, in those words**, for any passage where the call was not
obvious. **A borderline passage that you kept is cheaper than one you moved.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD4's row is one of the five largest and it is the one to be most careful
with.** Its enforcement IS repetition, stated in every brief and answered in
every return, and `scripts/check-dd4-stated.py` now gates that a brief says it.
**So DD4's row must keep: the obligation, the no-metric ruling and its reason in
one clause, the three moments, the attitude clause, the one measured exception,
and the enforcement point.** Its measurements and its two paid-for episodes are
the remainder.

## ARCHIVE (DD18)

- **`dev/PLAN.md` section 3 WHOLE**, and DD0 first.
- **`dev/JOURNAL.md` WHOLE**, for the voice and the structure you must match.
- `archive/dev/DECISIONS-archived.md`: the retired `D` series, for how a
  consolidated row reads after the fact. **A `D` citation resolves only there.**
- `AGENTS.md`'s 「Where the rules live」 table: **read the row on project
  rulings**, which says a fact belongs in exactly one place, a ruling is a row,
  an episode is a journal entry, and a law is a LESSONS entry. **That division
  is this task's whole specification.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`dev/PLAN.md` section 3, then `dev/JOURNAL.md`.

## SCOPE (write)

`dev/PLAN.md` section 3, `dev/JOURNAL.md`, and
`agents/tasks/LJ-1-186/lj-1.186-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent.
- **DD0, DD13, DD19. D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36,
  C-37, C-39, C-40. I-5. P-l.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on everything you write, and
  `python3 scripts/check-rule-ids.py`, which resolves every code.
- **No em dash in any language.** CJK prose takes full-width punctuation.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the character count before and after, and the number of rows you
left untouched.** Then the per-row table with its journal heading. Then every
row you stopped on, with the passage you could not classify. Then the searches
you ran. **Mark every judgement RULE or READING.**
