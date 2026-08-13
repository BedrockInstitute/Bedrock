# LJ-1.137: apply the four ruled `AGENTS.md` blocks, and pay for them from the file's own fat

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`AGENTS.md` carries two sentences that are FALSE today. The owner has ruled
four blocks in. They cost 129 words and the file has 43 words of headroom.**

**Your job is the 86 words. Find them in the EXISTING text, and cut them.**

## THE RULING

The owner ruled on 2026-08-13: apply the four blocks below, and **pay for them
by trimming, not by raising the cap.**

**The owner's reason, and it decides your whole method:** the cap exists
because `AGENTS.md` says of itself 「A rulebook nobody finishes reading binds
nothing」. **Raising the cap reflexively is how that rule dies.** The cap went
from 2,200 to 2,300 on 2026-08-10 already.

## THE ARITHMETIC, which I measured

| | words |
|---|---:|
| `AGENTS.md` today | **2,257** |
| cap, `scripts/check-dev-docs.py:105` | **2,300** |
| headroom | **43** |
| the four ruled blocks | **+129** |
| **you must cut** | **at least 86** |

**Verify every one of those numbers yourself before you cut anything.** The
count is `len(text.split())`; `check-dev-docs.py` is the authority.

**Cut 110 to 130, not 86.** A file at the cap fails the next true sentence
somebody needs to add, and this is the third time in four days that the cap
has bound.

## THE FOUR BLOCKS, ruled and to be applied EXACTLY

### 1. The dispatch row (`[LJ-1.127]`, approved as 丙 on 2026-08-13)

The full diff and its reasoning are at
`agents/reports/lj-1.127-agents-diff.md:29-35`. **Read that file whole.** Apply
its one-row replacement verbatim. +15 words.

### 2. The routing row (`[LJ-1.130]`), because the row is FALSE

`AGENTS.md:105` sends probe reports and briefs to `_build/`. **They live in
`agents/`.** An agent reading it writes its report to the wrong place.
Replacement is at `agents/reports/lj-1.130-report.md`, section 9, "Second, the
routing row". +34 words.

### 3. The `_build` Never line (`[LJ-1.132]`)

The 32-word Never line, NOT the 73-word table row. The owner took the
actionable half and left the table row out. Text is at
`agents/reports/lj-1.132-report.md`, section 10.5, "And one line for the Never
list". +32 words.

### 4. The probe sentence (`[LJ-1.133]`), because the sentence is FALSE

`AGENTS.md:136-138` says 「Nobody commits one」. **`archive/probes/` holds 244
committed probes today.** Replacement is at
`agents/reports/lj-1.133-report.md`, section 6. +48 words.

**Take each text from the report that proposed it, not from my summary.** I
have already introduced one paraphrase error into a governance document this
session.

## WHAT IS **NOT** RULED IN, so do not apply it

- `[LJ-1.130]`'s Never-list "build output" rewrite (+16). **The owner judged
  the current line not false:** it forbids committing `_build/`, and reports
  are no longer there.
- `[LJ-1.130]`'s "never rewrite a brief or a report" line (+22). No
  enforcement point.
- `[LJ-1.132]`'s 73-word lifecycle table row.

**If your reading of the file says one of these three is needed after all, say
so in the report with the reason. Do not apply it.**

## HOW TO FIND THE 86 WORDS, and this is the real task

**`AGENTS.md`'s own preamble gives you the test, and it is better than any
test I could write:**

> **This file is deliberately short.** It holds only what changes what you DO
> on a task. For everything else, read one row in Where the rules live.

**So: for every paragraph, ask what an agent would DO differently if the
paragraph were gone.** If the answer is "nothing", it is fat. Candidates the
file itself suggests:

1. **A rule stated twice.** The file says 「Nothing is canonical twice: where
   this file restates a rule, the other document rules and this one
   summarizes」. **A restatement that has grown longer than a summary is fat by
   the file's own rule.** Look hard at Boundaries against the rules table.
2. **A history that no longer changes an action.** 「Memory drifted for five
   days while an imported playbook sat uncited in 102 of 112 briefs」 is a
   reason, and some reasons earn their words. **Others are settled and the
   action is now habit.** Judge each.
3. **A row whose gloss has become an essay.** The gloss column exists so a
   reader can skip the file. A gloss longer than the rule is fat.
4. **A dead cross-reference.** A rule pointing at something retired.

**Cut whole clauses, not adjectives.** Twenty words shaved off twenty
sentences leaves a file that reads worse and says the same. **Better: find two
or three passages that have stopped earning their space and remove them
entirely.**

## WHAT YOU MUST NOT CUT

- **Anything that changes what an agent DOES.** When in doubt, keep it.
- **DD4.** It is stated in the file as 「the rule that has cost this project
  most」, it has no metric and no checker by the owner's decision, and its ONLY
  enforcement is that it is repeated. **Cutting it would be cutting its
  enforcement.**
- **The Never list**, except as ruled above.
- **Any `file:line` or command that an agent runs.**
- **The 「Ask first」 list**, which is the owner's own authority.

## THE CHECK THAT MUST PASS

```
.venv/bin/python scripts/check-dev-docs.py
.venv/bin/python scripts/check-agents-guard.py
.venv/bin/python scripts/lint-prose.py --check AGENTS.md
.venv/bin/python scripts/check-rule-ids.py
```

**Report the final word count and the headroom.**

## WHAT YOU MUST NOT DO

- **DO NOT COMMIT.** DD19 requires the owner's ruling on the diff AND a dated
  `AGENTS-diff-approved:` trailer, and `check-agents-guard.py` refuses a
  commit without it. **The owner has ruled on the four blocks. The owner has
  NOT seen your trim.** Leave the tree edited and unstaged; I show the owner
  and I commit.
- **Do not raise `AGENTS_WORD_CAP`.** That is the one thing the owner ruled
  out.
- **Do not edit `CLAUDE.md`.** It imports `AGENTS.md`; there is nothing to
  mirror.
- **Do not touch `src/`, and do not run Agda.** Two siblings are running and
  one is measuring build times.
- Never push, never `git checkout .`, `git stash`, `git reset --hard` or
  `git clean`. **The tree carries three agents' uncommitted work.**

## THE ABORT CRITERION

- **You find 110 to 130 words of real fat**: cut, apply the four blocks,
  report, STOP.
- **You cannot find 86 words that do not change an action**: **STOP AND SAY
  SO.** Report the closest you got and what it would cost. **That is a real
  finding and it tells the owner the cap is now genuinely binding**, which is
  the evidence needed to move it. **Do not shave adjectives to hit a number.**
- **A cut you propose is arguable**: apply the safe ones, list the arguable
  one separately with the reason.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「Nothing depends on this
paragraph」 is MEASURED only if you searched, and say which search.

## ARCHIVE (DD18)

- **`agents/reports/lj-1.127-agents-diff.md`**, read WHOLE.
- **`agents/reports/lj-1.130-report.md` section 9**, `lj-1.132-report.md`
  section 10.5, `lj-1.133-report.md` section 6.
- **`scripts/check-agents-guard.py`**, read WHOLE, especially the docstring:
  it records the 2026-08-04 incident that created DD19.
- `scripts/check-dev-docs.py:105` and `:210`, the cap and its message.
- `dev/PLAN.md` DD19.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a rulebook. Say so in one line.**

## SCOPE (read)

`AGENTS.md` WHOLE and slowly, FIRST. Then the four proposal sources.

## SCOPE (write)

**`AGENTS.md` only.** Your report is `agents/reports/lj-1.137-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write: name any passage you judged
  fat but did not dare cut.
- **C-39.** A brief's prohibition binds harder than its goal. **The
  prohibition here is the cap and the commit ban.**
- **C-40.** Verify the CONSUMERS of a changed master. **`AGENTS.md`'s
  consumers are `CLAUDE.md`, `check-agents-guard.py`, `check-dev-docs.py` and
  `check-rule-ids.py`. Run all of them.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29.**

## CONSTRAINTS

- **`AGENTS.md` is English and ASD-STE100 does NOT bind it**, because nobody
  rewrites an existing document for that rule. **Match the voice that is
  there.**
- **No em dash, in any language.**
- Evidence is `file:line`. Your report is ASD-STE100.

## RETURN

**Lead with the final word count and the headroom.** Then the cuts: each
passage, its word count, and what an agent would do differently without it.
Then the four blocks applied, each confirmed against its source. Then anything
you judged fat and did not cut. Then the four checkers, clean. **Mark every
negative MEASURED or INFERRED.**
