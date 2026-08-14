# LJ-1.191 report: P1, the load-bearing-claim SKILL, built

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash. Build task.
The skill and this report were written. No Agda ran. No dispatch was made.
No commit, no push.

## 0. LEAD

**The skill exists at `.claude/skills/load-bearing-claim/SKILL.md`, and its
`description:` line, quoted whole:**

> "Verify, verified, MEASURED, measured, the bar, priced at: bind the claim
> these words start to the artifact that established it. A claim written
> MEASURED names the search that established it and the search's filter. A
> figure written into any document traces to the report row that measured
> it, at file:line. A source named in a brief is a claim that you opened it
> and read the part that bears. A fix sweeps by SHAPE, then sweeps the
> record, before declaring done. A brief's premise is the thing the dispatch
> tests: a premise from a memory, a verdict cell or a prior brief is a
> false-premise candidate until the report row it rests on is named. Load
> when about to write a claim, a figure, a verdict, a premise, a comparable,
> a search result or a done-declaration into a brief, a plan, a status
> screen, a commit body, a report or a checker. Triggers: verify, verified,
> MEASURED, measured, counted, the bar, priced at, stands at, costs, lines,
> seconds, rate, reads, quoted, figure, comparable, premise, basis, fixed,
> clean, done, grep, search, census, sweep, filter, nothing in, absent, no
> consumer, no supplier, zero references."

The description leads with `verify, MEASURED, the bar, priced at`, exactly
as the proposal's section 4 requires: the skill is named for the VERIFY and
WRITE moments, never the search moment.

## 1. The checklist: every rule in `[LJ-1.189]` section 4

Each rule is marked present or absent in the skill. All five are present.

| rule | in the skill | evidence kept |
|---|---|---|
| 1. A claim written MEASURED names the search that established it, and the search's filter | PRESENT | `4d77090`, `ac30ff1`, `ba88df4`, `c45a257`, `8736fdb`, the `[LJ-1.170]` brief, plus the `(override)` shape trap and the 2026-08-14 five-times line |
| 2. A figure written into any document traces to the report row that measured it, at file:line | PRESENT | `a6c5581`, `5be8195`, `4a97520`, `73d8f22`, `cfe2b5a`, `4a12cac` |
| 3. A source named in a brief is a claim: you have opened it and read the part that bears | PRESENT | `85507b4`, `de353ef`, `bba3070` |
| 4. Sweep by SHAPE, then sweep the record for the same shape, before declaring done | PRESENT | `819b482`, `bb3907b`, `cda4619` |
| 5. A brief's premise is the thing the dispatch tests | PRESENT | `0cb9b17` and the false-premise list in section 1 of the proposal |

Every hash in section 4 is kept. No rule from the proposal was dropped, and
no rule the proposal did not measure was added. Section 8's no-cure list is
carried so the skill promises nothing it cannot deliver: misreading the
right artifact, tool changes under a measuring agent, and the residual
attention failure are each named as having no cure.

## 2. The would-it-have-loaded test

**Answer: yes, and the mechanism is the model's own words.** The test
`[LJ-1.189]` set asks whether the skill would have LOADED at the moment the
error happened. The load comes from the `description:` field, matched
against the model's context. At every founding episode the trigger word is
in the model's own text, because the error IS the writing:

- At `4d77090` the model typed `grep` and wrote "MEASURED: nothing in src/
  supplies it". Both words are triggers.
- At `4a97520` it wrote "the bar is 0.0136". "the bar" is a trigger.
- At `73d8f22` it wrote "DD24 reads 1.91x". "reads" is a trigger.
- At `819b482` it wrote "the brief carries zero references". "zero
  references" is a trigger.
- At `85507b4` it wrote "ARM A's delivered comparable". "comparable" is a
  trigger.

The proposal's caution is honored in the same line: a skill named "searching"
would not have loaded, because the model thought it was verifying. The
description therefore leads with the verify words, and the search words
(`grep`, `search`, `census`, `sweep`, `filter`) appear only later in the
trigger list.

INFERRED, and said so in the skill: the load itself is not observable until
the skill exists. The claim that the trigger words appear at each moment is
MEASURED, from the commit bodies read at `git log -1 --format=%B <hash>`.

## 3. Does any cited commit contradict the proposal?

**No.** I read every hash that section 4 cites, whole, and checked each
against the claim the proposal makes. The verification sweep, one pass per
hash, is in ARCHIVE USED. Three attributions needed the full body to
confirm, and all three confirmed:

- `4a97520` (the 0.0136 bar): the body reads "My brief quoted the bar as
  0.0136. That is the PRE-SEAL bar." CONFIRMED.
- `cfe2b5a` (the 455): the body reads "455 occurs zero times in that
  report; it is a sum of six per-step counts, restated as a measurement."
  CONFIRMED.
- `8736fdb` (the Axioms/Separation blind spot): the body reads "This wing's
  blind spot this time was src/L/Axioms/Separation.lagda.md". CONFIRMED.

One attribution needed the surrounding history, and it held:
`cda4619`'s body says the three briefs' bar sections were corrected and
"Only the bar was wrong". The proposal says it "fixed the bar section and
left three spots". Both are true: the audit at `819b482` (later in the same
history) found the struck DD27 figure in three places in `[LJ-1.178]`'s
brief, the abort criterion and the mandatory rules writing DD27 by name.
The skill states the episode with both halves so it cannot mislead.

## 4. The searches I ran

The brief's trap section demands I say which searches I ran, swept by
shape, never by one spelling.

- **The hash sweep.** `git log -1 --format="%h %ad%n%n%B" --date=short` on
  each of the seventeen hashes in section 4, plus the full body
  (`git log -1 --format=%B`) for `4a97520`, `cfe2b5a`, `de353ef`,
  `cda4619`, `8736fdb`. This is the verification sweep for section 3.
- **The rules sweep.** `python3 scripts/rules.py --for recon`, whole, and
  the recon bundle read at `dev/rules.toml:47-49`. The mandatory rules read
  at their homes: DD0 at `dev/PLAN.md:244`; D-10 at `dev/LESSONS.md:1333`;
  D-26 at `dev/LESSONS.md:1693`; D-29 at `dev/LESSONS.md:3260`; D-30 at
  `dev/LESSONS.md:3350`; C-31 at `dev/LESSONS.md:1873`; C-32 at
  `dev/LESSONS.md:2965`; C-33 at `dev/LESSONS.md:3005`; C-34 at
  `dev/LESSONS.md:3189`; C-36 at `dev/LESSONS.md:3302`; C-37 at
  `dev/LESSONS.md:3399`; C-39 at `dev/LESSONS.md:3539`; C-40 at
  `dev/LESSONS.md:3620`; C-41 at `dev/LESSONS.md:3657`; C-42 at
  `dev/LESSONS.md:3704`; C-43 at `dev/LESSONS.md:3758`; P-l at
  `dev/LESSONS.md:2323`; I-5 at `dev/LESSONS.md:1213`; C-22 at
  `dev/rules.toml:49` and the brief's own MANDATORY RULES line.
- **The shape sweep for `(override)`.** I did not re-run the orchestrator's
  `(override)` grep; the 52-versus-5 count is taken from the proposal's
  section 1 at `4f2c541`, and the shape lesson is quoted into the skill. A
  fresh grep would measure the tree, not the episode.
- **The skill shape sweep.** `cat` of `dispatch-herdr/SKILL.md` and
  `asd-ste100/SKILL.md` for the frontmatter and description shape, and of
  `update-agents-md/SKILL.md` for the trigger-list form.

No search in this task excluded the thing it looked for. The one filter
used, the `--for recon` bundle, was checked against `dev/rules.toml` for
its full membership rather than trusted from the printed tail.

## 5. The abort criteria, answered

- **BUILT.** The skill exists, its description names the triggers, and
  every rule from section 4 is in it with its evidence. The description is
  quoted whole in section 0. The abort criterion's first branch is met, so
  I stop here.
- **A RULE CANNOT BE WRITTEN AS A TRIGGER.** Not triggered. All five rules
  are write-moment rules and each writes its own keyword: "MEASURED",
  "figure", "comparable", "clean" and "premise" are all in the description.
  The proposal's own refutation mechanism does not fire.
- **A RULE IN THE PROPOSAL IS WRONG.** Not triggered. Section 3 records the
  verification of every hash.

## 6. DD4

The skill is written generic. It names no task kind, no document, no head
and no dispatch mode. Its rules bind any document that carries claims:
a brief, a plan, a status screen, a commit body, a report or a checker. The
six figures of the week appear as episodes, never as the rule, and the rule
is stated so it transfers: name the search and its filter, trace the figure
to its row, name the source only when you read the part that bears, sweep by
shape, name the premise's row.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-189/lj-1.189-report.md`, read whole. This is the
  proposal I built: section 4 for the five rules and their hashes, section 8
  for the no-cure list the skill must not promise, section 4's trigger list
  for the description, and the sharp-question answer I carry into section 2.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole. Took the shape:
  the description as the trigger, the MEASURED/INFERRED/UNMEASURED marking,
  the "The trigger" section that says there is no slash command and no magic
  word.
- `.claude/skills/asd-ste100/SKILL.md`, read whole, and
  `.claude/skills/update-agents-md/SKILL.md` frontmatter: the description
  shape, "what it does, then trigger phrases".
- `dev/LESSONS.md` C-32 at `:2965`, C-39 at `:3539`, C-40 at `:3620`, C-41
  at `:3657`, C-42 at `:3704`, C-43 at `:3758`, read whole: the process
  laws the skill must not restate, and C-32's failure to reach the moment of
  action, which is this batch's argument.
- The mandatory rules read at their homes, listed with `file:line` in
  section 4: DD0, D-10, D-26, D-29, D-30, C-31, C-33, C-34, C-36, C-37,
  P-l, I-5.
- `scripts/rules.py --for recon`, whole, and `dev/rules.toml:47-49` for the
  bundle's membership.
- `git log -1 --format=%B` on every hash in section 4 of the proposal:
  `4d77090`, `ac30ff1`, `ba88df4`, `c45a257`, `8736fdb`, `a6c5581`,
  `5be8195`, `4a97520`, `73d8f22`, `cfe2b5a`, `4a12cac`, `85507b4`,
  `de353ef`, `bba3070`, `819b482`, `bb3907b`, `cda4619`, `0cb9b17`, plus
  `git log cda4619~1..819b482` for the ordering that reconciles `cda4619`
  with the audit's finding. This is the verification corpus for section 3.

## LITERATURE (DD18)

Not this task's subject. Nothing in `dev/literature/` bears on building a
load-bearing-claim skill; DD18 is satisfied by this one line.

## CONSTRAINTS CHECK

`python3 scripts/lint-prose.py --check` run on both files, clean. No em
dash in either file. Evidence is a commit hash or `file:line`. Written
ASD-STE100. C-22 honored: the skill was written first and the report
second, so the deliverable survives independently of this report.
