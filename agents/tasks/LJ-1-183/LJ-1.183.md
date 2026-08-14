# LJ-1.183: audit the ORCHESTRATOR against every `DD`, under DD0

tier: pi (override). **The switch's adversarial row, taken as the table gives
it.** The owner named the harness and it is the same row. DD17's invariant
holds: the critic is never the same head as the author, and every target here
was written by the in-harness Opus 5.

## GOAL

**Run an adversarial audit of the ORCHESTRATOR, not of any agent and not of the
mathematics.**

**Find every place, in the recent record, where the orchestrator did not comply
with a `DD` ruling.** Replay the evidence: `git log`, the briefs under
`agents/tasks/*/`, and the reports beside them.

**The owner ordered this task on 2026-08-14, immediately after ruling DD0.**

## THE RULING THAT GOVERNS YOUR READING, and it is one hour old

**DD0**, `dev/PLAN.md` section 3, the first row:

> **The owner's temporary instructions are NOT an interpretation of the `DD`
> rules, and NOT an endorsement that the agent may disobey them. The owner may
> disregard any `DD` at any time, and that is not the agent's business.**

**So when you find the orchestrator doing something a `DD` forbids, the defence
「the owner told me to do something like this once」 is NOT a defence.** DD0's
test is the one to apply: **would the sentence justifying the choice write,
citing the RULING rather than the owner's past act?**

**And the converse binds you too: an instruction the owner gave for a NAMED task
is not a violation by the orchestrator.** Separate the two. **A finding that
blames the orchestrator for the owner's own decision is a false positive and it
costs more than a miss.**

## WHAT THE ORCHESTRATOR HAS ALREADY SELF-REPORTED

**These are ADMITTED. Verify each one is real and correctly scoped, then move
on. Your value is in what is NOT on this list.**

1. **DD0 and DD17.** Dispatched four DD25 adversarial reviews to `fable` when
   the switch's adversarial row reads `pi`, generalizing a one-off owner
   instruction. Recorded as DD0 and `dev/LESSONS.md` C-43.
2. **A DUPLICATE `DD27`.** Minted a second DD27 when DD27 was ruled 2026-08-10.
   The table's own preamble says a number is never reused.
3. **INVENTED READINGS OF DD24.** Wrote a module-rate-against-wing-rate
   question, a 「spent tolerance」 and a debt to collect, and shipped them to
   three agents as a ruling. The owner struck all of it.
4. **SIX FALSE BRIEF PREMISES**, most recently `[LJ-1.177]`, sent to cure a term
   `[LJ-1.158]` had cured five dispatches earlier, whose row sits directly below
   the row the brief cited.
5. **DD25 COMPLIANCE.** No negative return since `[LJ-1.160]` named a review
   code in its index row, which is DD25's own declared enforcement point.
6. **COLLIDING DISPATCHES.** Sent agents into masters another agent was
   actively editing, more than once, and warned none of them.

## WHERE TO LOOK, and build your own list rather than trusting mine

**`git log` since roughly 2026-08-13**, with the commit bodies read, because
this orchestrator writes its reasoning into them. **Read what a commit CLAIMS
against what its diff DOES.**

**Every brief and every report under `agents/tasks/`** for the same window.

**Check at least these rows, and say what you checked:**

| ruling | what to test |
|---|---|
| **DD4** | It must be stated in EVERY brief, whatever the kind, and answered in every return. **Count the briefs that carry it and the returns that answer it.** |
| **DD8** | A build brief must name its widest unmeasured term AND the probe that measures it. An estimate is ONE number naming its basis. |
| **DD13** | A retirement is priced from the REWRITE side, and nothing is deleted. |
| **DD15** | `make check` runs in the BACKGROUND, never the foreground. No standing figure quoted from a paragraph. |
| **DD17** | The brief's `tier:` line names the head AND the version. |
| **DD18** | EVERY brief carries an ARCHIVE section and a LITERATURE section; EVERY return carries ARCHIVE USED and LITERATURE USED at `file:line`. **`scripts/check-archive-cited.py` reports the drift; run it.** |
| **DD19** | An `AGENTS.md` edit needs the owner's ruling and a dated `AGENTS-diff-approved:` trailer. **Also: no rule is canonical twice.** |
| **DD23** | Mathematical prose is FROZEN until both trophies land. |
| **DD24** | The bar and how it was applied. **The owner ruled 2026-08-14 that DD24 is the whole rule and layered readings are the orchestrator's own.** |
| **DD25** | A negative return is adversarially reviewed IMMEDIATELY, and the index row names the review's code. |

## THE TWO FINDINGS I MOST EXPECT YOU TO BEAT ME TO

**1. A rule obeyed in FORM and dead in CONTENT.** `[LJ-1.157]` measured that 164
of 164 briefs carried the ARCHIVE heading while the CONTENT decayed to citing
the new route's own tasks. **C-41 is that shape and it has now appeared three
times.** Look for a fourth.

**2. A figure that reached a decision without a basis.** `[LJ-1.168]` measured
that a 5,047-line figure was never a measurement, and `[LJ-1.173]` withdrew a
+126 s extrapolation built on a delta inside the instrument's own band.
**`check-ratio.py` prints `noise band: at least +-12.8%, MEASURED [LJ-1.148]`.**
**Find another figure that a ruling or a dispatch rests on and that nobody
measured.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CENSUS COMPLETE.** Report it, ranked by what the violation COST or risked.
  STOP.
- **NOTHING BEYOND THE ADMITTED LIST.** **SAY SO PLAINLY.** That is a real
  result: it would mean the self-reporting is working. **Do not manufacture
  findings to fill a table.**
- **LARGER THAN YOU CAN COMPLETE.** Say how far you got, by what method, and
  what is left. **A partial census that names its own boundary is worth more
  than a complete-sounding sample.**

## WHAT YOU MUST NOT DO

- **Do not edit any master, any brief or any report.** They are frozen records.
  **You write your own report and nothing else.**
- **DO NOT RUN AGDA.** Siblings are running. This audit is a reading of the
  record.
- **Do not re-litigate the route or the mathematics.** DD2 rules the endpoint.
  **You audit COMPLIANCE, never whether a ruling is correct.**
- **A sibling's file may be RED while you read it.** `[LJ-1.178]` lost about
  fifteen minutes to that and said a brief line would have cost nothing. **This
  is that line: expect a dirty tree and read committed state where it matters.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY FINDING

**MEASURED or INFERRED, in those words.** 「No brief carried this」 is MEASURED
only if you searched every brief and say which search.

**And rank by COST**, in dispatches, lines, seconds or a wrong decision that
shipped. **A violation that cost nothing is still a violation and it is not the
same finding.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **Here it is the audit's own subject: DD4's only
enforcement is that it is stated in every brief and answered in every return.
MEASURE that compliance and report the two counts.** A rule whose sole
enforcement is repetition dies the moment the repetition lapses.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-157/`**, read the report WHOLE. **The previous audit of
  this same orchestrator, and its method is your baseline to beat.**
- `dev/PLAN.md` section 3 for every `DD`, section 0.0 for the live status, and
  section 11 for the task index.
- `dev/LESSONS.md` **C-39, C-40, C-41, C-42, C-43**, read WHOLE.
- `dev/ORCHESTRATION.md`, whole. **It is the rulebook the orchestrator works
  to.**
- `archive/dev/DECISIONS-archived.md`: **a `D` citation resolves only there**,
  and C-41 exists because live files cited the wrong series.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`git log` and everything under `agents/tasks/` and `dev/`.

## SCOPE (write)

`agents/tasks/LJ-1-183/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent. **So when
  you find one violation, sweep for the others of its shape.**
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0, DD8, DD25.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on anything you write.
- Evidence is `file:line` or a commit hash, on BOTH sides: the rule, and the act
  that broke it. Write ASD-STE100.

## RETURN

**Lead with the COUNT: how many violations beyond the admitted six, and what the
most expensive one cost.** Then the table, ranked by cost: the ruling, the act
at `file:line` or commit, what it cost, and whether the orchestrator
self-reported it. Then your method and its coverage. Then the DD4 compliance
counts. **Mark every finding MEASURED or INFERRED.**

**If the answer is 「nothing beyond the six」, say that in the first line.**
