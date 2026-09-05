# LJ-1.189 report: which recurring orchestrator errors a SKILL would prevent

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash. Read-only recon.
No skill, checker, brief, report or dev/ file was edited. No Agda ran.
No dispatch was made. No commit, no push.

## 0. LEAD

**Four proposals, and the one to build first is the load-bearing-claim skill.
Every finding is MEASURED or INFERRED in those words.**

| # | proposal | cure kind | covers |
|---|---|---|---|
| P1 | the load-bearing-claim skill | SKILL | known 1, 3, 4, 5, plus the new figure-travel and wrong-source shapes |
| P2 | the artifact-over-proxy skill | SKILL | the new proxy-over-artifact shape |
| P3 | the commit gate against the live-agent registry | CHECKER | the git-add half of known 2 |
| P4 | the DD number-uniqueness check | CHECKER | the minted duplicate DD27 |

**The finding under the findings, and it is the answer to the brief's own
question.** The seven known errors are not seven failures with seven cures.
They are ONE disease in seven costumes: **the orchestrator records and acts
on a claim, a search result, a figure, a status field, a named source or a
premise, and the claim is not bound to an artifact it opened.** The brief
asked which of the seven a skill would prevent. My answer: a skill prevents
the ones whose moment of action is a WRITING moment, because the model's own
words at that moment are the trigger. It does not prevent the attention
halves, and I name those plainly in section 8.

**The strongest single argument in this report, stated once.** The figure
freshening law exists as `dev/LESSONS.md` C-32 since 2026-08-11, and its own
measured instance records the orchestrator holding a pre-cure figure and
quoting it three times. On 2026-08-13, two days after C-32 was admitted, the
same orchestrator quoted the pre-seal bar 0.0136 into a brief
(`4a97520`), inherited the wrong direction of a bar (`c96016f`), and left
three false figures in the live status screen (`73d8f22`). **The lesson did
not reach the moment of action. That is the brief's own condition for
needing a skill: an entry covered by LESSONS needs no skill unless it never
reaches the moment.** It did not reach, and the moment is a writing moment
with writable keywords.

## 1. The known seven, verified one by one

Each is real. The evidence is a commit hash or a report line.

1. **A search that excludes what it looks for.** MEASURED. `4d77090`
   ([LJ-1.163]): `grep -rn "ElemDown" src/ | grep -v
   "^src/L/BoundedSubset.lagda.md"` excluded the one file with sixteen hits.
   `819b482` ([LJ-1.183] fix): `status | grep RUNNING` filtered out the
   `!! N RETURN(S) NEVER REPORTED` line. `4f2c541` ([DD17] rename): a
   literal `(override)` count returned five against a true 52.
2. **Editing a file under a running agent.** MEASURED. `dev/JOURNAL.md`
   (2026-08-14, the [LJ-1.187] entry): twice a directory-wide `git add -A`
   swept in a sibling's work, once a tool rewrite landed while another agent
   measured with that tool and lost four figures.
3. **A brief premise that was false.** MEASURED. `0cb9b17` ([LJ-1.177]):
   sent to cure a term [LJ-1.158] had cured five dispatches earlier, whose
   row sits directly below the row the brief cited.
4. **Acting on a figure with no measured basis.** MEASURED. `a6c5581`
   ([LJ-1.168]): the 5,047 lines were never measured. `a01ef58`
   ([LJ-1.173]): the +126 s extrapolation. `5be8195` ([LJ-1.185]): the
   16 s double subtraction.
5. **Fixing only what the search could see, then declaring done.** MEASURED.
   Three times in one hour on 2026-08-14: `819b482` (DD27 in three places,
   fixed one), `bb3907b` (two head names fixed at the top, two left further
   down), `cda4619` (the bar section fixed, three other spots wrong).
6. **Believing the code over the rule it cites.** MEASURED. `323451a`: the
   refusal cited `dev/ORCHESTRATION.md` section 3, which already read the
   brief is pinned in `agents/tasks/<TASK>/`; the orchestrator built a
   workaround in `_build/briefs/` instead of opening the section.
7. **Deriving a standing rule from a one-off owner instruction.** MEASURED.
   `eb9bf0d`: four DD25 reviews to `fable` from one owner naming of fable.
   Now `dev/PLAN.md` DD0 and `dev/LESSONS.md` C-43.

## 2. The finding under the findings

**The seven reduce to one disease.** Each instance is a claim that was not
bound to an artifact. The search result was filtered against a belief
(`4d77090`). The figure was quoted from a note, a plan paragraph or a
memory (`c96016f`, `4a97520`, `73d8f22`). The premise was a verdict cell
read instead of the report (`0e004c7`). The named source was cited without
its hypothesis (`85507b4`). The status field was read instead of the launch
log (`2b95717`).

**The same disease ran in the retired route.** MEASURED.
`archive/dev/JOURNAL-archived.md` [T242] (2026-08-09): four of the
orchestrator's figures corrected, a slice rate quoted as the content rate, a
base stale by 41 s. `archive/dev/TASKS-archived.md:252` ([T248]):
sixteen headline figures in a status memo were wrong. `dev/LESSONS.md` C-31:
a wrong denominator stood in three places at once. `dev/LESSONS.md` C-1
([L3.2], July 2026): a `git add -A` swept a revert into a commit. **An error
that repeats across a route change is the strongest case for a skill, and
the figure and commit shapes repeat across the route change.**

**Why the cures split the way they do.** The four-cure table asks whether
the error is a knowledge gap, a mechanical act, an undecided question, or a
measured law. For this disease the answer depends on the MOMENT:
- At the WRITE moment, the model writes the claim. Its own words are the
  trigger, and a skill carries the rule to that moment. That is P1 and P2.
- At the mechanical edges, a gate can see the act. That is P3 and P4.
- The rest is attention. That is section 8.

The other three cures are worse for each proposal, and each row says why.

## 3. The ranked table

Ranked by what the error cost. Costs are the record's own words, quoted or
summarized at the evidence. Each row names the cure and why the other three
are worse.

| # | error | occurrences | cost | cure | why the other three are worse |
|---|---|---|---|---|---|
| E1 | a brief premise that was false | 12 self-admitted, 2026-08-13/14 | three or more dispatches spent on false premises | P1, SKILL | a checker cannot see intent in a premise; a DD ruling was never needed, the rule exists; a lesson exists and did not reach the moment |
| E2 | a figure with no measured basis, or re-quoted stale | 10 new-route: 5,047, the +126 s, the 16 s, the 455, the 0.0136 bar, the 11 percent direction, the 1.91x screen, the T261 "queued", the minted DD27 bar, the struck question in the screen. Plus the retired route's T242 and T248 | a factor-14 misprice; a stage funded on a phantom; a wrong gap shipped | P1, SKILL | C-32 exists and did not reach the moment; a checker cannot judge a figure's freshness; the owner need not rule that figures carry provenance |
| E3 | a search that excludes its target | at least ten self-admitted episodes across eight commits, 2026-08-13/14 | three dispatches priced a held term; two findings hidden twice | P1, SKILL | the act is not mechanical, an ad hoc grep has no gate; no ruling needed; C-42's converse was deliberately not numbered |
| E4 | fix only what the search saw | three in one hour | struck rulings stayed live in briefs and a rulebook | P1, SKILL | the sweep is a habit, not a mechanical act; the number half is P4's checker; the prose half has no gate |
| E5 | commit or rewrite under a running agent | five, plus the retired route's C-1 | four figures lost once; sibling work swept twice | P3, CHECKER for the git-add half; NONE for the tool-rewrite half | the git-add act is mechanical and a gate can see it; a skill can be skipped; the tool-rewrite half is attention |
| E6 | a proxy read as the outcome | six | a finished task declared dead; four days of a false plan claim | P2, SKILL | the outcome is a judgment, not mechanical; no ruling needed; the lesson exists in the dispatch skill and the shape outruns dispatch |
| E7 | believing the code over the rule it cites | one | one workaround, since removed | already in the dispatch-herdr skill, mistake 6 | covered; no new cure |
| E8 | a one-off owner instruction made standing | one episode, four dispatches | four wrong-head reviews | already `dev/PLAN.md` DD0, `dev/LESSONS.md` C-43, the dispatch-herdr skill | covered; no new cure |
| E9 | a duplicate DD number | one | three briefs carried a struck bar | P4, CHECKER | uniqueness is mechanical and `check-rule-ids.py` already cannot see it; the orchestrator's own commit says it is worth a checker |

## 4. P1: the load-bearing-claim skill

**The proposal.** One skill, named for the WRITE moment. Its description
fires when the model is about to write a claim into a brief, a plan, a
status screen, a commit body, or a checker. Its body holds the rules this
report measured, each with its episode:

1. **A claim written as MEASURED names the search that established it, and
   the search's filter.** `4d77090` wrote "MEASURED: nothing in src/
   supplies it" on a grep whose filter excluded the answer file. The
   misses then named themselves in a pattern: `ac30ff1` (three closure
   classes proved at `src/L/Choice/Name.lagda.md:120-135`, no brief cited
   it), `ba88df4` (the preceding dispatch's own green probe), `c45a257`
   (four misses, all mine, two in the same file), `8736fdb` (the
   Axioms/Separation blind spot), and the LJ-1.170 brief named
   `src/L/Choice/` paying a fourth time. A rule: a load-bearing negative
   names its command, and a filter that removes a candidate file is named
   in the record.
2. **A figure written into any document traces to the report row that
   measured it, at file:line.** The 5,047 (`a6c5581`), the 16 s
   (`5be8195`), the 0.0136 bar (`4a97520`), the 1.91x screen (`73d8f22`),
   the 455 (`cfe2b5a`), the T261 "queued, never ran" (`4a12cac`). A figure
   from a plan paragraph, a note, a status screen, or a memory is a
   hypothesis, never a price (P-l).
3. **A source named in a brief is a claim: you have opened it and read the
   part that bears.** `85507b4` named an archived lemma as a delivered
   comparable; it took the satisfaction relation as a hypothesis. `de353ef`
   named `LevelKit:562` on the word "coverage"; it was a word coincidence.
   `bba3070` named a certificate that was not the one the consumer uses.
4. **Sweep by SHAPE, then sweep the record for the same shape, before
   declaring done.** C-42 is the law. `819b482` fixed one of three DD27
   sites and called the brief clean. `bb3907b` fixed the top of
   `dev/ORCHESTRATION.md` and left the bottom. `cda4619` fixed the bar
   section and left three spots.
5. **A brief's premise is the thing the dispatch tests.** The false-premise
   list in E1 is the evidence. A premise that came from a memory, a verdict
   cell, or a prior brief is a false-premise candidate until the report row
   it rests on is named.

**The trigger.** The description carries the model's own words at the
write moment: `verify, verified, MEASURED, measured, counted, grep, search,
census, sweep, filter, nothing in, absent, no consumer, no supplier, the
bar, priced at, costs, lines, seconds, rate, stands at, reads, quoted,
figure, comparable, premise, basis, fixed, clean, done, zero references`.

**The sharp question, answered honestly.** Would it have LOADED at the
moment of each error? At `4d77090` the model typed `grep`. At `4a97520`
it wrote "the bar is 0.0136". At `73d8f22` it wrote "DD24 reads 1.91x". At
`819b482` it wrote "the brief carries zero references". At `85507b4` it
wrote "ARM A's delivered comparable". In every one, the trigger word is in
the model's own text at the moment of acting, because the error IS the
writing. The brief's caution is right that a skill named "searching" would
not have loaded, because the model thought it was verifying. **So this
skill is named for the VERIFY and WRITE moments, not the search moment, and
its description leads with `verify, MEASURED, the bar, priced at`.**
INFERRED: the load itself is not observable until the skill exists.

**Why the other three cures are worse.** A checker cannot see intent in a
premise or judge a figure's freshness. A DD ruling was never needed: the
rules exist, in DD8, C-32, C-42, P-l. A lesson exists for the figure half
(C-32) and its own instance shows it did not reach the moment, which is the
brief's stated condition for a skill. A skill is the only one of the four
that puts the rule into the model's context at the moment of writing.

**DD4.** The skill is generic. It serves any task kind, because every kind
writes claims and figures. It serves any head and either dispatch mode,
because it is about the orchestrator's own writing, not about a tool path.

## 5. P2: the artifact-over-proxy skill

**The proposal.** One skill, named for the OUTCOME-reading moment. Its
description fires when the model is about to record an outcome from a
proxy: a status table, a verdict cell, a header, a note, a machine-load
number. Its body holds the rules:

1. **The artifact is the evidence; the status field is a hint.**
   `2b95717` recorded [LJ-1.187] as DIED because the status table said so;
   the report was on disk. That commit calls it the third time in one
   session.
2. **A header is not a report.** `4a12cac`: [LJ-0.3]'s closeout read
   T261's brief header, which says "Queued for an Agda slot", instead of
   its report, and the plan asserted it never ran for four days.
3. **"Quiet" means measured load, never an absence of siblings.**
   `21446f2`: no agent was running and the machine was not quiet.
4. **A verdict cell is not the report, and a count is not a price.**
   `0e004c7`: [LJ-1.175] read [LJ-1.156]'s count as its price.
5. **A row is not the row below it.** `0cb9b17`: [LJ-1.177] read [LJ-1.155]'s
   row and not [LJ-1.158]'s, which sat directly below it.
6. **A no-op that prints success is not success.** `bd64fba`:
   `check-probes.py --archive` no-op'd and printed "clean", which is how
   the orchestrator came to believe an archive had happened.

**The trigger.** `status, recorded, reported, DIED, RUNNING, FAILED,
CLEAN, the table says, the row says, the cell says, the note says, header,
verdict, quiet machine, no agent running`.

**The sharp question.** At `2b95717` the model wrote "the status table said
so": the trigger is present. At `21446f2` it wrote "I checked that no AGENT
was running and called that quiet": "quiet" is present. At `4a12cac` it
read a header: "header" is present. The rule is one sentence, and the
dispatch-herdr skill already holds the dispatch half ("read the launch log,
not the status table"). **This skill is that rule generalized beyond
dispatch, and I say plainly that it is the most attention-adjacent of the
four proposals: it raises the rule at the moment, it cannot open the file
for the model.**

**Why the other three are worse.** The outcome is a judgment, not a
mechanical act, so no gate can see it. No ruling is needed: the rule is
already stated. A lesson exists only in the dispatch skill and the shape
outruns dispatch. If the owner judges this one too thin, cut it: the
dispatch half is already covered, and the remaining instances are the
smallest costs in this report.

## 6. P3: the commit gate against the live-agent registry

**The proposal.** A pre-commit check, shaped like `check-probes.py
--staged`, that reads the dispatch registry
(`.claude/skills/codex-dispatch/.state/registry.json`) and refuses a staged
file whose path lies inside a live agent's write territory: its task
directory `agents/tasks/<CODE>/`, or the write scope its brief declares.
The registry records live agents and their brief paths, MEASURED at
`registry.json`. `dispatch.py` already computes write-scope intersections
for its own refusals, so the logic exists. Feasibility: INFERRED, I did not
build it.

**What it catches.** The two `git add -A` sweeps on 2026-08-13
(`dev/JOURNAL.md` [LJ-1.187] entry, `93b224e`, `a37e3fd`) and the retired
route's C-1 ([L3.2], July 2026). A staged file inside a live agent's task
directory is mechanical, visible, and a gate cannot be skipped.

**Why a checker and not the other three.** The act is mechanical: a
directory-wide add of a live agent's in-flight file. A gate can see it. A
skill can be forgotten, and C-1 existed for a month before the new route
repeated the shape. A ruling and a lesson exist (C-1) and did not reach the
moment; the gate does not depend on reaching.

**What it cannot catch, said plainly.** The tool-rewrite-under-a-measuring-
agent instance: the measuring agent reads the tool and never writes it, so
no commit-time gate knows. That instance has no mechanical cure and sits in
section 8.

## 7. P4: the DD number-uniqueness check

**The proposal.** Extend `scripts/check-rule-ids.py` to refuse a code that
appears in more than one row of its series. The plan's own preamble says a
number is never reused in either series. `cda4619` minted a duplicate DD27
and the checker reported CLEAN through the episode, because it verifies
resolution and never uniqueness. The commit itself says: "It is the same
blind spot C-41 records one level down, and it is worth a checker:
uniqueness is mechanical in a way intent is not." This is the
orchestrator's own suggestion, and this report adopts it.

**Why a checker.** Uniqueness is mechanical. A skill cannot be trusted to
check every row, and a rule already exists. Cost: three briefs carried the
wrong bar until the strike landed (`cda4619`), and the strike's own fix
missed three residual sites (E4).

## 8. Errors with NO cure

**These are named honestly. A skill nobody loads costs more than nothing,
because it makes the problem look solved.**

1. **Reading the wrong part of the right artifact.** `85507b4` opened the
   archived lemma and read its conclusion, not its hypothesis. `8f55b4b`
   read the first lines of a function and inferred the rest. The model
   reached the artifact and misread it. No document prevents misreading;
   P1's rule 3 raises the habit, and the specific miss stays attention.
   MEASURED, and the cure is none.
2. **Landing a tool change while an agent measures with that tool.**
   `dev/JOURNAL.md` [LJ-1.187] entry: it lost four figures. No gate can
   know what a live agent reads. The habit rule is already recorded there:
   "land a tool change only when no agent holds it." A skill would not have
   loaded: the moment is an edit, and the edit itself is legitimate work.
   MEASURED, and the cure is none beyond the recorded habit.
3. **The general attention failure behind E6's weakest cases.** A proxy
   that looks like an outcome, a figure that looks fresh, a premise that
   looks checked. The two skills carry the rules; the residual failure to
   open the file is attention. I mark this INFERRED: it is the residue
   after the rules exist, and it cannot be measured before the rules do.

## 9. What I swept and how

**Method.** I read every commit body from 2026-08-13 to HEAD, 111 commits
(`git log --since=2026-08-13`), whole. I swept the bodies for each shape
by its mechanism, never by one spelling: search-and-filter, figure-and-
provenance, proxy-and-outcome, premise-and-brief, commit-and-agent, fix-
and-declare-done, code-vs-rule, one-off-vs-standing, duplicate-number.

**The verification sweep, one pass per known item.** Item 1: every
"grep", "search", "miss", "filter" admission in the bodies. Item 2: every
"git add", "sibling", "under a running agent", "held the edit" admission.
Item 3: every "premise ... false", "corrections to my brief", "my lead was
wrong" admission. Item 4: every "figure", "never measured", "withdrawn",
"never existed" admission. Item 5: every "fixed ... clean", "zero
references", "left the two further down" admission. Item 6 and 7: the two
episodes by name.

**The archive sweep.** `archive/dev/JOURNAL-archived.md` at grep depth
over admission language, then the windows the hits named. `TASKS-archived.md`
for the T242 and T248 rows. `dev/LESSONS.md` C-1, C-31, C-32 for the
retired-route instances of the same shapes.

**The rule sweep.** `python3 scripts/rules.py --for recon` read whole.
Every rule the brief mandates, read at its home: DD0, D-10, D-26, D-29,
D-30, C-22, C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40, C-42, C-43,
P-l, I-5.

**The occurrence counts are MEASURED** where a commit or a report states
them ("sixth search miss of this shape", "the fourth instance today"), and
MEASURED where my sweep counted distinct self-admissions at distinct
commits. Nothing is counted by a spelling search alone. **The shapes
overlap, and the table rows are not disjoint**: one episode can be
self-admitted in more than one shape, and the brief's six false-premise
instances are a subset of the twelve counted, which include the wrong
attribution to the owner at `21446f2` and the wrong archive pointer at
`85507b4`. The sum of the rows therefore overcounts episodes, and each
row's count is the number of distinct self-admissions of that shape, not
the number of unique episodes.

## 10. DD4

The two skills are generic. They bind any task kind, any head, and either
dispatch mode, because the moments they serve, the write and the outcome
read, are the orchestrator's own in every dispatch. They are the shared
carrier; the episodes are the per-case instances. The two checkers are
mechanical and head-independent. Nothing in this proposal is written for
the case that bit one week.

## ARCHIVE USED (DD18)

- `.claude/skills/dispatch-herdr/SKILL.md`, read whole. Took the model of a
  good skill: the description as the trigger, the MEASURED/INFERRED/
  UNMEASURED marking, the mistake-and-rule pairs. Took the two rules this
  report generalizes: mistake 2 (the launch log, not the status table) and
  mistake 6 (when a tool and the rule it cites disagree, open the rule).
- `.claude/skills/asd-ste100/SKILL.md` and `.claude/skills/codex-dispatch/
  SKILL.md` frontmatter: the description shape.
- `agents/tasks/LJ-1-183/lj-1.183-report.md`, read whole. Took F1, F3, F5
  and the method of the DD4 census.
- `agents/tasks/LJ-1-157/lj-1.157-report.md`, read whole. Took the CSB
  chain finding: a returned fact does not persist unless the orchestrator
  re-injects it.
- `agents/tasks/LJ-1-188/lj-1.188-report.md`, read whole. Took the
  ten-mistake list and the model-flag measurement.
- `dev/JOURNAL.md` 2026-08-14 entries ([LJ-1.186], [LJ-1.187]): the DD
  remainders, the three-times habit, the artifact-is-the-evidence line.
- `dev/LESSONS.md` C-1, C-31, C-32, C-33, C-39 to C-43, D-29, D-30, C-36,
  C-37, I-5: the existing laws this report's proposals must not restate.
- `archive/dev/JOURNAL-archived.md` at grep depth, plus the [T242] window
  (lines 3485-3499): the retired route's figure corrections.
- `archive/dev/TASKS-archived.md:181,223,249,252`: the T146 band, T219,
  T245, and the T248 sixteen-figure status memo.
- `archive/dev/DECISIONS-archived.md` not opened; the retired rulings it
  holds do not bear on skill-vs-checker classification.
- `git log --since=2026-08-13`, 111 commit bodies read whole, hashes cited
  throughout: the primary corpus.
- `.claude/skills/codex-dispatch/.state/registry.json`: the live-agent
  records for P3's feasibility. `.claude/skills/codex-dispatch/dispatch.py`
  not re-read whole; `dispatch.py`'s write-scope logic was taken from the
  dispatch-herdr skill's refusals table and LJ-1.188's report.

## LITERATURE (DD18)

Not this task's subject. Nothing in `dev/literature/` bears on which
recurring orchestrator errors a skill would prevent; DD18 is satisfied by
this one honest line.
