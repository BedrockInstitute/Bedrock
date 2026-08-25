# LJ-1.405: how far does the least-code device reach? The C-42 sweep

**THIS IS A REQUEST AND NOT A DISPATCHABLE BRIEF, AND THE REASON IS MECHANICAL.**
Pre-flight P14 refuses a brief whose `obligations` list is empty
(`scripts/pod/preflight.py:489-490`), and this task writes no Agda, so it has no
`<probe path>::<name>` to list. Its queue entry therefore carries NO `brief` key:
rule (a1) skips it and the digest prints it. **The specification below is
complete and is kept so that the work is not lost.** What it needs is either a
recon obligation form the witness meter can read, or an owner's ruling that a
reading task may carry an empty list. The refill of 2026-08-20 reported both.

## HEAD
head_slot: mathematician
machine: shared

## THE OBLIGATION

Write `agents/tasks/LJ-1-405/lj-1.405-report.md` and nothing else. **It carries a
COUNT, not an opinion.**

Sweep `src/` for the shape below and report how many sites carry it, each at
`file:line`, with a one-line verdict for each:

> a TRUNCATED existential whose carrier is well-ordered by `orderAt` (or by any
> `SWO` the site already holds), and whose predicate is, or can be made, an
> hProp WITHOUT truncating the payload.

**At every site say which of three it is:**

1. **REACHED.** The payload is already propositional, so `leastOf` returns it as
   data and the truncation was never necessary.
2. **BLOCKED.** The payload is genuinely not a proposition, so the truncation is
   load-bearing and no device removes it.
3. **UNMEASURED.** You cannot tell from reading, and it needs a probe. Name the
   probe and the term it would build. **You do not write it.**

## OBLIGATION NAMES

None. This task writes no Agda and closes no proof obligation. The witness meter
reads an empty obligation list and returns the vacuous pass.

## SCOPE (write)
- agents/tasks/LJ-1-405/lj-1.405-report.md

## PREMISES
- `leastOf` returns data from a truncated non-emptiness whenever the predicate is hProp-valued. Basis: src/L/WellOrder/Base.lagda.md:158-160
- `IsLeast` is a proposition, which is why the selection is unique and the device is sound. Basis: src/L/WellOrder/Base.lagda.md:130-134
- **SITE A, THE AMBIENT ONE, IS BLOCKED AND THE CHAPTER SAYS SO IN ITS OWN COMMENT.** The payload is an injection, which is not a proposition, so it had to be truncated to enter the device. Basis: src/L/Cardinal.lagda.md:132
- and the truncated arrow that results is what every recent task could not pay. Basis: src/L/Cardinal.lagda.md:133-134
- **SITE B, THE CODED ONE, LOOKS REACHED.** Its predicate is truncated only because it quantifies a code existential, and the four conjuncts under it are each propositional by construction. Basis: src/L/Cardinal.lagda.md:240
- and the code existential it yields is exactly `leastOf`'s input shape. Basis: src/L/Cardinal.lagda.md:257
- `InjCode`'s four conjuncts, the object whose propositionality decides site B. Basis: src/L/Cardinal.lagda.md:223-228
- `leastOf` is used at the ambient selection too, and that use is site A's own. Basis: src/L/Cardinal.lagda.md:117

## WHAT IS DELIVERED ALREADY

Two uses of `leastOf` in `src/L/Cardinal.lagda.md`, at `:117` and `:247`. The
sweep starts from them and does not stop at them.

## WHAT IS MISSING

The count. `[LJ-1.401]` to `[LJ-1.403]` measure ONE site. **A measured cure does
not transfer by analogy** and C-42 says a measurement at one site says nothing
about how many other sites carry the shape. Nobody has counted.

## THE REASONING

**THIS TASK EXISTS BECAUSE THE CURE AND THE REFUTATION LOOK IDENTICAL FROM A
DISTANCE.** At site A the truncation is necessary and at site B it may not be,
and the two sit forty lines apart in one chapter. A campaign that learns「the
truncation was avoidable」without a count will try the device at site A and lose
a dispatch, or will leave a free untruncation standing somewhere else for weeks.

**HOW TO SWEEP, AND THE FILTER IS PART OF THE RESULT.** Search for `leastOf`,
for `∥`, for `squash₁` and for `PT.rec` over `src/`. **State your search commands
and their raw hit counts in the report before you triage**, because a sweep whose
filter is invisible cannot be checked and a hit that was dropped silently is a
hit that was never reported. Then triage each hit into the three buckets above.

**WHAT MAKES A SITE `REACHED`, PRECISELY.** Not「the payload feels
propositional」. A site is REACHED only when you can name, at `file:line`, why
each conjunct of its payload is an hProp: a `⟨ _ ⟩` of an hProp carries its own
`snd`; a Π into an hProp is one by `isPropΠ`; a product of them is one by
`isProp×`. **If you cannot name the reason at `file:line`, the site is
UNMEASURED, not REACHED.** Writing REACHED without that naming is the failure
this task is built to avoid.

**YOU WRITE NO AGDA.** Not a deliverable and not a probe (A21). Where a site
needs a probe, name the probe and the term, and the next brief hands it to a
coder.

**DO NOT RE-DERIVE `[LJ-1.401]`'s ANSWER.** Whether `InjCode` is a proposition is
that task's obligation. If it has returned, cite its verdict; if it has not,
treat site B as UNMEASURED and say so. **Never assert its result to make your own
count come out.**

## WHAT GO AND NO-GO EACH EARN

**A COUNT OF ONE IS A FULL RESULT AND IT IS THE LIKELY ONE.** It says the device
buys exactly the arrow `[LJ-1.402]` builds and nothing else, and it stops the
campaign from spending dispatches looking for a second free untruncation.

**A COUNT ABOVE ONE IS WORTH MORE THAN THIS TASK COSTS**, and each extra site
becomes a queued task with its own price.

**AN HONEST `UNMEASURED` AT EVERY SITE IS ALSO A RESULT**, provided each carries
the probe that would settle it.

## BRANCHES
```toml pod-branches
[[branch]]
id = "counted"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = 0

[[branch]]
id = "blocked"
priority = 15
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 0

[[branch]]
id = "attacked"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
```

## YOUR ROLE (program-generated, do not edit)

**You read and you judge; you write no Agda (A21).** The coder builds what a brief names. Your deliverable is the reading, the count and the record, and your report is what the next brief is written from.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md  (score 43.880)
- CANDIDATE archive/src/2026-08-09-rud-route/L/WellOrder  (score 38.221)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 34.005)
- CANDIDATE archive/dev/TASKS-archived.md  (score 29.118)
- CANDIDATE dev/ARCHIVE.md  (score 24.660)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 70.334)
- CANDIDATE dev/literature/devlin-II5.md  (score 21.007)
- CANDIDATE dev/literature/terms-2026-08.md  (score 18.442)
- CANDIDATE dev/literature/digest.md  (score 16.220)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
