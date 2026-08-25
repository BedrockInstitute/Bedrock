# LJ-1.617: does the bill ever need the pairing at module grain

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-617/Probe617.agda`:

    site-grain-suffices : <the bill's demand on ingredient (iii), stated at the
                           SITE the tree actually spends it, and shown to
                           suffice for everything downstream>

**or the term that shows the module-grain product is genuinely demanded.** Land
nothing in `src/`.

**I AM ATTACKING THE DEMAND AND NOT THE WALL, AND THIS IS MY JUDGEMENT.**
`[LJ-1.607]` proved a circle as a term and named a NEW OBJECT to build if anyone
wants to attack it. **I am not funding that object yet, because I think the
circle may rest on a demand nobody makes.**

**THE MEASUREMENT THAT MADE ME THINK SO, AND IT IS THREE GREPS.**

- `L.StageCardinal` is instantiated in **exactly one place** in the whole tree:
  `src/L/BoundedSubset.lagda.md:1397`, `module SC = L.StageCardinal {ℓ} lem α ordα sq`.
- At that site `sq` is **a Π-bound PARAMETER of the enclosing module**, at
  `src/L/BoundedSubset.lagda.md:1388`, sitting beside `absorbs` (`:1392`).
- It is spent at `:1410` as `sq α (self∈sucV α) α∉ω`: **at ONE α.**

**`[LJ-1.604]` PRICED (iii) AT TWO GRAINS AND THE CIRCLE USES THE WIDER ONE.**
At one site it is "one binary function with its injectivity" and **the smallest
of that site's five**; at module grain it is "the product over every infinite
ordinal of the band". `[LJ-1.605]` and `[LJ-1.607]` then measured the wider
thing. **Nothing I can find demands the wider thing.**

**THE SAME MOVE ALREADY WORKED ONCE ON THIS BILL.** `[LJ-1.588]` asked whether
`gch-from-five` ever needs row 4 WIDE, and the answer was no: the restricted row
suffices and no row grew. `[LJ-1.585]` gave the principle: **"the hypothesis
cannot be stated more widely than the function it is about."**

**I HAVE BEEN WRONG ABOUT THIS SHAPE THREE TIMES THIS WEEK** (`[LJ-1.580]`,
`[LJ-1.585]`, `[LJ-1.604]` each refuted a reading of mine). **Measure it. Do not
agree with me.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-617/Probe617.agda::site-grain-suffices"]

## SCOPE (write)
- agents/tasks/LJ-1-617/Probe617.agda
- agents/tasks/LJ-1-617/lj-1.617-report.md
- agents/tasks/LJ-1-617/review-of-site-grain.md
- agents/tasks/LJ-1-617/runs/

## PREMISES

1. `L.StageCardinal` is instantiated at one site. Basis: src/L/BoundedSubset.lagda.md:1397
2. `sq` is a Π-bound parameter there. Basis: src/L/BoundedSubset.lagda.md:1388
3. It is spent at one α. Basis: src/L/BoundedSubset.lagda.md:1410
4. `absorbs` is a sibling parameter. Basis: src/L/BoundedSubset.lagda.md:1392
5. `[LJ-1.604]` priced (iii) at two grains. Basis: agents/tasks/LJ-1-604/lj-1.604-report.md:1
6. `[LJ-1.605]` measured the wider grain and stopped. Basis: agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90
7. `[LJ-1.607]` confirmed the circle as a term. Basis: agents/tasks/LJ-1-607/lj-1.607-report.md:173
8. `[LJ-1.588]` found the restricted row 4 suffices. Basis: agents/tasks/LJ-1-588/Probe588.agda:424
9. `[LJ-1.585]` gave the width principle. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
10. `[LJ-1.613]` paid ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Four of `class-pred`'s five ingredients, and a circle measured at the module
grain of the fifth. **Nobody has asked which grain the bill spends.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SPEND SITES.** Grep the tree for every
use of `sq` and of `SqParam`, and say at `file:line` **every place the bill
actually consumes the pairing, and at what α.** Report the count.
**Never conclude a count from a command containing `head`.**

**THEN ASK WHETHER ANY CONSUMER NEEDS IT AT MORE THAN ITS OWN α.** If one does,
name it and the circle stands: **say so plainly and this task is a NO-GO that
saves the campaign a wasted attack.**

**DO NOT BUILD A PAIRING.** `[LJ-1.618]` has the site-level build. **This brief
is about the DEMAND and nothing else.**

**DO NOT RE-MEASURE THE CIRCLE.** `[LJ-1.607]` proved it as a term at the module
grain and I do not dispute that. **The question is whether the module grain is
the grain the bill pays in.**

**IF I AM WRONG, SAY SO IN THOSE WORDS.** Three of my readings have been refuted
by measurement this week and each refutation was worth more than the guess.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## EVERY SPEND SITE`.** Each at `file:line`, with the
α it spends at, and a count you measured.

**REQUIRED REPORT SECTION `## WHICH GRAIN THE BILL PAYS IN`.** One paragraph.
**Say whether the circle binds what the bill actually needs**, and do not read a
discharge into anything you did not inhabit.

ESTIMATE: about 140 lines in the probe, of which the obligation is about 35.
BASIS: `[LJ-1.588]` did the same shape of question on row 4 at a comparable
size. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the count of spend sites.

    -- every consumer of sq and SqParam in src/ and in the live probes,
    -- listed at file:line with its α

**Do this FIRST, by grep, and report the count before writing any Agda.**
ESTIMATE: two greps and about 10 lines, capped at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO DISSOLVES A CIRCLE THAT FIVE DISPATCHES ENTERED**, without attacking it,
and reduces ingredient (iii) to "one binary function with its injectivity",
which its own pricer called the smallest of the five.

**A NO-GO NAMING A CONSUMER THAT NEEDS THE BAND SAVES A WASTED ATTACK** and
tells the mathematician the new object is the only way, which is a ruling worth
having before it is funded.

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-617/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-617/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-617/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-617/Probe617.agda"]
  changed_files_none = ["agents/tasks/LJ-1-617/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-617/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

**THE RATIO BAR IS LIVE AND IT IS 0.0123 SECONDS PER IN-FENCE LINE.** A green return at or above that rate is ESCALATED to a critic by row `sys-dd24-ratio-bar`, which is DD24 restored by amendment A10. The divisor is fact 7, the in-fence line count of THIS task's write scope, counted the ledger's way: non-blank lines inside ` ```agda ` fences. **A raw `.agda` probe carries no fence and counts 0**, so the bar cannot fire on a probe and it binds the moment you write a `.lagda.md` master under `src/`. Design for it rather than discovering it: the number comes from `dev/pod/table.toml` at brief build, and its measured basis is in `dev/ledger.toml [ratio]`.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 195.229)
- CANDIDATE archive/dev/JOURNAL.md  (score 193.753)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 180.882)
- CANDIDATE archive/dev/DD-archived.md  (score 167.626)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 160.273)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 75.349)
- CANDIDATE dev/literature/devlin-II5.md  (score 61.143)
- CANDIDATE dev/literature/digest.md  (score 44.389)
- CANDIDATE dev/literature/geology.md  (score 42.346)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.301)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
