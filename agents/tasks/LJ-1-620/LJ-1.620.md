# LJ-1.620: where do the four paid ingredients live, a question I never asked

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-620/Probe620.agda`:

    landing-survey : <for each of the four PAID `class-pred` ingredients, the
                      chapter of `src/` that could host it, stated as a term
                      naming the module and the import edge it would add>

**or, for any that cannot be hosted, the term naming what blocks it.** Land
nothing in `src/`. **This brief SURVEYS the landing, it does not perform one.**

**THIS TASK EXISTS BECAUSE OF A COUNT I TOOK OF MY OWN WORK AND DID NOT LIKE.**
Of the 126 briefs I have written this campaign, **94 say "Land nothing in
`src/`"**, 4 carry `machine: exclusive`, and 4 name a `src/` path in scope.
**122 tasks were structurally unable to land anything, because I forbade it in
the brief.** That is not a fact about the mathematics.

**FOUR INGREDIENTS ARE PAID AND ALL FOUR ARE IN PROBES.**

| ingredient | paid by | lives at |
|---|---|---|
| (i) | `[LJ-1.613]` | `agents/tasks/LJ-1-613/Probe613.agda:137-154` |
| (ii) | `[LJ-1.613]` | `agents/tasks/LJ-1-613/Probe613.agda:180-192` |
| (iv) | `[LJ-1.601]` + `[LJ-1.608]` | their probes |
| (v) `keyS` | `[LJ-1.600]` | its probe |

**NOBODY HAS ASKED, OF ANY OF THEM, WHERE IT WOULD LIVE.** I never wrote the
question into a brief. **A term in a probe is not in the build, is not checked
by `make check`, and no chapter can use it.**

**AND THE ONE TIME SOMEBODY DID ASK, THE ANSWER WAS SURPRISING AND CHEAP.**
`[LJ-1.555]` read the import graph over the tree's **102 masters** and found
that **no existing master could host `CardAboveL` without a new import edge**,
because `L.BoundedSubset` already imports and instantiates `L.StageCardinal`.
**That measurement cost one task and it changed the answer completely.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-620/Probe620.agda::landing-survey"]

## SCOPE (write)
- agents/tasks/LJ-1-620/Probe620.agda
- agents/tasks/LJ-1-620/lj-1.620-report.md
- agents/tasks/LJ-1-620/review-of-landing-survey.md
- agents/tasks/LJ-1-620/runs/

## PREMISES

1. `[LJ-1.613]` is GO and paid ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
2. `[LJ-1.600]` is GO and paid (v). Basis: agents/tasks/LJ-1-600/lj-1.600-report.md:1
3. `[LJ-1.601]` is GO and paid (iv)'s base. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
4. `[LJ-1.608]` is GO and paid (iv)'s limit. Basis: agents/tasks/LJ-1-608/lj-1.608-report.md:1
5. `[LJ-1.555]` read the import graph over 102 masters. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56
6. It found no existing master could host the term. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:81
7. `L.BoundedSubset` imports `L.StageCardinal`. Basis: src/L/BoundedSubset.lagda.md:882
8. `src/Everything.lagda.md` is the aggregator. Basis: src/Everything.lagda.md:389
9. `[LJ-1.594]` states the five ingredients. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138
10. No mathematical prose is written until both trophies are proved. Basis: AGENTS.md:69
11. The program commits by explicit path from the task's scope. Basis: AGENTS.md:78
12. Chapter style is ruled. Basis: dev/STYLE-agda.md:1
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Four paid ingredients, all in probes, and one import-graph measurement made for
a different term.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE GRAPH.** Read the `import` lines of the
masters under `src/` and, for each of the four ingredients, say at `file:line`
**which chapter could host it and what import edge that would add.** Report the
count of masters you read. **Never conclude a count from a command containing
`head`.**

**A "NEW MASTER" ANSWER IS A REAL ANSWER AND NOT A FAILURE.** `[LJ-1.555]`
reached exactly that for `CardAboveL`. **If an ingredient needs a new chapter,
name the chapter and say what it would import.**

**SAY WHICH OF THE FOUR IS CHEAPEST TO LAND AND WHY.** That is the deliverable
the mathematician most needs: **one name, so the next brief can carry
`machine: exclusive` and a `src/` path instead of "Land nothing".**

**DO NOT LAND ANYTHING AND DO NOT RUN `make check`.** Two landing attempts have
heap-walled silently in under twenty seconds and `[LJ-1.619]` is measuring why.
**This brief must not step into that.**

**IF AN INGREDIENT CANNOT BE HOSTED AT ALL, SAY SO AND NAME WHAT BLOCKS IT.**
An import cycle is the expected shape, and it is what stopped `[LJ-1.555]`.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP**, and report
peak RSS: this family has walled twice.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## FOUR INGREDIENTS, FOUR HOMES`.** One row each:
chapter, import edge added, or the blocker.

**REQUIRED REPORT SECTION `## THE CHEAPEST ONE`.** Name it, say why, and say
what a brief landing it would have to carry. **That sentence is what the next
brief will be written from.**

ESTIMATE: about 120 lines in the probe, of which the obligation is about 30, and
most of the work is reading rather than proving. BASIS: `[LJ-1.555]` did the
same reading for one term. Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is the import closure of ingredient (v), the smallest of the four.

    -- keyS's dependencies, listed by module, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** If even the smallest has a
closure like `CardAboveL`'s, say so at once: that would answer the whole survey
in one rung. ESTIMATE: about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CAMPAIGN ITS FIRST LANDING TARGET CHOSEN BY MEASUREMENT**
rather than by my guess, and the last two guesses were both wrong.

**A NO-GO SHOWING NONE OF THE FOUR CAN BE HOSTED IS EQUALLY USEFUL**, because it
would mean the probes are the only home available today and the campaign must
say so plainly to the owner instead of promising landings.

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
  changed_files_none = ["agents/tasks/LJ-1-620/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-620/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-620/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-620/Probe620.agda"]
  changed_files_none = ["agents/tasks/LJ-1-620/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-620/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 222.359)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 219.758)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 204.915)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 202.129)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 199.384)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 60.642)
- CANDIDATE dev/literature/digest.md  (score 46.914)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.056)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 37.085)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.601)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
