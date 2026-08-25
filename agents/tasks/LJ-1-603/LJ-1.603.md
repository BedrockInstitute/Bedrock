# LJ-1.603: ingredient (iv) at the infinite member stages, the half LJ-1.601 left

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-603/Probe603.agda`:

    rec-graph-at-infinite : <the graph of ingredient (iv)'s recursion at an
                             INFINITE member stage, as a `Formula`, both
                             directions>

Land nothing in `src/`. **The `ω`-base is done and is not yours.**

**`[LJ-1.601]` IS GO AND IT NARROWED THIS INGREDIENT TO ONE HALF.** It measured
the question `[LJ-1.597]` left unmeasured and the answer was positive: **the
finite base HAS a formula**, given by the table term in its `Probe601.agda`
section 2. Its own words on what that leaves:

> "Ingredient (iv) of `[LJ-1.594]`'s table is thereby re-priced downward at its
> base only: the `ω`-base no longer blocks, so **what remains unmeasured in (iv)
> is the recursion at infinite member stages**, and ingredients (iii), the
> pairing, and (v), the coded copy, are untouched by this task."

**SO THIS BRIEF IS EXACTLY THAT REMAINDER AND NOTHING ELSE.**

**THE SHAPE IS FIXED AND YOU SHOULD REUSE IT, NOT INVENT ONE.** `[LJ-1.601]`
worked in `[LJ-1.597]`'s `Graph` shape (`agents/tasks/LJ-1-597/Probe597.agda:269`):
a `Formula S 2`, value variable first and index variable second, both
directions. **Use the same shape** so the two halves compose without a
respelling, which R-42 (`dev/LESSONS.md`) measures as the expensive move.

**THE CHAPTER'S CONDITION IS THE GRAPH ALONE.** `src/L/Recursion.lagda.md` is
titled "Recursive definitions are internalizable" and its condition names
nothing about the recursion's shape, depth or order of descent (`:259-261`).
**`[LJ-1.596]` tried that chapter at the whole object and returned NO-GO. This
brief aims it at ONE half of ONE ingredient**, which is not the same target.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-603/Probe603.agda::rec-graph-at-infinite"]

## SCOPE (write)
- agents/tasks/LJ-1-603/Probe603.agda
- agents/tasks/LJ-1-603/lj-1.603-report.md
- agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md
- agents/tasks/LJ-1-603/runs/

## PREMISES

1. `[LJ-1.601]` is GO and the finite base has a formula. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
2. It names the remainder as the recursion at infinite member stages. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
3. `finite-stage-inj` is the finite base. Basis: src/L/StageCardinal.lagda.md:485
4. The `Graph` shape is `[LJ-1.597]`'s. Basis: agents/tasks/LJ-1-597/Probe597.agda:269
5. `Recursion`'s condition is the graph alone. Basis: src/L/Recursion.lagda.md:259
6. `[LJ-1.596]` is a NO-GO at the whole object. Basis: agents/tasks/LJ-1-596/lj-1.596-report.md:1
7. `[LJ-1.594]` orders the five ingredients. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138
8. `step` is one equation. Basis: src/L/StageCardinal.lagda.md:561
9. Its value equation names `sq`. Basis: src/L/StageCardinal.lagda.md:283
10. `sq` is a bare module parameter. Basis: src/L/StageCardinal.lagda.md:17
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A measured formula for the finite base and a fixed `Formula S 2` shape to write
the other half in. **No formula at an infinite member stage.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHAT CHANGES AT A LIMIT.** Say at `file:line`
what the recursion does at an infinite member stage that it does not do at the
finite base. **If the answer is nothing but the index, the half is a
transcription and you should say so and finish early.**

**REUSE `[LJ-1.601]`'s SHAPE AND ITS TABLE TERM.** Import them. **Do not restate
its formula in your own words**: R-42 measures a cross-file respelling of one
object at 1.74 s against 155.02 s, and it was written from this campaign's own
runs.

**IF THE LIMIT CASE REACHES `sq`, SAY SO AND STOP.** Three tasks have already
arrived at that bare parameter from three directions (`[LJ-1.572]`,
`[LJ-1.594]`, `[LJ-1.597]`). **A fourth arrival is a result, not a failure**, and
it would tell the mathematician that (iv) and (iii) are one problem rather than
two.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.** Two tasks
ran 1800 s this week because nobody capped one.

**DO NOT ATTEMPT (i), (ii), (iii) OR (v).** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT CHANGES AT THE LIMIT`.** At `file:line`.

**REQUIRED REPORT SECTION `## DOES (iv) REACH sq`.** Two sentences, yes or no,
with the site. **This is the question the mathematician most wants answered.**

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.601]` did the sibling half. Comparables are of SHAPE and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the limit case's own index.

    -- the recursion's index at an infinite member stage, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 12 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO COMPLETES INGREDIENT (iv)**, leaving (iii) and (v) of the five.

**A NO-GO THAT SHOWS THE LIMIT CASE REACHES `sq` MERGES TWO INGREDIENTS INTO
ONE**, which is worth as much and would re-price the whole formula.

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
  changed_files_none = ["agents/tasks/LJ-1-603/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-603/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-603/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-603/Probe603.agda"]
  changed_files_none = ["agents/tasks/LJ-1-603/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-603/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 204.874)
- CANDIDATE archive/dev/JOURNAL.md  (score 196.842)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 193.804)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 158.495)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 157.668)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 65.210)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.149)
- CANDIDATE dev/literature/digest.md  (score 55.481)
- CANDIDATE dev/literature/geology.md  (score 44.058)
- CANDIDATE dev/literature/terms-2026-08.md  (score 37.117)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
