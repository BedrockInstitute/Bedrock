# LJ-1.600: keyS at this carrier, the first piece of the ordered route

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-600/Probe600.agda`:

    key-at-stage : <`keyS` instantiated at `A := LsetS δ oδ`>

that is, ingredient **(v)** of the `class-pred` formula, the coded copy at this
carrier. Land nothing in `src/`.

**TWO TASKS INDEPENDENTLY ORDERED THIS PIECE FIRST AND NAMED IT.** `[LJ-1.594]`
wrote the route (`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138`):

> "The order the pieces go in is **(v) first, because the existential's range has
> to exist before the rest of the clause can be written: `keyS` at
> `A := LsetS δ oδ`.** Then (i) and (ii), which are already internal. Then (iv)
> through `L.Recursion`'s `Definition`, whose `dom` is `hierL`. **The pairing,
> (iii), goes in LAST and is the smallest of the five.** A brief that asks for
> the whole formula in one dispatch is asking for a chapter; **the first dispatch
> worth ordering is (v) at this carrier, because it is the one nobody has
> instantiated here.**"

**AND IT SAYS THE TREE HAS ALREADY ANSWERED THIS SHAPE TWICE.** `Coding/CodeSet`
and `Coding/Powerset` "are the CURE for the shape and not an instance of it:
they are where the coded copy is built."

**`[LJ-1.597]` REPEATED THE ORDER AND ADDED TWO CONSTRAINTS.** A brief that
orders (v) **must name the STAGE that holds `AllCodes` at this carrier**, because
`[LJ-1.86]` measured that the proof cannot choose it
(`archive/dev/LJ-dispatch-index.md:160`), and **must name the LIVE chapter
`src/L/Coding/CodeSet.lagda.md`, NOT the retired `L.Rud.CodeSet`.**

**DO NOT ATTEMPT THE WHOLE `class-pred` FORMULA.** Its predecessor calls that a
chapter. AD12 gives this brief one obligation and this is the first of five.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-600/Probe600.agda::key-at-stage"]

## SCOPE (write)
- agents/tasks/LJ-1-600/Probe600.agda
- agents/tasks/LJ-1-600/lj-1.600-report.md
- agents/tasks/LJ-1-600/review-of-key-at-stage.md
- agents/tasks/LJ-1-600/runs/

## PREMISES

1. `[LJ-1.594]` states the order and names (v). Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138
2. It names `CodeSet` and `Powerset` as the cure for the shape. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:128
3. `[LJ-1.597]` repeats the order and adds the two constraints. Basis: agents/tasks/LJ-1-597/review-of-step-graph.md:154
4. `[LJ-1.86]` measured that the proof cannot choose the stage. Basis: archive/dev/LJ-dispatch-index.md:160
5. The live chapter is `CodeSet`. Basis: src/L/Coding/CodeSet.lagda.md:1
6. `step` is one equation. Basis: src/L/StageCardinal.lagda.md:561
7. Its value equation names `sq`. Basis: src/L/StageCardinal.lagda.md:283
8. `sq` is a bare module parameter. Basis: src/L/StageCardinal.lagda.md:17
9. `[LJ-1.572]` measured the chain to `sq` by refl. Basis: agents/tasks/LJ-1-572/review-of-b9-g-definable.md:116
10. `[LJ-1.568]` proved coding is describing, necessary and sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Two chapters that build a coded copy, an ordered route naming five ingredients,
and three independent measurements that the chain bottoms out at `sq`. **No
instantiation of (v) at this carrier.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE STAGE.** `[LJ-1.86]` measured that the
proof cannot choose the stage holding `AllCodes`. **Name it at `file:line`
before you build.** If you cannot name it, say so and stop: that is the
measurement and it costs one hour.

**USE THE LIVE CHAPTER.** `src/L/Coding/CodeSet.lagda.md`. **`L.Rud.CodeSet` is
retired and importing it is a defect**, not a shortcut.

**READ HOW `CodeSet` AND `Powerset` BUILD THEIR COPY BEFORE YOU BUILD YOURS.**
`[LJ-1.594]` says they are the cure for this shape. **Say at `file:line` what
each does and whether the method instantiates here.**

**MEASURE THE FLOOR FIRST AND TIME-BOX IT.** State the obligation with a hole
and typecheck it under an explicit wall-clock cap you set yourself. **If the
floor does not finish inside your cap, stop and report the cap and the fact,
rather than waiting.** Two tasks this week ran 1800 s because nobody time-boxed
a typecheck.

**DO NOT ATTEMPT (i), (ii), (iii) OR (iv).** AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE STAGE, NAMED`.** At `file:line`, with how you
chose it and why the proof could not.

**REQUIRED REPORT SECTION `## WHAT (i) AND (ii) NOW NEED`.** Three sentences.
`[LJ-1.594]` calls them already internal. **Say whether your (v) lets them be
written, and name what a brief on them should carry.** Do not build them.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.594]` and `[LJ-1.597]` worked this machinery at comparable sizes.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `keyS` at this carrier.

    -- keyS with A := LsetS δ oδ, re-ascribed, TYPE ONLY, under a wall-clock cap

**Write it FIRST, typecheck it ALONE, and cap it.** ESTIMATE: about 12 lines,
and set your own cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE FIRST PIECE OF THE ONLY ORDERED ROUTE TWO TASKS HAVE AGREED ON**,
and it unblocks the four pieces behind it.

**A NO-GO THAT NAMES WHY THE STAGE CANNOT BE CHOSEN HERE IS A RULING**, because
`[LJ-1.86]` measured the same wall at an older tree and the mathematician must
know whether it still stands.

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
  changed_files_none = ["agents/tasks/LJ-1-600/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-600/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-600/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-600/Probe600.agda"]
  changed_files_none = ["agents/tasks/LJ-1-600/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-600/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 202.436)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 195.626)
- CANDIDATE archive/dev/JOURNAL.md  (score 193.216)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 174.299)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 169.860)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 67.030)
- CANDIDATE dev/literature/digest.md  (score 59.492)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.603)
- CANDIDATE dev/literature/terms-2026-08.md  (score 45.509)
- CANDIDATE dev/literature/geology.md  (score 41.418)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
