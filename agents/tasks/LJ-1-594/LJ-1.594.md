# LJ-1.594: what a definable pairing would cost L.StageCardinal

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-594/Probe594.agda`:

    pairing-suffices :
      <a definable pairing for `L.StageCardinal`, stated as a hypothesis>
      → <`[LJ-1.584]`'s `Reopener`, `InjL (Lset α) α`>

**State the pairing hypothesis yourself. Naming it is the deliverable.** Land
nothing in `src/`.

**`[LJ-1.584]` IS A NO-GO AND THIS IS ITS ROUTE 2.** In its own words:

> **"GIVE `L.StageCardinal` A DEFINABLE PAIRING INSTEAD OF `sq`.** If the module
> took a pairing that came with a formula rather than a bare injection, section
> 2's theorem would carry the formula through to `h`, because `class-pred`'s
> other two ingredients are already internal: `defSet` is `𝒟ₒ`
> (`src/L/StageCardinal.lagda.md:400-401`), and the least-element selection is
> the ordinal order (`src/L/StageCardinal.lagda.md:258-259`). **THE PAIRING IS**
> [the only non-internal part]."

**SO TWO OF THE THREE INGREDIENTS ARE ALREADY INTERNAL, MEASURED BY THAT TASK.**
That is why this is worth one brief: the module is one substitution away from
carrying a formula, and nobody has priced the substitution.

**`[LJ-1.592]` IS CARRYING ROUTE 1 IN PARALLEL AND THE TWO ARE INDEPENDENT.**
Either reopens the object. **Do not build route 1's term and do not wait on it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-594/Probe594.agda::pairing-suffices"]

## SCOPE (write)
- agents/tasks/LJ-1-594/Probe594.agda
- agents/tasks/LJ-1-594/lj-1.594-report.md
- agents/tasks/LJ-1-594/review-of-pairing-suffices.md
- agents/tasks/LJ-1-594/runs/

## PREMISES

1. `[LJ-1.584]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:12
2. Its route 2 names a definable pairing. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:123
3. `defSet` is `𝒟ₒ` in that module. Basis: src/L/StageCardinal.lagda.md:400
4. The least-element selection is the ordinal order. Basis: src/L/StageCardinal.lagda.md:258
5. `stage-card-upper` is the ambient bound. Basis: src/L/StageCardinal.lagda.md:564
6. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:38
7. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
8. `[LJ-1.585]` measured that this object buys at most one row. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
9. `[LJ-1.526]` named a fact and `[LJ-1.528]` then built it. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
10. `[LJ-1.587]` delivered two general `InjL` producers. Basis: agents/tasks/LJ-1-587/Probe587.agda:255
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A module whose other two ingredients are already internal, and no pairing that
carries a formula.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS `sq` AT ITS SITE.** Say at `file:line` where
`L.StageCardinal` takes `sq`, what its type is, and how many places use it.
**Never conclude a count from a command containing `head`.**

**STATE THE PAIRING AS WEAKLY AS YOU CAN.** The value is in how little it
assumes. **If your hypothesis is as strong as the conclusion, it is not a
reduction and you must say so plainly.** `[LJ-1.526]` did this half well for B4
and `[LJ-1.528]` then built it; that is the pattern.

**DO NOT EDIT `src/L/StageCardinal.lagda.md`.** State the substituted module in
your own probe. **Nothing lands in `src/`.**

**DO NOT BUILD THE PAIRING.** This brief prices it and names it. If it is one
line, say so and build it, but do not spend the estimate trying.

**DO NOT CLAIM BOTH ROWS.** `[LJ-1.585]` measured that this object buys at most
one.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE PAIRING, STATED`.** In full, with one sentence
on what it assumes.

**REQUIRED REPORT SECTION `## WHAT SUBSTITUTING IT WOULD COST src/`.** The sites
that use `sq`, counted, and one sentence on whether the substitution is local.
**A count you measured.**

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.526]` made a comparable reduction. Comparables are of SHAPE and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `sq`'s type at the module header.

    -- L.StageCardinal's sq parameter, re-ascribed alone, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 10 lines, under 60
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO NAMES A SUBSTITUTION THAT MAKES A WHOLE CHAPTER CARRY FORMULAS**, which
would serve more than this one row.

**A NO-GO SHOWING THE PAIRING MUST BE AS STRONG AS THE CONCLUSION CLOSES ROUTE
2**, and leaves `[LJ-1.592]`'s route 1 carrying the object alone. That is worth
knowing early.

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
  changed_files_none = ["agents/tasks/LJ-1-594/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-594/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-594/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-594/Probe594.agda"]
  changed_files_none = ["agents/tasks/LJ-1-594/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-594/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park_and_split"

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

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL.md  (score 179.516)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 168.179)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 167.063)
- CANDIDATE dev/ARCHIVE.md  (score 145.769)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 140.668)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 64.392)
- CANDIDATE dev/literature/devlin-II5.md  (score 57.251)
- CANDIDATE dev/literature/digest.md  (score 37.488)
- CANDIDATE dev/literature/geology.md  (score 32.157)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
