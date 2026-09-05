# LJ-1.517: a witness other than hierL, which is the door 494 left open

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-517/Probe517.agda`:

    approx-in-stage :
        (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
      → Σ[ f ∈ S ] (⟨ fst f ∈ˢ Lset α ⟩ × (f approximates the tower below δ))

**a witness for `ApproxAt` that lies in the stage, and it must NOT be
`hierL`.** Land nothing in `src/`, and if no such witness exists, say so with
the census that shows it.

**`[LJ-1.494]` NAMED THIS DOOR AND NOBODY HAS WALKED THROUGH IT.** Its
next-brief section reads: "Do not order `GraphSatAtStage` until
`hier-in-stage` is delivered, **or until a brief names a different witness than
`hierL`**" (`agents/tasks/LJ-1-494/lj-1.494-report.md:358-360`). Eight
condensation dispatches have gone at the first half. **This is the second.**

**WHY `hierL` IS THE WRONG WITNESS.** `[LJ-1.494]` measured that the tree does
not bound `hierL δ` by `α` (`:127`). `hierL` returns an element of `L`
(`src/L/Hierarchy.lagda.md:621`), and being an element of `L` is not being an
element of THIS stage. **That measurement stands and this task does not
re-open it.**

**AND ONE ROUTE IS ALREADY CLOSED, SO DO NOT SPEND TIME ON IT.**
`src/FOL/Manipulation/Bounding.lagda.md` bounds a FORMULA's constants and its
own prose says the chapter "mentions neither levels nor stages" (`:24`). **It
is pure syntax. It cannot bound a set by a stage.** `[LJ-1.514]` used it
correctly for the formula and it does not generalise here.

**WHAT `GraphAt` ACTUALLY NEEDS.** `GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇
Step (suc w) (suc b) zero)` (`src/L/Coding/Sequence.lagda.md:291-292`). The
existential's witness is an approximation. **Any set that approximates the
tower below `δ` and lies in the stage will serve. The tree's own choice is
`hierL`; the question is whether it is the only one.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-517/Probe517.agda::approx-in-stage"]

## SCOPE (write)
- agents/tasks/LJ-1-517/Probe517.agda
- agents/tasks/LJ-1-517/lj-1.517-report.md
- agents/tasks/LJ-1-517/review-of-approx-in-stage.md
- agents/tasks/LJ-1-517/runs/

## PREMISES

1. `[LJ-1.494]` names a different witness as the alternative route. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:358
2. It measured that the tree does not bound `hierL δ` by the stage. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:127
3. `hierL` returns an element of `L`. Basis: src/L/Hierarchy.lagda.md:621
4. `GraphAt` is an existential over `ApproxAt` and `Step`. Basis: src/L/Coding/Sequence.lagda.md:291
5. `ApproxAt` is `domAt` conjoined with two universals. Basis: src/L/Coding/Sequence.lagda.md:286
6. `ApproxAt-value` reads a value out of an approximation. Basis: src/L/Coding/Sequence.lagda.md:298
7. The bounding chapter is pure syntax and mentions no stage. Basis: src/FOL/Manipulation/Bounding.lagda.md:24
8. `[LJ-1.514]` is GO and used that chapter for the formula. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:103
9. `Lset` and its readings are delivered. Basis: src/L/Hierarchy.lagda.md:646
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CONDENSATION LEG HAS TWO BLOCKERS AND ONE FELL TONIGHT.** `[LJ-1.514]`
removed the Formula-carrier wall for the whole family. `[LJ-1.516]` is
transporting the satisfaction. **This blocker is the other one, and it has been
attacked only from the `hierL` side.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS A CENSUS.** List, at `file:line`, every set
in `src/` that satisfies `ApproxAt` at an ordinal, or that a reading says
approximates the tower. **Then say which of them the tree bounds by a stage.**
If `hierL` is the only approximation the tree ever builds, **STOP AND SAY SO**:
that closes the door `[LJ-1.494]` left open, and it would mean
`GraphSatAtStage` depends on `hier-in-stage` and on nothing else, which is
worth knowing before another dispatch guesses.

**DO NOT REBUILD `hierL` AND DO NOT RE-MEASURE ITS BOUND.** `[LJ-1.494]`
settled that.

**DO NOT USE `Bounding`.** It is pure syntax by its own prose and cannot bound
a set by a stage.

**DO NOT POSTULATE A WITNESS AND DO NOT ADD A REFLECTION HYPOTHESIS.** If the
stage contains no approximation, that is the finding, and it is the same fact
`[LJ-1.494]` reached by a different road.

**DO NOT ATTEMPT `GraphSatAtStage`, `cover` OR `levelIn`.** AD12 gives this
brief one obligation, and `[LJ-1.516]` holds the transport.

**REQUIRED REPORT SECTION `## EVERY APPROXIMATION THE TREE BUILDS`.** The
census as a table, with `file:line` and whether each is bounded by a stage.
**This section is the deliverable even if the obligation is not built.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 35. BASIS: `[LJ-1.514]` built a census and an instance in 86 non-blank
non-comment lines. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the census, because the obligation may have no inhabitant and the census
decides that before any term is attempted.

    -- every set in src/ that ApproxAt holds of, by file:line

**Do this FIRST, before any term, and write it into the report as you go
(C-22).** If the census returns `hierL` alone, the task stops there with the
door closed and the leg's dependency named exactly.

ESTIMATE for W3: mostly reading, under 30 seconds of Agda. **Do not fund it
against `[LJ-1.514]`'s census run**: that counted a formula's constants with
`countFo` and this reads a chapter.

Report the median wall time and peak RSS over three forced rechecks, for the
full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CONDENSATION LEG A ROUTE THAT DOES NOT WAIT ON
`hier-in-stage`**, which eight dispatches have not delivered.

**A NO-GO CLOSES THE DOOR `[LJ-1.494]` LEFT OPEN**, and says `GraphSatAtStage`
depends on `hier-in-stage` alone. **That is worth as much: it would let the
mathematician stop hedging between two routes and price one.**

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
  changed_files_none = ["agents/tasks/LJ-1-517/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-517/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-517/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-517/Probe517.agda"]
  changed_files_none = ["agents/tasks/LJ-1-517/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-517/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 182.347)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 182.248)
- CANDIDATE archive/dev/JOURNAL.md  (score 180.317)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 159.817)
- CANDIDATE dev/ARCHIVE.md  (score 157.260)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 71.209)
- CANDIDATE dev/literature/digest.md  (score 56.155)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 51.189)
- CANDIDATE dev/literature/terms-2026-08.md  (score 47.961)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 44.990)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
