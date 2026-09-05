# LJ-1.554: can a formula describe an assignment it was not built with

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-554/Probe554.agda`:

    no-generic-link :
      ( (δ κ : S) (s : ⟪ fst δ ⟫ → S)
        → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
        → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
        → Σ[ Link ∈ Formula S 3 ] <the two readings of [LJ-1.549]'s Residue> )
      → Empty.⊥

**IF YOU CAN INSTEAD BUILD THE GENERIC `Link`, DO THAT AND REPORT A GO**, with
the built term named in place of `no-generic-link` in your report's first line.
**One of the two is true and the task is to find out which.** Land nothing in
`src/`.

**WHY THIS IS THE RIGHT QUESTION NOW.** `[LJ-1.549]` is a NO-GO, upheld, and it
named exactly two missing inputs for B10: the ambient assignment `s` and its
object-language description `Link`
(`agents/tasks/LJ-1-549/review-of-succ-into-subsets.md`, FINDING 2).
`[LJ-1.552]` takes the assignment. **This brief asks whether the second follows
from the first, or whether the two must be built TOGETHER.** That answer decides
the shape of every later brief on this row, and it costs one task to get.

**`[LJ-1.533]` IS THE PRECEDENT AND IT WORKED.** It proved by a type argument
that no term codes an arbitrary ambient injection
(`agents/tasks/LJ-1-533/lj-1.533-report.md`). **The shape of that argument is
the shape this task probably wants**, and a measured cure does not transfer by
analogy, so re-measure it here.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-554/Probe554.agda::no-generic-link"]

## SCOPE (write)
- agents/tasks/LJ-1-554/Probe554.agda
- agents/tasks/LJ-1-554/lj-1.554-report.md
- agents/tasks/LJ-1-554/review-of-no-generic-link.md
- agents/tasks/LJ-1-554/runs/

## PREMISES

1. `Residue`'s `Link` component and its two readings are stated in full. Basis: agents/tasks/LJ-1-549/Probe549.agda:668
2. `[LJ-1.549]` names `s` and `Link` as the two missing inputs. Basis: agents/tasks/LJ-1-549/review-of-succ-into-subsets.md:63
3. Its critic upheld the stop. Basis: agents/tasks/LJ-1-549/review-of-LJ-1-549-1.md:1
4. `[LJ-1.533]` refuted a generic code by a type argument. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
5. `[LJ-1.535]` closed the counting-site route. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
6. `[LJ-1.514]` counted 664 constants in the Formula carrier. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:1
7. `Formula` is a set of syntax, not a function space. Basis: src/FOL/LevyHierarchy.lagda.md:47
8. `[LJ-1.516]` found the Levy grade to be the real obstruction on a sibling row. Basis: agents/tasks/LJ-1-516/lj-1.516-report.md:1
9. A stop is a deliverable. Basis: AGENTS.md:43
10. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
11. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A residue that names two missing inputs and a term that spends the whole residue
for B10. **Nothing says whether the two inputs are independent.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE COUNTING.** Say at `file:line` how many
`Formula S 3` there are and how many assignments `⟪ fst δ ⟫ → S` there are.
**If the formulas are a set and the assignments are a function space into a
proper carrier, say so**: that is the whole argument and the rest is writing it
down.

**DO NOT ASSUME THE ANSWER FROM `[LJ-1.533]`.** It refuted a code for an
arbitrary ambient INJECTION. This asks about an arbitrary ASSIGNMENT with two
laws, which is a different statement at a different arity. **Re-measure.**

**IF THE REFUTATION NEEDS A CARDINALITY FACT THE TREE DOES NOT HAVE, SAY SO AND
STOP.** Do not import one and do not postulate one. `[LJ-1.526]` overturned an
archived claim about cardinals by measurement, so **check before you believe the
tree lacks it.**

**DO NOT BUILD `s`. DO NOT BUILD B10.** `[LJ-1.552]` has the assignment. AD12
gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHICH WAY IT WENT`.** One paragraph. Say whether
the generic `Link` exists, and say what that means for `[LJ-1.552]`'s successor:
**either `Link` can be added to any assignment, or the assignment must be built
WITH its formula in one task.**

**REQUIRED REPORT SECTION `## WHAT A NON-GENERIC LINK WOULD NEED`.** Three
sentences. If the generic one is refuted, **say what extra property of `s` a
`Link` would need** — definability, a bound, a Levy grade. Do not build it.

ESTIMATE: about 120 lines in the probe, of which the obligation is about 30.
BASIS: `[LJ-1.533]` made a comparable type argument. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the arity-3 satisfaction reading itself.

    -- ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩ for an abstract Link, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If the reading will not even form
away from `[LJ-1.549]`'s frame, the task is about a different statement and you
must say so before spending the estimate. ESTIMATE: about 12 lines, under 60
seconds.

## WHAT GO AND NO-GO EACH EARN

**EITHER OUTCOME IS A FULL RESULT AND I MEAN IT.** A generic `Link` would make
`[LJ-1.552]` sufficient for B10 on its own. A refutation says the assignment and
its formula are one task, and it saves the campaign from splitting them again.

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
  changed_files_none = ["agents/tasks/LJ-1-554/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-554/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-554/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-554/Probe554.agda"]
  changed_files_none = ["agents/tasks/LJ-1-554/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-554/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 158.299)
- CANDIDATE archive/dev/JOURNAL.md  (score 156.284)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 151.675)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 145.450)
- CANDIDATE archive/dev/DD-archived.md  (score 139.685)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 61.103)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 54.894)
- CANDIDATE dev/literature/digest.md  (score 54.253)
- CANDIDATE dev/literature/terms-2026-08.md  (score 43.569)
- CANDIDATE dev/literature/geology.md  (score 33.159)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
