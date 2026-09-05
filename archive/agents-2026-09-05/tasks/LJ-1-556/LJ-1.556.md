# LJ-1.556: the square law, inside L

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-556/Probe556.agda`:

    square-inside-L :
      (κ : S) → IsOrd (fst κ) → IsCardinalL κ
      → <an L-SET injection of κ × κ into κ, coded>

an injection that lives in L and is witnessed by a code, not an ambient
function. Land nothing in `src/`.

**`[LJ-1.552]` IS A NO-GO, UPHELD, AND IT NAMED THIS AS STEP 2 OF THE ONLY
PRICED ROUTE IT FOUND.** Its `## WHAT WOULD REOPEN THIS` names `Codes δ κ`
(`agents/tasks/LJ-1-552/Probe552.agda:295-300`), whose existence half
decomposes into two steps, and the second is **"the square law INSIDE L: an
L-set injection of κ × κ into κ."**

**THE TREE HAS THE SQUARE LAW AMBIENTLY AND NOT INTERNALLY, AND THAT IS THE
WHOLE TASK.** `L.Ordinal.SquareLaw` is imported at `src/L/Cardinal.lagda.md:22`
and at `src/L/InjChain.lagda.md:23`, and `src/L/Cardinal.lagda.md:46` describes
its type as **"The ambient injection type, as the square-law chain carries
it."** An ambient injection is what `[LJ-1.533]`, `[LJ-1.535]`, `[LJ-1.549]` and
`[LJ-1.552]` have each failed to code, four times at four sites.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-556/Probe556.agda::square-inside-L"]

## SCOPE (write)
- agents/tasks/LJ-1-556/Probe556.agda
- agents/tasks/LJ-1-556/lj-1.556-report.md
- agents/tasks/LJ-1-556/review-of-square-inside-L.md
- agents/tasks/LJ-1-556/runs/

## PREMISES

1. `[LJ-1.552]` is a NO-GO and names `Codes δ κ` as the reopener. Basis: agents/tasks/LJ-1-552/Probe552.agda:295
2. Its second decomposition step is the square law inside L. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:171
3. Its critic upheld the stop. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:1
4. `SquareLaw` is imported by `Cardinal`. Basis: src/L/Cardinal.lagda.md:22
5. `SquareLaw` is imported by `InjChain`. Basis: src/L/InjChain.lagda.md:23
6. The chapter calls its injection type AMBIENT. Basis: src/L/Cardinal.lagda.md:46
7. `ordSWO` is the name `Cardinal` takes from it. Basis: src/L/Cardinal.lagda.md:22
8. `InjCode` is what a coded injection means here. Basis: src/L/Cardinal.lagda.md:223
9. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
10. `[LJ-1.51]` landed `SquareLaw` as a 775-line master. Basis: archive/dev/LJ-dispatch-index.md:100
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An ambient square law, used by two chapters. **No internal one.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER THE AMBIENT PROOF INTERNALIZES.**
Read `L.Ordinal.SquareLaw` and say at `file:line` what its injection is built
from. **Then say whether each step of it is available inside L**, and name the
first step that is not. If every step internalizes, say so and the task is a
transcription; if one does not, that step IS the result.

**DO NOT TRY TO CODE THE AMBIENT INJECTION.** `[LJ-1.533]` measured that no term
codes an arbitrary ambient injection, and three later tasks hit the same wall at
their own sites. **Build the internal one from internal parts, or stop.**

**IsCardinalL IS A HYPOTHESIS AND NOT A THING TO PROVE.** `[LJ-1.526]` overturned
an archived claim that it is never inhabited, so it is usable, but nothing here
asks you to inhabit it.

**DO NOT BUILD `Codes δ κ` AND DO NOT TOUCH THE ASSIGNMENT.** AD12 gives this
brief one obligation. `[LJ-1.557]` takes the other decomposition step.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT INTERNALIZED AND WHAT DID NOT`.** Step by
step against the ambient proof, each at `file:line`.

**REQUIRED REPORT SECTION `## WHAT THIS BUYS `Codes``.** Three sentences. Given
what you built, **say what step 1 of `[LJ-1.552]`'s decomposition still needs**,
and whether the two steps compose as it expected. Do not build step 1.

ESTIMATE: about 200 lines in the probe, of which the obligation is about 60.
BASIS: the ambient master is 775 lines by the archive's count, and an
internalization is not a rewrite of it. **This estimate is uncertain and I say
so.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the pairing that the internal injection must use.

    -- κ × κ as an L-SET, with its two projections, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If the product is not an L-set at
this frame, the obligation is about a different object and you must say so
before spending the estimate. ESTIMATE: about 15 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS HALF OF THE ONLY PRICED ROUTE TO B10 THAT ANY TASK HAS FOUND.**

**A NO-GO THAT NAMES THE FIRST NON-INTERNALIZING STEP TELLS THE CAMPAIGN THAT
THE SQUARE LAW IS AMBIENT BY NATURE**, which would close `[LJ-1.552]`'s route
and force the mathematician to look for a different one. That is worth as much.

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
  changed_files_none = ["agents/tasks/LJ-1-556/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-556/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-556/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-556/Probe556.agda"]
  changed_files_none = ["agents/tasks/LJ-1-556/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-556/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 167.458)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 153.342)
- CANDIDATE archive/dev/JOURNAL.md  (score 150.891)
- CANDIDATE dev/ARCHIVE.md  (score 137.850)
- CANDIDATE archive/dev/STATUS-archived.md  (score 106.441)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.278)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.934)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 41.980)
- CANDIDATE dev/literature/digest.md  (score 37.708)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 27.244)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
