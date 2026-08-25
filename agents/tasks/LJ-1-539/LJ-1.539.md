# LJ-1.539: the subK family collected, against a real heap figure

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-539/Probe539.agda`:

    subK-frame-inhabited :
        (the extra hypotheses the SIX subK forms take, collected as one
         telescope)
      → (a witness of that telescope at KValue's frame)

**the `subK` family ONLY, the second of the honest-form families.** Land
nothing in `src/`.

**`[LJ-1.538]` IS GO AND IT GAVE THE METHOD AND THE NUMBER.** It collected the
nine `envK-*` and `envInK-*` forms and inhabited them:
**3.56 s cold and 722,698,240 B peak RSS**
(`agents/tasks/LJ-1-538/lj-1.538-report.md:26`), where `[LJ-1.534]`'s attempt at
all sixteen at once hit a heap wall four times. **One family at a time works.
Price yourself against 538's number and report yours beside it.**

**AND ITS RESULT WAS BETTER THAN I EXPECTED.** Of the eight hypotheses it
collected, **seven are supplied by `KValue` already** and only one is NEW:
`ω∈σ : ⟨ ω ∈ sucV gam ⟩` (`src/L/Coding/EnvSupply.lagda.md:111`), which is the
gate `[LJ-1.503]` measured and the mathematician ruled. **Each of the nine cost
one application and one `refl`, with no `subst` and no weakening.**

**THE `subK` FAMILY IS THE NEXT AND IT IS ALREADY WRITTEN OUT.** `[LJ-1.509]`
is GO and found `subK-gen` (`src/L/Coding/EnvSupply.lagda.md:481-487`), generic
in the environment length and all four indices, **already instantiated at five
of the six prefixes** (`:506`, `:517`, `:528`, `:539`, `:550`). The sixth,
`subK-un`, needs the sibling `subKSucc-gen` (`:489-495`), also delivered.

**AND `[LJ-1.509]` MEASURED THAT ALL SIX WANT ONE MEMBERSHIP.** They read `T`
out of the same cell, `γ'` position one. **`[LJ-1.508]` ruled the slot-one
hypothesis `valSub` and `[LJ-1.530]` built `dK` and `zK` at that frame. Say
which of those the six can take and which they cannot.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-539/Probe539.agda::subK-frame-inhabited"]

## SCOPE (write)
- agents/tasks/LJ-1-539/Probe539.agda
- agents/tasks/LJ-1-539/lj-1.539-report.md
- agents/tasks/LJ-1-539/review-of-subK-frame.md
- agents/tasks/LJ-1-539/runs/

## PREMISES

1. `[LJ-1.538]` is GO and collected the nine env forms. Basis: agents/tasks/LJ-1-538/lj-1.538-report.md:26
2. Only one of its eight hypotheses was NEW. Basis: agents/tasks/LJ-1-538/Probe538.agda:159
3. `[LJ-1.509]` is GO on the `subK` family. Basis: agents/tasks/LJ-1-509/lj-1.509-report.md:56
4. `subK-gen` is delivered and generic. Basis: src/L/Coding/EnvSupply.lagda.md:481
5. `subKSucc-gen` is its sibling for the successor form. Basis: src/L/Coding/EnvSupply.lagda.md:489
6. It is instantiated at five prefixes already. Basis: src/L/Coding/EnvSupply.lagda.md:506
7. The gate is `SupplyEnv`'s own. Basis: src/L/Coding/EnvSupply.lagda.md:111
8. `[LJ-1.508]` ruled the slot-one hypothesis. Basis: agents/tasks/LJ-1-508/Probe508.agda:201
9. `[LJ-1.530]` built `dK` at this frame. Basis: agents/tasks/LJ-1-530/Probe530.agda:131
10. It built `zK` beside it. Basis: agents/tasks/LJ-1-530/Probe530.agda:169
11. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**ONE FAMILY OF FIFTY NINE FIELDS IS COLLECTED AND INHABITED, AT ONE NEW
HYPOTHESIS.** That is `[LJ-1.538]`. **The `subK` family is six more fields with
a delivered generic and five delivered instantiations.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.538]` found one of its eight hypotheses
carried but never consumed. **Do the same audit here: list what `subK-gen` and
`subKSucc-gen` actually use, and say which telescope entries are dead weight.**
Size is what killed `[LJ-1.534]`.

**TRIM, THEN COLLECT, THEN INHABIT. IN THAT ORDER.**

**REPORT THE PEAK RSS BESIDE 538's 722,698,240 B.** Two families with two
figures tell the mathematician whether the whole record can be collected or
only its parts.

**DO NOT COLLECT THE READERS OR `someEnv`.** AD12 gives this brief one
obligation and `[LJ-1.534]` measured what happens when the scope is everything.

**DO NOT REBUILD `subK-gen` OR ITS FIVE INSTANTIATIONS.** `[LJ-1.509]` found
them delivered. Cite them.

**DO NOT ASSUME `valSub`, `dK` OR `zK` FITS.** All three are built at this
frame, and whether the six `subK` forms want them is the question, not the
premise.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## THE SIX, AND WHAT THEY COST`.** Every hypothesis
at its `file:line`, and for each: supplied by `KValue`, supplied by a
predecessor's term, or NEW. **Plus the peak RSS.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.538]` collected nine forms at this frame and reported
its own figures. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is which slot-one fact the six take, because three are built at this frame
and no dispatch has asked which of them `subK-gen` wants.

    -- subK-gen's TK argument, at the frame, from valSub or dK or zK or none

**Write it FIRST, and typecheck it ALONE.** If none of the three fits, the
`subK` family needs a fourth slot-one fact and that is the finding.

ESTIMATE for W3: about 20 lines and under 40 seconds. **Do not fund it against
`[LJ-1.538]`'s numbers**: that collected env forms and this matches a
membership.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES A SECOND COLLECTED FAMILY AND A SECOND HEAP FIGURE**, and the
remaining forms can be priced by extrapolation from two points instead of one.

**A NO-GO SAYS THE SIX WANT A SLOT-ONE FACT NOBODY HAS BUILT**, which is one
named statement and not a wall.

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
  changed_files_none = ["agents/tasks/LJ-1-539/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-539/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-539/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-539/Probe539.agda"]
  changed_files_none = ["agents/tasks/LJ-1-539/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-539/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 207.232)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 205.434)
- CANDIDATE archive/dev/JOURNAL.md  (score 188.360)
- CANDIDATE dev/ARCHIVE.md  (score 173.137)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 145.579)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.228)
- CANDIDATE dev/literature/devlin-II5.md  (score 54.253)
- CANDIDATE dev/literature/digest.md  (score 48.019)
- CANDIDATE dev/literature/geology.md  (score 44.991)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 38.371)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
