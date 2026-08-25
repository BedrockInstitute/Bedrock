# LJ-1.528: CardAboveL, the one input the successor cardinal still wants

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-528/Probe528.agda`:

    CardAboveL :
        (κ : S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ θ ∈ S ] (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

**SOME ordinal L-cardinal above κ. Not the successor.** Land nothing in `src/`.

**`[LJ-1.526]` IS A NO-GO ON B4 THAT DELIVERED A GREEN REDUCTION.**
`reduction : CardAboveL → SuccCardExists`
(`agents/tasks/LJ-1-526/Probe526.agda:285-292`), no holes. Its report says:
"B4 is one input and it has a name. `CardAboveL`. Everything else the successor
cardinal needs is in the tree today". **`[LJ-1.523]`'s seven unpaid inputs
become six the moment this lands.**

**DO NOT ASK FOR κ⁺ DIRECTLY.** `[LJ-1.526]` says a brief that does "would
rebuild the 104 lines of `module Reduce` and discover the same wall".

**AND `[LJ-1.526]` OVERTURNED THE ARCHIVE FINDING THAT MADE THIS LOOK
IMPOSSIBLE.** `archive/dev/LJ-dispatch-index.md:166` records `[LJ-1.90-A]`:
"IsCardinal is never inhabited. CONFIRMED." **That is now false.** `ω-card`
(`Probe526.agda:130-133`) and `ω-cardL` (`:137`) inhabit the ambient and the
internal predicate, and the report says ω cost four lines.

**THE ARCHIVE ALSO HOLDS A LARGE DELIVERED COMPARABLE AND YOU MUST READ IT.**
`archive/dev/LJ-dispatch-index.md:170` records `[LJ-1.94]`: "Build the ambient
Hartogs cardinal and end at the consumer. CARDK SUPPLIED, GREEN. **1058 lines,
27 s, no choice.** But `IsCardinal` is stated locally, and the next blocker is
Devlin55's `sq`". **That probe is on disk**:
`agents/tasks/LJ-1-94/ProbeLJ194A.agda`, with `cardκ : IsCardinal κ` at
`:1160` and `:1196`, the Hartogs set built at `:866`.

**IT IS AMBIENT AND THIS OBLIGATION IS INTERNAL.** `grep -rn "Hartogs" src`
returns NOTHING and `archive/src/` returns nothing: **the 1058 lines never
landed.** `[LJ-1.526]` reports that the ambient-to-internal bridge EXISTS while
the other direction does not. **So the shape is: an ambient cardinal above κ,
then that bridge. Measure both. Neither is free and the 1058 lines are a
comparable of SHAPE, not a price.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-528/Probe528.agda::CardAboveL"]

## SCOPE (write)
- agents/tasks/LJ-1-528/Probe528.agda
- agents/tasks/LJ-1-528/lj-1.528-report.md
- agents/tasks/LJ-1-528/review-of-CardAboveL.md
- agents/tasks/LJ-1-528/runs/

## PREMISES

1. `[LJ-1.526]` delivered the reduction from this to B4. Basis: agents/tasks/LJ-1-526/Probe526.agda:285
2. It states this obligation's type. Basis: agents/tasks/LJ-1-526/Probe526.agda:178
3. It inhabits the internal predicate at ω. Basis: agents/tasks/LJ-1-526/Probe526.agda:137
4. It inhabits the ambient predicate at ω. Basis: agents/tasks/LJ-1-526/Probe526.agda:130
5. `IsCardinalL` is the internal predicate. Basis: src/L/Cardinal.lagda.md:230
6. `IsCardinal` is the ambient one. Basis: src/L/BoundedSubset.lagda.md:1046
7. `[LJ-1.94]` built the ambient Hartogs cardinal in a probe. Basis: agents/tasks/LJ-1-94/ProbeLJ194A.agda:1160
8. Its Hartogs set is built there. Basis: agents/tasks/LJ-1-94/ProbeLJ194A.agda:866
9. `[LJ-1.523]` counted seven unpaid inputs on the GCH bridge. Basis: agents/tasks/LJ-1-523/Probe523.agda:191
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE TROPHY'S WITNESS IS NOT UNREACHABLE, WHICH IS WHAT THE OWNER ASKED.**
`[LJ-1.526]` measured that `[LJ-1.91]`'s ambient obstruction does not reach the
internal predicate, and delivered the reduction. **What stands between GCH and
its δ is this one statement.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read `[LJ-1.94]`'s probe and say at `file:line` what
its `IsCardinal κ` is stated against, since the index says it is "stated
locally". **If its predicate is not `src/L/BoundedSubset.lagda.md:1046-1047`'s,
the 1058 lines do not transfer and you must say so before anything rests on
them.**

**THEN CHOOSE, AND SAY WHY IN THE REPORT.** Either rebuild the ambient Hartogs
and cross the bridge, or find a shorter internal route. **`[LJ-1.526]` reports
that ω cost four lines both ways; whether that generalises above ω is the
question and nobody has asked it.**

**DO NOT REBUILD 1058 LINES WITHOUT SAYING SO FIRST.** If the route needs them,
write the report's estimate section BEFORE the Agda and let the record show the
decision. C-22 requires the report early in any case.

**DO NOT ASK FOR THE SUCCESSOR.** `SOME` cardinal above κ is the obligation.
`[LJ-1.526]`'s reduction turns it into the successor.

**DO NOT POSTULATE AND DO NOT ASSUME CHOICE.** `[LJ-1.94]` recorded its
construction as choice-free and any route here should say whether it is.

**REQUIRED REPORT SECTION `## AMBIENT OR INTERNAL`.** Which route you took, and
what the other would have cost, at `file:line`. **Do not price the one you did
not take in lines unless you measured it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: **I do not give one.** The only comparable is 1058 lines
in a probe that never landed, at a different predicate, and quoting it as a
price would be the mistake this campaign has made three times tonight. **Report
what it actually cost.**

## W3, THE WIDEST UNMEASURED TERM

It is whether `IsCardinalL` has an inhabitant ABOVE ω, because `[LJ-1.526]`
inhabited it AT ω in four lines and everything here turns on the step up.

    someCardinalL-above : ∥ Σ[ θ ∈ S ] (IsOrd (fst θ) × IsCardinalL θ
                          × ⟨ fst ωʟ ∈ˢ fst θ ⟩) ∥₁

**Write it FIRST, at the one concrete κ = ωʟ, and typecheck it ALONE.** If no
L-cardinal above ω can be exhibited, the general statement is out of reach and
the task stops at its cheapest point with the sharpest finding this campaign
could produce.

ESTIMATE for W3: unknown, and the brief will not guess. **Report it.**

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES GCH ITS δ** and turns `[LJ-1.523]`'s seven unpaid inputs into six.

**A NO-GO AT ω⁺ SAYS THE INTERNAL CARDINALS STOP AT ω IN THIS TREE**, which
would be the ruling-grade finding about GCH that four archived dispatches
circled without stating.

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
  changed_files_none = ["agents/tasks/LJ-1-528/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-528/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-528/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-528/Probe528.agda"]
  changed_files_none = ["agents/tasks/LJ-1-528/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-528/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 250.099)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 210.073)
- CANDIDATE archive/dev/JOURNAL.md  (score 177.535)
- CANDIDATE dev/ARCHIVE.md  (score 163.113)
- CANDIDATE archive/dev/DD-archived.md  (score 147.179)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 63.906)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 62.343)
- CANDIDATE dev/literature/digest.md  (score 49.084)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.935)
- CANDIDATE dev/literature/geology.md  (score 35.097)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
