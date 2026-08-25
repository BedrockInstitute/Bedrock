# LJ-1.618: the pairing at ONE alpha, which its own pricer called the smallest of five

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-618/Probe618.agda`:

    pairing-at-alpha :
      (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
          ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

that is, **ONE binary function on one infinite ordinal with its injectivity.**
Land nothing in `src/`. **You are not asked for a family, a band, or a product.**

**THIS IS THE OBJECT AT THE GRAIN THE TREE ACTUALLY SPENDS.** `L.StageCardinal`
is instantiated in exactly one place (`src/L/BoundedSubset.lagda.md:1397`), `sq`
is a Π-bound parameter there (`:1388`), and it is spent at ONE α
(`:1410`, `sq α (self∈sucV α) α∉ω`).

**AND ITS OWN PRICER CALLED IT THE SMALLEST OF FIVE.** `[LJ-1.604]`: "At ONE
site the ingredient costs **one binary function with its injectivity**, and I
agree with `[LJ-1.594]` that it is **the smallest of that site's five**."

**THE CIRCLE `[LJ-1.607]` PROVED IS AT THE MODULE GRAIN, NOT THIS ONE.** It
measured that the uniform supply over the band IS the square law at the band.
**A single pairing at a single infinite ordinal is a different object**, and this
brief does not dispute that proof: it works below it.

**`[LJ-1.617]` IS ASKING WHETHER THE BILL EVER NEEDS THE WIDER GRAIN, IN
PARALLEL. THIS TASK DOES NOT WAIT ON IT.** A pairing at one infinite ordinal is
worth having whichever way that answer falls.

**AND IT IS CLASSICAL.** At every infinite ordinal the square is in bijection
with the ordinal; `[LJ-1.605]` said so while refusing to fund the band version.
**So look for it in the tree before you build it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-618/Probe618.agda::pairing-at-alpha"]

## SCOPE (write)
- agents/tasks/LJ-1-618/Probe618.agda
- agents/tasks/LJ-1-618/lj-1.618-report.md
- agents/tasks/LJ-1-618/review-of-pairing-at-alpha.md
- agents/tasks/LJ-1-618/runs/

## PREMISES

1. `L.StageCardinal` is instantiated at one site. Basis: src/L/BoundedSubset.lagda.md:1397
2. `sq`'s type is stated there. Basis: src/L/BoundedSubset.lagda.md:1388
3. It is spent at one α. Basis: src/L/BoundedSubset.lagda.md:1410
4. `[LJ-1.604]` prices it at one site as the smallest of five. Basis: agents/tasks/LJ-1-604/lj-1.604-report.md:1
5. `[LJ-1.605]` measured the band version as the square law. Basis: agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90
6. `[LJ-1.607]` confirmed the circle at the module grain. Basis: agents/tasks/LJ-1-607/lj-1.607-report.md:173
7. `sq`'s own type in the module. Basis: src/L/StageCardinal.lagda.md:17
8. `SquareLaw` is imported by `Cardinal`. Basis: src/L/Cardinal.lagda.md:22
9. `[LJ-1.593]` forbade a fourth square-law dispatch. Basis: agents/tasks/LJ-1-593/review-of-square-coded.md:73
10. `[LJ-1.613]` paid ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An ambient square law at ω and at the initial ordinals, and a truncated one at
the band. **No single pairing stated at one infinite ordinal as a Σ.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SEARCH.** `L.Ordinal.SquareLaw` exists
and `src/L/Cardinal.lagda.md:22` takes `ordSWO` from it. **Grep for anything
that already gives a pairing at ONE infinite ordinal, and report what you found
at `file:line` before you build anything.** `[LJ-1.560]`'s obligation turned out
to be an instantiation of something already present, and that is a good outcome.

**IF THE TREE HAS IT TRUNCATED ONLY, SAY SO AND SAY WHAT UNTRUNCATING ONE
INSTANCE COSTS.** `[LJ-1.607]` measured that untruncating the BAND is the square
law. **One instance is not the band, and whether that distinction survives is
exactly what I want measured.**

**DO NOT BUILD THE BAND VERSION AND DO NOT ATTEMPT THE SQUARE LAW.**
`[LJ-1.593]` forbade a fourth square-law dispatch and `[LJ-1.605]` was the fifth
arrival. **This brief is strictly below that object.**

**IF ONE INSTANCE ALSO NEEDS THE UNTRUNCATION, SAY SO AND STOP.** That would
mean the circle reaches down to the site grain too, and it is the single most
useful thing this task could report.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT THE TREE ALREADY HAS`.** Every candidate at
`file:line`, each marked as reaching one α or not.

**REQUIRED REPORT SECTION `## DOES THE CIRCLE REACH THE SITE GRAIN`.** Two
sentences, yes or no, with the site. **That is the answer that decides whether
`[LJ-1.617]`'s question is worth anything.**

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
**If the tree already has it at one α, far less, and I would rather be wrong
that way than fund a rebuild.** Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether a pairing at one α exists untruncated anywhere.

    -- any existing pairing at ONE infinite ordinal, re-ascribed as a Σ,
    -- TYPE ONLY, capped

**Do this FIRST, by grep, then typecheck it alone.** ESTIMATE: one grep and
about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS INGREDIENT (iii) AT THE GRAIN THE TREE SPENDS IT**, and with
`[LJ-1.613]`'s (i) and (ii), `[LJ-1.601]` and `[LJ-1.608]`'s (iv) and
`[LJ-1.600]`'s (v), the `class-pred` formula would be complete.

**A NO-GO SHOWING THE CIRCLE REACHES ONE α TOO CLOSES THE LAST CHEAP ROUTE**,
and then the new object `[LJ-1.607]` named is the only one left, which is worth
knowing before it is funded.

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
  changed_files_none = ["agents/tasks/LJ-1-618/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-618/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-618/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-618/Probe618.agda"]
  changed_files_none = ["agents/tasks/LJ-1-618/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-618/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 179.717)
- CANDIDATE archive/dev/JOURNAL.md  (score 166.983)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 161.818)
- CANDIDATE archive/dev/DD-archived.md  (score 132.328)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 125.196)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 66.397)
- CANDIDATE dev/literature/devlin-II5.md  (score 59.937)
- CANDIDATE dev/literature/digest.md  (score 40.422)
- CANDIDATE dev/literature/terms-2026-08.md  (score 37.895)
- CANDIDATE dev/literature/geology.md  (score 35.648)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
