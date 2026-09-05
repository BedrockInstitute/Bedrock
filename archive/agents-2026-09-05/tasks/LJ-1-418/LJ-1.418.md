# LJ-1.418: the stage injects into an ordinal, at EVERY ordinal, with no pairing

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-418/Probe418.agda`.

    stage-into-bound : (α : S) → IsOrd α
                     → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))

**AT EVERY ORDINAL, WITH NO `Init`, NO BAND AND NO INFINITENESS HYPOTHESIS.**
The delivered route needs all three. This one needs none, because `orderAt` is
a well-order at EVERY ordinal and not only at the site bound.

**TAKE `[LJ-1.417]`'s TERM AS A MODULE HYPOTHESIS.** Take `swo-into-ord` at
`[LJ-1.417]`'s type. Do not import `Probe417` and do not rebuild the rank.
**If `[LJ-1.417]` returned NO-GO, this task still runs**, because it measures
whether the tower's own order can be fed to that term at all, which is a
separate question.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-418/Probe418.agda::stage-into-bound"]

## SCOPE (write)
- agents/tasks/LJ-1-418/Probe418.agda
- agents/tasks/LJ-1-418/lj-1.418-report.md

## PREMISES
- `orderAt` is a strict well-order on a stage's members at EVERY ordinal, and it is not restricted to the site bound. Basis: src/L/Choice/Step.lagda.md:730
- `carry` moves a well-order from the pair form of a stage's members to the small member type. Basis: src/L/Choice/Step.lagda.md:272
- The pair form of a set's members sits at `ℓ-suc ℓ` and is NOT small. Basis: src/L/Choice/Step.lagda.md:217
- The small member type IS accepted as a `boundingOrd` index, and the tree already does it. Basis: src/L/Reflect.lagda.md:447
- The tower instantiates the well-order chapter at order level `ℓ-suc ℓ`. Basis: src/L/Choice/Step.lagda.md:58
- The consumer wants an injection from the stage's member type into a member type, with no truncation. Basis: src/L/StageCardinal.lagda.md:565
- The only delivered use of the tower's order names one ordinal, the site bound, so the generality below is not exercised anywhere yet. Basis: src/L/Cardinal.lagda.md:195
- The ambient least cardinal's arrow is truncated at its definition site, and this route does not pass through it. Basis: src/L/Cardinal.lagda.md:133

## WHAT IS DELIVERED ALREADY

**THE ORDER, AT EVERY ORDINAL.** `orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))`
at `src/L/Choice/Step.lagda.md:730`. It is built by `∈-induction` over the
ordinals, so its generality is real and not an accident of a statement.

**THE CARRIER BRIDGE.** `carry` at `src/L/Choice/Step.lagda.md:272` takes
`SWO (Mem A)` to `SWO ⟪ A ⟫`. **That is the step that makes the carrier SMALL**,
and without it `boundingOrd` cannot be reached at all, because `Mem` is at
`ℓ-suc ℓ` (`src/L/Choice/Step.lagda.md:217`).

## WHAT IS MISSING

**NOBODY HAS FED `orderAt` TO ANYTHING OUTSIDE THE SITE BOUND.** The one
delivered consumer names `SiteBound.β` (`src/L/Cardinal.lagda.md:195`). This
task uses the order at a generic `α`, which the statement already permits.

## THE REASONING

**THE COMPOSITION IS THREE STEPS AND EACH IS DELIVERED OR HYPOTHESIZED.**

1. `orderAt α oα : SWO (Mem (Lset α))`, delivered.
2. `carry (Lset α) (orderAt α oα) : SWO ⟪ Lset α ⟫`, delivered. The carrier is
   now the small member type.
3. `swo-into-ord` at `A := ⟪ Lset α ⟫`, hypothesized from `[LJ-1.417]`.

**THE LEVEL IS THE ONE THING TO WATCH, AND IT IS WHY STEP 2 EXISTS.** `carry`
changes the CARRIER's level and leaves the ORDER's level alone. So the order
stays at `ℓ-suc ℓ` while the carrier drops to `ℓ`. **Report both levels as you
measured them and say whether `[LJ-1.417]`'s hypothesis accepted them
unchanged.** If it did not, name the mismatch as a type. **That mismatch, if it
exists, is the whole finding of this task.**

**WHAT THIS TERM DOES NOT CLAIM.** It gives SOME ordinal `β`, not `α`. It does
not say `β` is small enough for anything. **Do not state a bound relating `β`
and `α` and do not attempt one.** `[LJ-1.419]` measures that, and a task that
smuggles it in has changed its own obligation.

**W2 (DD4).** Generic in `α`. Name no band, no cardinal and no numeral. Do not
carry `α₀`, `sucV α₀` or `ω` into the telescope: none of the three is needed.

**W3, THE WIDEST UNMEASURED TERM.**

    carry-at-generic : (α : S) → IsOrd α → SWO ⟪ Lset α ⟫

**State it alone, run it, and report its wall time and its code lines BEFORE
you compose anything.** The risk is that `carry` and `orderAt` compose only
under a hypothesis the site bound supplies silently. ESTIMATE: about 4 code
lines. BASIS: it is one application of each, and both are delivered. ESTIMATE
for the whole obligation: about 15 code lines. BASIS: the same plus the
hypothesis application. **Comparables of SHAPE and never of size.**

**MEASURE THE COST AND REPORT IT.** `orderAt` is `opaque`
(`src/L/Choice/Step.lagda.md:729`). Say whether you had to unfold it, and what
that cost. LESSONS P-l and P-y are in your laws block.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS AN UNTRUNCATED INJECTION FROM EVERY STAGE INTO AN ORDINAL IN THE
TREE, WITH NO PAIRING.** The consumer's parameter `sq` exists only to build
such an arrow. **A GO therefore says the parameter may be unnecessary**, and
that is the measurement `[LJ-2.5]` asks for.

**A NO-GO EARNS THE COMPOSITION THAT WILL NOT CLOSE, AT `file:line`.** If
`carry` cannot be applied at a generic ordinal, name the hypothesis it wants.
**A stated NO-GO is a full return** and it closes the route in three dispatches
rather than four.

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 193.884)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 189.609)
- CANDIDATE archive/dev/JOURNAL.md  (score 166.245)
- CANDIDATE dev/ARCHIVE.md  (score 158.143)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 135.549)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 71.514)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 66.821)
- CANDIDATE dev/literature/terms-2026-08.md  (score 58.458)
- CANDIDATE dev/literature/geology.md  (score 44.544)
- CANDIDATE dev/literature/digest.md  (score 43.517)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-418/Probe418.agda"]
  changed_files_none = ["agents/tasks/LJ-1-418/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-418/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

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
