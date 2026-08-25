# LJ-1.425: unlock the internal least cardinal, with the identity graph

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-425/Probe425.agda`, at a GENERIC L-element
`κ : S` with its ordinal certificate `oκ` as module parameters, with
`L.Cardinal`'s own site bound in scope (`open SiteBound κ`,
`src/L/Cardinal.lagda.md:163`):

    internal-nonempty :
      ∥ Σ[ δ ∈ Mem (Lset β) ]
          ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ ∥₁

**THAT IS `InternalLeastCard.Selected`'s ONE HYPOTHESIS**, written out with
`Good` unfolded (`src/L/Cardinal.lagda.md:239-243`). Nothing else in that module
takes an argument.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-425/Probe425.agda::internal-nonempty"]

## SCOPE (write)
- agents/tasks/LJ-1-425/Probe425.agda
- agents/tasks/LJ-1-425/lj-1.425-report.md
- agents/tasks/LJ-1-425/review-of-internal-nonempty.md

## PREMISES
- `InternalLeastCard.Selected` takes exactly one hypothesis and delivers the internal least cardinal from it. Basis: src/L/Cardinal.lagda.md:243
- Its witness is a CODED injection, still truncated, and it is delivered the moment that hypothesis is paid. Basis: src/L/Cardinal.lagda.md:257
- The trophy statement `IsCardinalL` is defined against the same coded notion. Basis: src/L/Cardinal.lagda.md:231
- A constructible graph carved between two sets is delivered, by ONE separation and no replacement. Basis: src/L/InjChain.lagda.md:468
- It exposes all four `InjCode` conjuncts publicly. Basis: src/L/InjChain.lagda.md:598
- The range conjunct is where the subset witness is spent, and the chapter says the identity graph is the case that does not have it. Basis: src/L/InjChain.lagda.md:513
- Its bound is a SEALED `StageBound` over the pair family. Basis: src/L/InjChain.lagda.md:75
- The site bound is a different device: `stageBound`, above the set's own stage and above ω. Basis: src/L/Choice/Stage.lagda.md:366
- The chapter delivers one bridge from that bound down to members of members. Basis: src/L/Choice/Stage.lagda.md:370
- `up` lifts a member of `Lset β` to an L-element. Basis: src/L/Cardinal.lagda.md:171
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE GRAPH, AND IT IS GENERIC IN THE ORDINAL.** `module InclGraph D C sub`
(`src/L/InjChain.lagda.md:575-598`) carves the inclusion graph of `D` into `C`
by one separation and opens `Carve` publicly, so `sv` (`:518`), `ij` (`:525`),
`dm` (`:532`) and `ran` (`:544`) are all in scope. `module OrdIncl`
(`src/L/InjChain.lagda.md:604-607`) is its ordinal instance and needs `D ∈ C`.

**THE CONSUMER.** `InternalLeastCard` (`src/L/Cardinal.lagda.md:235`) has never
been instantiated. `grep` finds no application of `Selected` in `src/`.

## WHAT IS MISSING

**A `nonempty`, AND THE CHEAPEST ONE IS THE IDENTITY.** Take `δ := κ` and
`F :=` the inclusion graph of `κ` into `κ`. `OrdIncl` cannot serve it, because
it wants `D ∈ C` and here they are the same set. `InclGraph κ κ (λ _ z → z)`
can: the subset witness is the identity.

## THE REASONING

**D-10, BEFORE ANY AGDA.** The statement is an existence claim over a bounded
stage, and it is true only if BOTH `κ` and its identity graph really are
members of `Lset β`. Neither is free. **The two bounds in this task are built
by different devices and the tree states no comparison between them**: `β` is
`stageBound (fst κ) (snd κ) .fst` (`src/L/Cardinal.lagda.md:166`), while
`Carve`'s bound is a `boundingOrd` over the pair family, sealed opaque
(`src/L/InjChain.lagda.md:75-93`). **If the graph's bound does not sit under
`β`, the statement is false as written and you must say so and stop**, and the
report then names what a corrected statement would quantify over.

**BUILD THE TWO MEMBERSHIPS FIRST AND THE GRAPH SECOND.** The graph costs one
module application. The memberships are the task.

**DO NOT REBUILD THE CARVE, THE SEPARATION OR ANY CODING PRIMITIVE.** Apply
`InclGraph`. The chapter warns that an unsealed `Small` application exhausts an
8 GB heap (`src/L/InjChain.lagda.md:550-551`), and nothing here needs `Small`
at all: the four conjuncts are what this task returns, not a function.

**W2 (DD4).** Generic in `κ`. The ordinal certificate is a module parameter, as
`InternalLeastCard` states it (`src/L/Cardinal.lagda.md:235`). Name no cardinal,
no band and no numeral except `ω`, which `stageBound`'s own type names.

**W3, THE WIDEST UNMEASURED TERM.**

    graph-in-site-bound

**THE PROBE.** Typecheck the membership `⟨ fst G ∈ˢ Lset β ⟩` ALONE, with the
graph `G` taken as a bare module hypothesis and nothing carved, before you
apply `InclGraph`. Report wall seconds and peak RSS at the caliber the program
set on your pane, one Agda process, three forced rechecks, and the median.
**Report which delivered fact you spent to cross from one bound to the other,
at `file:line`, or that there is none.** If it costs a heap event, that is a
WALL event: report it and stop.

ESTIMATE for the Agda: about 20 code lines. BASIS: `src/L/InjChain.lagda.md:604-607`
is the whole ordinal-inclusion instantiation in 4 lines, and the comparable of
SHAPE for a stage-membership argument is `src/L/Cardinal.lagda.md:171-172`.
**Comparables of SHAPE and never of size, and nothing may be funded against
them.**

## WHAT GO AND NO-GO EACH EARN

**A GO UNLOCKS A MODULE THE TREE HAS NEVER RUN.** `InternalLeastCard.Selected`
then delivers `δᴸ` (`src/L/Cardinal.lagda.md:253`) and `δ-inj`
(`src/L/Cardinal.lagda.md:257`), a truncated CODED injection at the internal
least cardinal. That is the input `[LJ-1.424]` consumes, and it is delivered by
the tree rather than assumed. Name in the report what `δ-inj` costs to obtain
once this term is green.

**A NO-GO IS WORTH AS MUCH.** It names which of the two bounds fails to contain
the other, at the elaborator's own error text, and that prices the alternative:
re-carve the graph inside `Lset β` directly. Do not attempt that alternative in
this task.

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
  changed_files_any = ["agents/tasks/LJ-1-425/Probe425.agda"]
  changed_files_none = ["agents/tasks/LJ-1-425/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-425/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 186.726)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 159.505)
- CANDIDATE archive/dev/JOURNAL.md  (score 140.697)
- CANDIDATE dev/ARCHIVE.md  (score 137.271)
- CANDIDATE archive/dev/STATUS-archived.md  (score 109.607)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 69.216)
- CANDIDATE dev/literature/devlin-II5.md  (score 49.487)
- CANDIDATE dev/literature/terms-2026-08.md  (score 43.548)
- CANDIDATE dev/literature/geology.md  (score 41.437)
- CANDIDATE dev/literature/digest.md  (score 40.173)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
