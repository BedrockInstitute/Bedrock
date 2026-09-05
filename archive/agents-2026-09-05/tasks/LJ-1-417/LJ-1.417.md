# LJ-1.417: the rank becomes an injection into an ordinal, untruncated

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-417/Probe417.agda`, at a GENERIC small
type `A` with a GENERIC well-order on it.

    swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))

**THERE IS NO `∥ ∥₁` ANYWHERE IN THAT TYPE. THAT IS THE WHOLE TASK.** The
campaign has spent five dispatches on one untruncation and refuted every route
(`agents/tasks/LJ-1-391/lj-1.391-report.md:33-38`). This term needs no
untruncation, because nothing is selected: the rank is computed and the bound
is a pair.

**TAKE THE RANK AS A MODULE HYPOTHESIS. DO NOT REBUILD IT.** Take
`swo-rank`, `swo-rank-ord` and `swo-rank-mono` at `[LJ-1.416]`'s types, as bare
module hypotheses. Do not import `Probe416`. **If `[LJ-1.416]` returned NO-GO,
this task still runs**, because it measures whether the rank is ENOUGH, which
is a separate question from whether the rank is buildable.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-417/Probe417.agda::swo-into-ord"]

## SCOPE (write)
- agents/tasks/LJ-1-417/Probe417.agda
- agents/tasks/LJ-1-417/lj-1.417-report.md

## PREMISES
- `boundingOrd` returns the bound, its ordinal certificate and the membership law, as a genuine pair. Basis: src/L/Ordinal.lagda.md:155
- The ordinals of this chapter are the ambient ones. Basis: src/L/Ordinal.lagda.md:59
- `SWO` carries `tri∙`, so two distinct carrier elements are ordered one way or the other. Basis: src/L/WellOrder/Base.lagda.md:104
- `SWO` carries `irr∙`, so no element is below itself, which is what turns monotonicity into injectivity. Basis: src/L/WellOrder/Base.lagda.md:105
- Membership in the ambient hierarchy is irreflexive, which is the other half of the injectivity argument. Basis: src/V/Hierarchy.lagda.md:155
- The campaign's untruncation routes are refuted, so a route that needs none is the finding. Basis: agents/tasks/LJ-1-391/lj-1.391-report.md:38
- The consumer's target is a bare injection into a member type and carries no truncation. Basis: src/L/StageCardinal.lagda.md:565
- `boundingOrd` is applied to a member type of a stage already, so the small-index shape is delivered. Basis: src/L/Reflect.lagda.md:447

## WHAT IS DELIVERED ALREADY

**THE BOUND IS A PAIR AND NOT A TRUNCATED EXISTENCE**, and the chapter says so
in its own prose at `src/L/Ordinal.lagda.md:155`. That is the fact the whole
route turns on. Every other selection in this campaign arrived truncated.

**THE THREE ORDER FIELDS.** `tri∙`, `irr∙` and `trans∙` are record fields, so
they cost nothing to obtain.

## WHAT IS MISSING

**THE STEP FROM A MONOTONE MAP TO AN EMBEDDING.** Nothing in the tree derives
injectivity from order-monotonicity. It is three lines of trichotomy, and this
task writes them.

## THE REASONING

**INJECTIVITY IS TRICHOTOMY PLUS IRREFLEXIVITY, AND IT IS NOT AN INDUCTION.**
Given `swo-rank a ≡ swo-rank b`, split with `tri∙ a b`. In the case `a <∙ b`,
`swo-rank-mono` gives `⟨ swo-rank a ∈ˢ swo-rank b ⟩`, and the equality turns
that into a membership of an ordinal in itself, which `∈-irrefl` refutes. The
case `b <∙ a` is the mirror. The remaining case is `a ≡ b`, which is the goal.

**THE BOUND COMES FROM `boundingOrd` APPLIED TO THE RANK ITSELF.** Take
`boundingOrd A swo-rank swo-rank-ord`. Its third component says every
`swo-rank a` is a member of `β`, which is exactly the codomain membership the
embedding needs. **`A` is small, so this application is legal. That is the
premise `[LJ-1.416]` measures and this task assumes.**

**THE EMBEDDING, NOT MERELY AN INJECTION.** The target `↪` is the tree's
embedding type. An injection of sets into a member type is an embedding when
the codomain is a set. Say in the report which lemma you used to promote the
injective function to `↪`, and cite it at `file:line`. **If the promotion needs
a fact the tree does not carry, that is a finding and you state it as a type.**

**W2 (DD4).** Generic in `A` and in `w`. Name no stage and no cardinal.
`[LJ-1.418]` does the instantiation.

**W3, THE WIDEST UNMEASURED TERM.**

    rank-inj : (a b : A) → swo-rank a ≡ swo-rank b → a ≡ b

**State it alone, prove it, and report its code lines before you assemble the
Sigma.** ESTIMATE: about 8 code lines. BASIS: it is one `tri∙` split with two
symmetric `∈-irrefl` refutations, which is the shape `κ-min-at` already spends
in one line at `src/L/Cardinal.lagda.md:145`. ESTIMATE for the whole obligation:
about 25 code lines. BASIS: the same, plus the `boundingOrd` application and the
embedding promotion. **Comparables of SHAPE and never of size.**

**D-10.** Do not weaken `↪` to a bare function with an injectivity proof if the
promotion fails. State the gap and stop. The consumer's type is `↪`
(`src/L/StageCardinal.lagda.md:565`) and a weaker term does not plug in.

## WHAT GO AND NO-GO EACH EARN

**A GO DELIVERS, AT A GENERIC WELL-ORDERED SMALL CARRIER, AN UNTRUNCATED
INJECTION INTO AN ORDINAL.** That is the shape the whole campaign has been
unable to obtain by any other route.

**A NO-GO EARNS THE STEP THAT WILL NOT CLOSE, AT `file:line`.** If the
embedding promotion is the wall, name the missing fact as a type. **A stated
NO-GO is a full return.**

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 200.392)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 196.765)
- CANDIDATE archive/dev/JOURNAL.md  (score 193.576)
- CANDIDATE dev/ARCHIVE.md  (score 154.902)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 146.716)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 89.634)
- CANDIDATE dev/literature/devlin-II5.md  (score 69.295)
- CANDIDATE dev/literature/terms-2026-08.md  (score 55.467)
- CANDIDATE dev/literature/geology.md  (score 49.581)
- CANDIDATE dev/literature/digest.md  (score 44.130)

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
  changed_files_any = ["agents/tasks/LJ-1-417/Probe417.agda"]
  changed_files_none = ["agents/tasks/LJ-1-417/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-417/review-of-*.md"]

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
