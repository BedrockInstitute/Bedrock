# LJ-1.429: the identity code, at a bound built FROM the graph

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-429/Probe429.agda`, at a GENERIC L-element
`a : S`:

    id-code-wide : ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a a ∥₁

where `γ` is the ordinal this task DEFINES,

    G  = InclGraph.G a a (λ _ h → h)            -- the identity graph on a
    γ  = bound2 β (sucV (stage (fst G) (snd G))) oβ (suc-ord (stage-ord _ _)) .fst

with `β` and `oβ` from `open SiteBound a` (`src/L/Cardinal.lagda.md:163`), and
`upγ : Mem (Lset γ) → S` the same crossing `SiteBound.up` writes at
`src/L/Cardinal.lagda.md:171`, restated at `γ` and `oγ`.

**THE BOUND IS DERIVED FROM THE GRAPH, NOT GUESSED AHEAD OF IT.** That is the
whole move of this task, and it is not what `[LJ-1.425]` was asked to do.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-429/Probe429.agda::id-code-wide"]

## SCOPE (write)
- agents/tasks/LJ-1-429/Probe429.agda
- agents/tasks/LJ-1-429/lj-1.429-report.md
- agents/tasks/LJ-1-429/review-of-id-code-wide.md

## PREMISES
- `[LJ-1.425]` asked for the same existence claim at `SiteBound`'s own `β` and its instance took the `no-go-stated` row. Basis: dev/pod/transitions/2026-08.jsonl:488
- The site bound is `bound2 ω (stage a p)`, so it contains `ω` and `stage a p` and nothing was ever proved about a graph's stage against it. Basis: src/L/Choice/Stage.lagda.md:366
- `bound2` returns an ordinal containing BOTH arguments, as a genuine pair and not a truncation. Basis: src/L/Ordinal.lagda.md:185
- Every L-element has a least stage, and it is a member of that stage. Basis: src/L/Stage.lagda.md:188
- That stage is an ordinal. Basis: src/L/Stage.lagda.md:185
- Membership in a smaller stage lifts to a larger one. Basis: src/L/Constructible.lagda.md:355
- `InclGraph D C` needs ONE argument, the subset witness, and carves the graph by one separation. Basis: src/L/InjChain.lagda.md:575
- The carved graph is an L-element. Basis: src/L/InjChain.lagda.md:479
- It exposes the first three `InjCode` conjuncts at `G ∷ D ∷ []`. Basis: src/L/InjChain.lagda.md:515
- It exposes the fourth, the range clause, valued in `C`. Basis: src/L/InjChain.lagda.md:544
- `InjCode` is exactly those four. Basis: src/L/Cardinal.lagda.md:223
- The crossing from a member of a stage to an L-element is one line and is generic in the ordinal. Basis: src/L/Cardinal.lagda.md:171
- `OrdIncl` is the only live consumer of `InclGraph`, and it demands a STRICT membership, so it cannot serve the identity. Basis: src/L/InjChain.lagda.md:604
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE GRAPH, WITH ALL FOUR CONJUNCTS, AND NOBODY HAS PLACED IT.**
`module InclGraph` (`src/L/InjChain.lagda.md:575-598`) takes exactly one
argument beyond its two sets, the subset witness
`(z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩`. At `D = C = a` that witness is
`λ _ h → h`. The module then delivers `sv` (`:518`), `ij` (`:525`), `dm`
(`:532`) and `ran` (`:544`) at `γI = G ∷ D ∷ []` (`:515`), and those four are
`InjCode G a a` term for term (`src/L/Cardinal.lagda.md:223-228`).

**THE PLACEMENT IMPLICATION IS ALSO DELIVERED.** `[LJ-1.425]` typechecked
`⟨ stage (fst G) (snd G) ∈ˢ β ⟩ → G ∈ Mem (Lset β)` green, out of `Lset-mono`
(`src/L/Constructible.lagda.md:355`) and `stage-mem` (`src/L/Stage.lagda.md:188`).
**What it could not pay was the premise.**

## WHAT IS MISSING

**A BOUND THAT CONTAINS THE GRAPH'S OWN STAGE.** `[LJ-1.425]` was asked for the
claim at `SiteBound`'s `β`, and `β` is fixed before the graph exists
(`src/L/Choice/Stage.lagda.md:366`). Its return names the corrected shape as a
stage above `sucV (sucV (sucV (stage a)))`, reached by pair arithmetic.

**THIS BRIEF ASKS FOR A DIFFERENT AND CHEAPER BOUND, AND IT IS THE POINT OF THE
TASK.** Do not compute where the pairs land. **Take the graph's own stage.** `G`
is an L-element (`src/L/InjChain.lagda.md:479`), so `stage (fst G) (snd G)`
exists and is an ordinal (`src/L/Stage.lagda.md:185`), and `G` is a member of
its own stage (`:188`). Then

    γ = bound2 β (sucV (stage (fst G) (snd G))) .fst

contains `β`, so nothing the site bound proves is lost, and contains
`sucV (stage G)`, so `stage G ∈ γ` follows by ONE step of ordinal transitivity
through `self∈sucV`. **No comparison with `StageBound`'s sealed `boundingOrd`
(`src/L/InjChain.lagda.md:75-93`) is needed, and that seal is what stopped
`[LJ-1.425]`.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, why this bound
is admissible where `SiteBound`'s is not, and state the ONE thing that could
still be false: that `bound2` needs `IsOrd` of both arguments and `oβ` plus
`suc-ord (stage-ord ...)` supply them. **If you cannot state that paragraph, do
not write Agda.**

**STEP ONE, THE GRAPH.** Instantiate `InclGraph a a (λ _ h → h)`
(`src/L/InjChain.lagda.md:575`). Do NOT go through `OrdIncl` (`:604`): it derives
its subset witness from a strict membership `⟨ fst D ∈ fst C ⟩`, and `a ∈ a` is
false. Report whether the four conjuncts come out at `G ∷ a ∷ []` with no
repackaging, and quote the line if one is needed.

**STEP TWO, THE BOUND AND THE MEMBERSHIP.** Build `γ` as above and discharge
`⟨ stage (fst G) (snd G) ∈ˢ γ ⟩`. That is W3 and it is the whole risk.

**STEP THREE, THE PACKAGING.** `up (fst G , m)` and `G` agree on `fst` and
differ only in the `isL` proof, which is a proposition. **Say in the report
whether the two are equal definitionally, or whether one `Σ≡Prop` step is
needed, and quote the elaborator.** Then truncate.

**DO NOT WIDEN `InternalLeastCard` AND DO NOT WRITE INTO `src/`.** This task
measures a bound. Nothing lands in a master.

**W2 (DD4).** Generic in `a`. Name no cardinal, no band, no numeral and no `ω`
of your own; the `ω` inside `stageBound` is the chapter's and you do not name it.

**W3, THE WIDEST UNMEASURED TERM.**

    stage-in-gamma : ⟨ stage (fst G) (snd G) ∈ˢ γ ⟩

**THE PROBE.** Typecheck `stage-in-gamma` ALONE, with the graph built and the
`InjCode` conjuncts omitted, before you write the obligation. Report wall
seconds and peak RSS at the caliber the program set on your pane, one Agda
process, three forced rechecks, and the median. **If `bound2` will not accept
`sucV (stage (fst G) (snd G))`, or the transitivity step does not close, that is
the NO-GO and it closes this route in ONE dispatch.** Say which, at the
elaborator's own error text and `file:line`. If it costs a heap event, that is a
WALL event: report it and stop.

ESTIMATE for the Agda: about 45 code lines. BASIS: `src/L/InjChain.lagda.md:575-598`
is `InclGraph` in 24 lines, and this task instantiates it once, adds one `bound2`
application, one transitivity step and one truncation. **Comparables of SHAPE and
never of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE ONE PREMISE THE CODED ROUTE HAS NEVER HAD.** Every coded
selection in `src/L/Cardinal.lagda.md` is guarded by a nonemptiness hypothesis
that nobody has ever discharged: `Canonical` at `:193` and `InternalLeastCard`
at `:242`, and `grep -rn "InternalLeastCard" src/` returns the definition only.
A GO here is the first witness any of them has had. Name in the report what the
selection at that bound would then cost.

**A NO-GO IS WORTH AS MUCH AND IT IS DECISIVE.** It says the tree cannot place
even the IDENTITY graph in any stage it can name, and that closes the coded
route for good, not only at `SiteBound`'s `β`. Name the exact term that failed
and say whether the obstruction is the seal at `src/L/InjChain.lagda.md:75-93`
or the ordinal arithmetic. That is a first-class input to `[LJ-2.5]`.

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
  changed_files_any = ["agents/tasks/LJ-1-429/Probe429.agda"]
  changed_files_none = ["agents/tasks/LJ-1-429/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-429/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 179.289)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 170.172)
- CANDIDATE archive/dev/JOURNAL.md  (score 159.561)
- CANDIDATE dev/ARCHIVE.md  (score 147.871)
- CANDIDATE archive/dev/DD-archived.md  (score 139.335)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.876)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.433)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.209)
- CANDIDATE dev/literature/digest.md  (score 38.562)
- CANDIDATE dev/literature/geology.md  (score 35.587)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
