# LJ-1.424: untruncate a CODED injection, the device the campaign never tried

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-424/Probe424.agda`, at a GENERIC pair of
L-elements `a b : S`, with `L.Cardinal`'s own site bound in scope
(`open SiteBound a`, `src/L/Cardinal.lagda.md:163`):

    coded-to-arrow : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁
                   → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

**FROM A TRUNCATED CODED GRAPH TO AN AMBIENT ARROW AS DATA.** The input is
truncated. The output is not. No hypothesis of this module may be an ambient
injection, truncated or otherwise.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-424/Probe424.agda::coded-to-arrow"]

## SCOPE (write)
- agents/tasks/LJ-1-424/Probe424.agda
- agents/tasks/LJ-1-424/lj-1.424-report.md
- agents/tasks/LJ-1-424/review-of-coded-to-arrow.md

## PREMISES
- `leastOf` returns a Sigma and not a truncation, so its output is DATA. Basis: src/L/WellOrder/Base.lagda.md:158
- The tree already spends `leastOf` as data at the ambient cardinal site. Basis: src/L/Cardinal.lagda.md:117
- That ambient site leaves its payload truncated, and the chapter says why in its own comment. Basis: src/L/Cardinal.lagda.md:133
- A selection over CODED graphs is delivered, with the stage well-order, and it returns three of the four conjuncts as data. Basis: src/L/Cardinal.lagda.md:195
- Its predicate carries three conjuncts. Basis: src/L/Cardinal.lagda.md:187
- `InjCode` carries a fourth, the range clause. Basis: src/L/Cardinal.lagda.md:228
- `leastOf` accepts a predicate at `hProp (ℓ-suc ℓ)`, and the chapter already builds one there. Basis: src/L/Cardinal.lagda.md:239
- The well-order the selection runs on is delivered at every ordinal. Basis: src/L/Choice/Step.lagda.md:730
- The read-off from a coded graph to a function with injectivity is delivered. Basis: src/L/CantorBernstein.lagda.md:33
- `_↪_` is exactly that pair. Basis: src/L/Cardinal.lagda.md:47
- `[LJ-1.411]` already measured this exact gap: the selection returns a graph and not an `InjCode`, and the read-off quantifies over `S` and names no stage. Basis: agents/tasks/LJ-1-411/lj-1.411-report.md:142
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**BOTH HALVES, AND NEITHER HAS EVER BEEN JOINED.**

- **THE SELECTION.** `module Canonical` (`src/L/Cardinal.lagda.md:182-211`)
  runs `leastOf (orderAt β oβ) lem` over the members of `Lset β` and returns
  `F₀`, `sv`, `dm` and `ij` as DATA (`:197-209`). `grep` finds no consumer of
  that module anywhere in `src/`.
- **THE READ-OFF.** `readL` (`src/L/CantorBernstein.lagda.md:33-39`) takes
  `Σ[ F ∈ S ] InjCode F a b` and returns the function and its injectivity,
  through `module Small`.

## WHAT IS MISSING

**ONE CONJUNCT AND ONE COMPOSITION.** `Canonical`'s predicate has three
conjuncts (`src/L/Cardinal.lagda.md:187-190`) and `InjCode` has four
(`src/L/Cardinal.lagda.md:224-228`). The fourth, the range clause, is the one
`readL` needs and the one the selection does not carry.

**THAT GAP IS ALREADY MEASURED AND NOBODY HAS CLOSED IT.**
`agents/tasks/LJ-1-411/lj-1.411-report.md:142-146` reads: `Canonical.chosen`
「selects a graph at `SiteBound.β`, not an `InjCode`」, and `readL`
「quantif(ies) over `S` and name(s) no stage」. This task is that one sentence
turned into a term.

## THE REASONING

**D-10, BEFORE ANY AGDA. WHY THIS SITE IS NOT THE SITE THAT FAILED.** The
ambient selection at `src/L/Cardinal.lagda.md:117` chooses an index and its
payload stays truncated, and the chapter states the reason at `:133`: the
payload is itself an injection, which is not an hProp. **The coded site is a
different shape. There the payload IS the index**, a member of `Lset β`, and
the predicate on it is a satisfaction fact, which is an hProp by construction.
Write that difference out in the report before you write Agda. If you cannot
state it, do not proceed.

**STEP ONE, THE SELECTION.** Rebuild `Canonical`'s `Good`
(`src/L/Cardinal.lagda.md:187-190`) in the probe with the range clause of
`src/L/Cardinal.lagda.md:228` as a FOURTH conjunct, at `hProp (ℓ-suc ℓ)`, the
level `src/L/Cardinal.lagda.md:239` already uses. The range clause is a Pi into
a proposition, so give it its `isProp` witness rather than asserting one. Feed
it the same `leastOf (orderAt β oβ) lem` the chapter feeds
(`src/L/Cardinal.lagda.md:195`).

**STEP TWO, THE READ-OFF.** Apply `readL` (`src/L/CantorBernstein.lagda.md:33`)
to the four conjuncts the selection returned. **Say in the report whether its
result is `_↪_` definitionally, at `src/L/Cardinal.lagda.md:47-48`, or whether
one repackaging is needed, and quote the line.**

**DO NOT REBUILD `Small`, THE GRAPH READBACK, OR ANY CODING PRIMITIVE.** The
chapter warns that an unsealed `Small` application exhausts an 8 GB heap
(`src/L/InjChain.lagda.md:550-551`). `readL` is a top-level function that
already carries that application, so applying it costs one call. Importing
`L.CantorBernstein` pulls `L.GCH` and `L.Cardinal` with it: **report the import
cost as a plain wall figure**, separately from W3.

**W2 (DD4).** Generic in `a` and in `b`. Name no cardinal, no band, no numeral
and no ordinal. This term must not know what `b` is.

**W3, THE WIDEST UNMEASURED TERM.**

    good-four-selects

**THE PROBE.** Typecheck the FOUR-conjunct `Good` and the `leastOf` application
ALONE, with the read-off omitted and the result discarded, before you write
step two. Report wall seconds and peak RSS at the caliber the program set on
your pane, one Agda process, three forced rechecks, and the median. **If the
fourth conjunct does not fit `leastOf`'s level, or the range clause has no
`isProp` witness at that level, that is the NO-GO and it closes this route in
ONE dispatch.** Say which, at the elaborator's own error text and `file:line`.
If it costs a heap event, that is a WALL event: report it and stop.

ESTIMATE for the Agda: about 30 code lines. BASIS: `src/L/Cardinal.lagda.md:182-211`
is `Canonical` in 30 lines, and this is that module with one conjunct added plus
a two-line composition. **Comparables of SHAPE and never of size, and nothing
may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO REFUTES A STANDING ARCHITECTURE SENTENCE.** `[LJ-1.422]` returned NO-GO
on the untruncated arrow and named the missing device as「a well-order on the
injections」, absent from the tree. A GO here says the tree untruncates a CODED
injection with the well-order it DOES have, so the missing device is not a
well-order at all: it is one constructible graph. Name in the report what the
input `∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁` would still cost.

**A NO-GO IS WORTH AS MUCH.** It puts a second, independent measurement behind
`[LJ-1.422]`'s sentence, at the one device that report never examined, and that
is a first-class input to `[LJ-2.5]`.

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
  changed_files_any = ["agents/tasks/LJ-1-424/Probe424.agda"]
  changed_files_none = ["agents/tasks/LJ-1-424/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-424/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 215.673)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 183.952)
- CANDIDATE archive/dev/JOURNAL.md  (score 177.512)
- CANDIDATE dev/ARCHIVE.md  (score 155.583)
- CANDIDATE archive/dev/PLAN-archived.md  (score 144.313)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 102.201)
- CANDIDATE dev/literature/devlin-II5.md  (score 63.989)
- CANDIDATE dev/literature/digest.md  (score 47.531)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.315)
- CANDIDATE dev/literature/geology.md  (score 39.567)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
