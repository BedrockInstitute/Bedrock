# LJ-1.430: select the least cardinal by the CODED predicate, on the AMBIENT carrier

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-430/Probe430.agda`, at a GENERIC L-element
`a : S` with `oa : IsOrd (fst a)`, at a GENERIC ordinal `γ` with `oγ : IsOrd γ`,
and with ONE bare module hypothesis `nonempty-coded`:

    kappaC-ord : IsOrd (fst κC)

where the selection is the ambient one of `src/L/Cardinal.lagda.md:116-117` with
its predicate replaced:

    CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
    CodedInjP' d = ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

    nonempty-coded : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' d ⟩ ∥₁

    selected = leastOf w lem CodedInjP' nonempty-coded
    κC       = upα (fst selected)

`w` is the sealed `ordSWO (sucV (fst a)) (suc-ord oa)` of
`src/L/Cardinal.lagda.md:90-92`, `upα` is that module's crossing at
`src/L/Cardinal.lagda.md:78`, and `upγ` is `SiteBound.up`'s one line
(`src/L/Cardinal.lagda.md:171`) restated at `γ` and `oγ`.

**THE CARRIER IS AMBIENT AND THE PREDICATE IS CODED. NO EXISTING SELECTION IN
THE TREE HAS THAT PAIR OF CHOICES.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-430/Probe430.agda::kappaC-ord"]

## SCOPE (write)
- agents/tasks/LJ-1-430/Probe430.agda
- agents/tasks/LJ-1-430/lj-1.430-report.md
- agents/tasks/LJ-1-430/review-of-kappaC-ord.md

## PREMISES
- The ambient selection runs over `⟪ sucV (fst α) ⟫` and its predicate is a TRUNCATED AMBIENT INJECTION at `hProp ℓ`. Basis: src/L/Cardinal.lagda.md:82
- Its well-order is `ordSWO` on that carrier, and it is sealed. Basis: src/L/Cardinal.lagda.md:90
- The selected index is a member of `sucV (fst α)`, and THAT is where the ambient site gets ordinality, in two lines. Basis: src/L/Cardinal.lagda.md:125
- `mem-ord` is the lemma those two lines spend. Basis: src/L/Ordinal.lagda.md:221
- The ambient payload stays truncated, and the chapter states the reason in its own comment. Basis: src/L/Cardinal.lagda.md:133
- The internal selection runs over `Mem (Lset β)` instead, and its predicate is the CODED existential at `hProp (ℓ-suc ℓ)`. Basis: src/L/Cardinal.lagda.md:239
- That internal selection delivers no ordinality: its predicate carries no `IsOrd` conjunct. Basis: src/L/Cardinal.lagda.md:240
- `[LJ-1.427]` asked for `IsOrd` of that internal selection and its instance took the `no-go-stated` row. Basis: dev/pod/transitions/2026-08.jsonl:502
- `leastOf` takes its predicate at an arbitrary level `ℓ''` and its `LEM` at the max of three. Basis: src/L/WellOrder/Base.lagda.md:158
- `InjCode` is four satisfaction facts about a SET and names no ambient function. Basis: src/L/Cardinal.lagda.md:223
- The crossing from a member of a stage to an L-element is generic in the ordinal. Basis: src/L/Cardinal.lagda.md:171
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**TWO SELECTIONS, AND EACH HAS EXACTLY ONE OF THE TWO PROPERTIES THE DESCENT
NEEDS.**

- **THE AMBIENT ONE** (`src/L/Cardinal.lagda.md:116-134`) selects over
  `⟪ sucV (fst α) ⟫`. Ordinality of the result is two lines, `mem-ord` along
  `member (sucV (fst α)) γ-card` (`:125-127`). **Its payload is an ambient
  injection and stays truncated** (`:133`).
- **THE INTERNAL ONE** (`src/L/Cardinal.lagda.md:235-263`) selects over
  `Mem (Lset β)`. **Its payload is a CODE**, which is the shape `[LJ-1.424]`
  untruncates. **Its result is not an ordinal**: `Good` (`:239-240`) has no
  `IsOrd` conjunct, and `[LJ-1.427]` measured that gap
  (`dev/pod/transitions/2026-08.jsonl:502`).

## WHAT IS MISSING

**THE THIRD SELECTION, WHICH IS NEITHER OF THE TWO.** Take the AMBIENT carrier,
so ordinality is free, and the CODED predicate, so the payload is untruncatable.
Nothing in `src/` makes that pair of choices, and no task of this campaign has
asked for it.

**WHAT COULD STOP IT IS A LEVEL, AND THAT IS WHY IT IS W3.** The ambient site
runs `leastOf w lem` with a predicate at `hProp ℓ`
(`src/L/Cardinal.lagda.md:82-83`). The coded existential is at `hProp (ℓ-suc ℓ)`
(`:239`). `leastOf` is polymorphic in that level (`src/L/WellOrder/Base.lagda.md:158`)
and its `LEM` argument is at the max of three levels. **Whether the chapter's own
`lem` covers that max, on this carrier, is not stated anywhere in the tree.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, the two-column
statement of what each existing selection gives and what it withholds, and name
the ONE thing this task could fail on. **If you cannot state it, do not write
Agda.**

**STEP ONE, W3, THE SELECTION.** Build `CodedInjP'` and apply
`leastOf w lem CodedInjP' nonempty-coded`, with `nonempty-coded` a bare module
hypothesis and the result DISCARDED. Nothing else in the file. This is the level
question and it is the whole risk.

**STEP TWO, THE OBLIGATION.** `IsOrd (fst κC)` is `mem-ord` along
`member (sucV (fst a)) (fst selected)`, which is the ambient site's own two lines
at `src/L/Cardinal.lagda.md:125-127`. **Report whether those two lines transfer
unchanged, and quote the elaborator if they do not.**

**`nonempty-coded` IS A HYPOTHESIS AND YOU DO NOT INHABIT IT.** `[LJ-1.429]` is
the task that pays it. **Do not import that task's probe, do not copy a type out
of its brief, and do not assert its statement anywhere in your report.** Name it
as owed, and say which task owes it.

**DO NOT REBUILD `LeastCardInjL` AND DO NOT WRITE INTO `src/`.** Seal what you
rebuild at the call site, as `[LJ-1.421]` does at `Probe421.agda:125-135`: an
unsealed `⟪ sucV (fst a) ⟫` comparison unfolds the union representation, and the
chapter records the cost in its own comment at `src/L/Cardinal.lagda.md:87-89`.

**W2 (DD4).** Generic in `a` and in `γ`. Name no cardinal, no band, no numeral
and no `ω`. This term must not know what `γ` is.

**W3, THE WIDEST UNMEASURED TERM.**

    coded-selects : Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodedInjP' d

**THE PROBE.** Typecheck `coded-selects` ALONE, result discarded, before you
write the obligation. Report wall seconds and peak RSS at the caliber the
program set on your pane, one Agda process, three forced rechecks, and the
median. **If the chapter's `lem` does not cover `leastOf`'s level at this
carrier and this predicate, that is the NO-GO and it closes this route in ONE
dispatch.** Print the level the elaborator asks for and the one it has, at
`file:line`. If it costs a heap event, that is a WALL event: report it and stop.

ESTIMATE for the Agda: about 35 code lines. BASIS: `src/L/Cardinal.lagda.md:82-127`
is the ambient selection with its seal and its ordinality in 46 lines, and this is
that block with one predicate replaced and the minimality clauses dropped.
**Comparables of SHAPE and never of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO REPAIRS `[LJ-1.427]`'s OBSTRUCTION AT ITS ROOT.** That task measured that
the internal least cardinal is not delivered as an ordinal, and named a corrected
`Good` with an added conjunct, which selects a DIFFERENT object. **This task adds
no conjunct.** It moves the carrier instead, and ordinality then comes from where
the ambient site already gets it. Say in the report what the selected `κC` would
still owe before it can serve as a descent target.

**A NO-GO IS WORTH AS MUCH.** A level refusal here says the coded predicate
cannot be selected on the ambient carrier at all, which is a fact about the two
towers and not about this task, and it is a first-class input to `[LJ-2.5]`.

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
  changed_files_any = ["agents/tasks/LJ-1-430/Probe430.agda"]
  changed_files_none = ["agents/tasks/LJ-1-430/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-430/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 127.211)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 114.440)
- CANDIDATE dev/ARCHIVE.md  (score 107.445)
- CANDIDATE archive/dev/JOURNAL.md  (score 101.424)
- CANDIDATE archive/dev/STATUS-archived.md  (score 80.212)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.697)
- CANDIDATE dev/literature/devlin-II5.md  (score 38.926)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.871)
- CANDIDATE dev/literature/geology.md  (score 26.543)
- CANDIDATE dev/literature/digest.md  (score 22.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
