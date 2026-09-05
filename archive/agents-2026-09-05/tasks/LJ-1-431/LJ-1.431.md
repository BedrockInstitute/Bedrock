# LJ-1.431: the arrow as DATA at the coded least cardinal

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-431/Probe431.agda`, at a GENERIC L-element
`a : S` with `oa : IsOrd (fst a)`, at a GENERIC ordinal `γ` with `oγ : IsOrd γ`,
and with ONE bare module hypothesis `nonempty-coded`:

    arrow-at-kappaC : ⟪ fst a ⟫ ↪ ⟪ fst κC ⟫

`κC` is the coded selection on the ambient carrier, rebuilt in this probe:

    CodedInjP' d = ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁
    selected     = leastOf w lem CodedInjP' nonempty-coded
    κC           = upα (fst selected)

**THE INPUT IS TRUNCATED AND THE OUTPUT IS NOT.** No hypothesis of this module
may be an ambient injection, truncated or otherwise.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-431/Probe431.agda::arrow-at-kappaC"]

## SCOPE (write)
- agents/tasks/LJ-1-431/Probe431.agda
- agents/tasks/LJ-1-431/lj-1.431-report.md
- agents/tasks/LJ-1-431/review-of-arrow-at-kappaC.md

## PREMISES
- `[LJ-1.424]` DELIVERED the untruncation of a coded injection, and its report is in this tree and reads GO. Basis: agents/tasks/LJ-1-424/lj-1.424-report.md:23
- The delivered term takes the truncated code and returns `_↪_` as data. Basis: agents/tasks/LJ-1-424/Probe424.agda:91
- It was proved at `SiteBound a`'s own `β` and at a GENERIC pair, so its second argument is free. Basis: agents/tasks/LJ-1-424/Probe424.agda:77
- Its read-off is `readL`, which quantifies over a bare `S` and names no stage. Basis: src/L/CantorBernstein.lagda.md:33
- `readL`'s result is `_↪_` definitionally. Basis: src/L/Cardinal.lagda.md:47
- The well-order the selection over `Mem (Lset γ)` needs is delivered at EVERY ordinal. Basis: src/L/Choice/Step.lagda.md:730
- The ambient carrier's own well-order is sealed, and the chapter records what unsealing costs. Basis: src/L/Cardinal.lagda.md:87
- The crossing from a member of a stage to an L-element is generic in the ordinal. Basis: src/L/Cardinal.lagda.md:171
- `InjCode` is four satisfaction facts about a SET. Basis: src/L/Cardinal.lagda.md:223
- The campaign's residue is ONE untruncated arrow at a named ordinal, and `[LJ-1.421]` says so in a delivered report in this tree. Basis: agents/tasks/LJ-1-421/lj-1.421-report.md:60
- The chapter warns that an unsealed `Small` application exhausts an 8 GB heap. Basis: src/L/InjChain.lagda.md:550
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE DEVICE, AND IT IS IN THIS TREE.** `[LJ-1.424]` returned GO
(`agents/tasks/LJ-1-424/lj-1.424-report.md:23`) on

    coded-to-arrow : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁
                   → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

at `agents/tasks/LJ-1-424/Probe424.agda:91-95`, generic in `a` and in `b`
(`:77`). That report is not NO-GO and it does not name its statement false.

## WHAT IS MISSING

**THE DEVICE AT A DIFFERENT BOUND, AND THE INPUT IT CONSUMES.**

1. `coded-to-arrow` was proved with `open SiteBound a`, so its `β` is
   `stageBound (fst a) (snd a) .fst` and nothing else. **This task needs the same
   device at an ARBITRARY ordinal `γ`.** `orderAt` is delivered at every ordinal
   (`src/L/Choice/Step.lagda.md:730`) and `readL` names no stage
   (`src/L/CantorBernstein.lagda.md:33`), so the restatement should be uniform.
   **Should be is not measured, and that is why it is W3.**
2. The input `∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a κC ∥₁` is exactly what
   the coded selection returns as the first half of `IsLeast`.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.424]` proved the device at ONE bound. C-42
says a measurement of one site does not measure another. Write in the report,
at `file:line`, which lines of `Probe424.agda:80-100` mention `β` and which are
free of it, and say what the restatement at `γ` therefore costs. **If you cannot
state it, do not write Agda.**

**STEP ONE, W3, THE DEVICE AT `γ`.** Restate `coded-to-arrow` at a generic
ordinal `γ` with `oγ`, with the four-conjunct `Good4` and the `isProp` witness
rebuilt from `agents/tasks/LJ-1-424/Probe424.agda:57-70`. Typecheck it ALONE,
applied to a bare truncated hypothesis, with the selection of step two omitted.

**STEP TWO, THE SELECTION AND THE JOIN.** Rebuild the coded selection on the
ambient carrier and feed `fst (snd selected)` to the device. Report whether the
two types meet with no repackaging, and quote the elaborator if they do not.

**`nonempty-coded` IS A HYPOTHESIS AND YOU DO NOT INHABIT IT.** `[LJ-1.429]` is
the task that pays it. **Do not import that task's probe, do not copy a type out
of its brief, and do not assert its statement anywhere in your report.** Name it
as owed, and say which task owes it. The same holds for `kappaC-ord`, which
`[LJ-1.430]` owes: **this task does not need it and must not assume it.**

**DO NOT REBUILD `Small` OR ANY CODING PRIMITIVE.** `readL` is a top-level
function that already carries that application, so applying it costs one call
(`src/L/InjChain.lagda.md:550-551` is the warning). Importing `L.CantorBernstein`
pulls `L.GCH` and `L.Cardinal` with it: **report the import cost as a plain wall
figure**, separately from W3.

**W2 (DD4).** Generic in `a` and in `γ`. Name no cardinal, no band, no numeral
and no `ω`.

**W3, THE WIDEST UNMEASURED TERM.**

    coded-to-arrow-at : (b : S)
                      → ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a b ∥₁
                      → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

**THE PROBE.** Typecheck `coded-to-arrow-at` ALONE, with the selection omitted,
before you write the obligation. Report wall seconds and peak RSS at the caliber
the program set on your pane, one Agda process, three forced rechecks, and the
median. **If the device does not restate at a bound that is not `stageBound`'s,
that is the NO-GO and it closes this route in ONE dispatch.** Name the term that
depended on `β` and quote the elaborator at `file:line`. If it costs a heap
event, that is a WALL event: report it and stop.

ESTIMATE for the Agda: about 40 code lines. BASIS: `agents/tasks/LJ-1-424/Probe424.agda:57-100`
is the device with its `isProp` witness in 44 lines, and this is that block with `β`
made a parameter plus one selection and one application. **Comparables of SHAPE and
never of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS AN UNTRUNCATED ARROW AT AN ORDINAL IN THE TREE FOR THE FIRST TIME.**
`[LJ-1.421]` names the campaign's residue as exactly one such arrow
(`agents/tasks/LJ-1-421/lj-1.421-report.md:60`) and `[LJ-1.422]` refused it at
the AMBIENT least cardinal. **A GO here does not discharge that residue**, because
the target is `κC` and not `κL`, and it must not be reported as if it did. Say in
the report exactly which of the two ordinals the arrow lands at, and what still
stands between the two.

**A NO-GO IS WORTH AS MUCH.** It says `[LJ-1.424]`'s device is tied to
`stageBound`'s bound, which would be a fact about the device and not about this
task, and it would make the widened bound of `[LJ-1.429]` useless. Name the tie
at `file:line`.

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
  changed_files_any = ["agents/tasks/LJ-1-431/Probe431.agda"]
  changed_files_none = ["agents/tasks/LJ-1-431/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-431/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 183.406)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 156.750)
- CANDIDATE dev/ARCHIVE.md  (score 142.489)
- CANDIDATE archive/dev/JOURNAL.md  (score 132.088)
- CANDIDATE archive/dev/STATUS-archived.md  (score 104.554)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 80.879)
- CANDIDATE dev/literature/devlin-II5.md  (score 53.744)
- CANDIDATE dev/literature/digest.md  (score 46.144)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.453)
- CANDIDATE dev/literature/geology.md  (score 36.209)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
