# LJ-1.419: does the rank route discharge the consumer WITHOUT the pairing parameter

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-419/Probe419.agda`, at a GENERIC band
`α₀` with its ordinal certificate as module parameters.

    upper-from-rank : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
                    → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫

**THERE IS NO `sq` IN THAT TELESCOPE AND THERE MUST NOT BE ONE. THAT IS THE
WHOLE TASK.** The type above is the consumer's own delivered statement,
verbatim (`src/L/StageCardinal.lagda.md:564-565`). The consumer reaches it
today only inside a module that takes the pairing `sq` as a parameter
(`src/L/StageCardinal.lagda.md:17-19`). **This task asks whether the pairing is
needed at all.**

**TWO MODULE HYPOTHESES, AND EXACTLY TWO.**

1. `stage-into-bound`, at `[LJ-1.418]`'s type.
2. **THE RESIDUE**, and it is the point of the task:

       bound-into-ord : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                      → (β : S) → IsOrd β → (⟪ Lset α ⟫ ↪ ⟪ β ⟫)
                      → ⟪ β ⟫ ↪ ⟪ α ⟫

Do not import `Probe416`, `Probe417` or `Probe418`. **Do not attempt the
residue.** State it, use it, and report the exact type you used.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-419/Probe419.agda::upper-from-rank"]

## SCOPE (write)
- agents/tasks/LJ-1-419/Probe419.agda
- agents/tasks/LJ-1-419/lj-1.419-report.md
- agents/tasks/LJ-1-419/review-of-bound-into-ord.md

## PREMISES
- The consumer's target is a bare injection from the stage's member type into the ordinal's, with no truncation. Basis: src/L/StageCardinal.lagda.md:565
- The consumer reaches that target by an induction over every band ordinal, so the statement must hold at each one. Basis: src/L/StageCardinal.lagda.md:566
- The consumer takes the pairing as a module parameter, so today the pairing is needed before the module opens. Basis: src/L/StageCardinal.lagda.md:17
- `[LJ-1.408]` refuted the truncated grade of that parameter, so the pairing must be DATA. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:25
- `[LJ-1.414]` measured the last open implication of the pairing route NOT decidable in this tree. Basis: agents/tasks/LJ-1-414/lj-1.414-report.md:20
- `[LJ-1.391]` refuted both untruncation routes for the pairing. Basis: agents/tasks/LJ-1-391/lj-1.391-report.md:38
- The tower's own order is a well-order at every ordinal, which is what the rank route consumes. Basis: src/L/Choice/Step.lagda.md:730
- The one delivered use of that order SELECTS with `leastOf` rather than computing. Basis: src/L/Cardinal.lagda.md:195
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE CONSUMER'S TARGET, AND ITS EXACT TYPE.** `stage-card-upper` at
`src/L/StageCardinal.lagda.md:564-565`. It is an `∈-induction` over the band, so
`[LJ-1.419]`'s term must hold at a generic `α` and not at a chosen one.

**THE PAIRING ROUTE'S VERDICT, IN FIVE MEASUREMENTS.** `[LJ-1.390]`,
`[LJ-1.391]`, `[LJ-1.408]`, `[LJ-1.413]` and `[LJ-1.414]` each measured one
part of it, and the last returned NOT DECIDABLE in this tree. **This task does
not re-open any of them.**

## WHAT IS MISSING

**NOBODY HAS ASKED WHETHER THE PAIRING IS NECESSARY.** Every dispatch since
`[LJ-1.384]` has asked how to BUILD it. The consumer's type is an injection into
an ordinal, and a pairing is one way to reach such an injection. **A rank is
another, and this task prices it against the same consumer.**

## THE REASONING

**THE COMPOSITION IS ONE STEP.** `stage-into-bound α oα` gives `β`, its ordinal
certificate and `⟪ Lset α ⟫ ↪ ⟪ β ⟫`. `bound-into-ord` turns that into
`⟪ β ⟫ ↪ ⟪ α ⟫`. Compose the two embeddings. **If embedding composition is not
in the tree, write it and say so: it is three lines.**

**WHY THE RESIDUE IS STATED IN THAT SHAPE AND NOT AS A CARDINALITY.** It takes
the embedding into `β` as a HYPOTHESIS, so it says「a bound that the stage
already injects into can be pulled back to `α`」, not「every ordinal injects into
`α`」, which is false. **A residue that is false measures nothing.** D-10 binds
you here: check the target's truth at this generality BEFORE you use it, and
record the corrected target beside the original if it is wrong.

**W2 (DD4).** Generic in `α`. The two hypotheses are generic. Name no cardinal
and no numeral except `ω`, which the consumer's own type names.

**W3, THE WIDEST UNMEASURED TERM, AND IT IS THE COMPARISON AND NOT THE CODE.**

    residue-vs-pairing

**This is the measurement `[LJ-2.5]` asks for, and it is written in PROSE in
your report, not in Agda.** After the term is green, write a section
`## THE TWO BILLS` that states, each with `file:line`:

1. What `bound-into-ord` demands, in one sentence.
2. What `sq` demands, in one sentence, from the five reports above.
3. **Whether the two are the same mathematical content in different clothes.**
   If the residue needs an order-type fact that itself needs a pairing, say so
   and the route is closed. If it does not, say what it needs instead.

ESTIMATE for the Agda: about 12 code lines. BASIS: it is two hypothesis
applications and one embedding composition, which is the shape `[LJ-1.413]`'s
case-four composition already spends at
`agents/tasks/LJ-1-413/Probe413.agda:106`. **Comparables of SHAPE and never of
size, and nothing may be funded against them.**

**CLOSE WITH THE CONSUMER CHECK.** Restate the consumer's target verbatim as
`ConsumerShape`, with no `sq` in scope, and discharge it with `upper-from-rank`,
the way `[LJ-1.407]` discharged its form at
`agents/tasks/LJ-1-407/Probe407.agda:273`. **A term that does not plug in has
not finished.**

## WHAT GO AND NO-GO EACH EARN

**A GO SAYS THE PAIRING PARAMETER IS REPLACEABLE, AND THAT IS THE `[LJ-2.5]`
WARRANT.** It would mean the campaign's whole measured wall sits on a route the
consumer does not require. Say in the report what `L.StageCardinal` would look
like with the parameter removed, and name the line that would change.

**A NO-GO IS WORTH AS MUCH AND MAY BE WORTH MORE.** If the residue reduces to
the pairing, then the pairing is NECESSARY and not merely convenient, and
`[LJ-1.414]`'s NOT DECIDABLE becomes a statement about the architecture and not
about one route. **That is the strongest possible input to `[LJ-2.5]`, and a
stated NO-GO is a full return.**

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 160.891)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 139.706)
- CANDIDATE archive/dev/JOURNAL.md  (score 130.662)
- CANDIDATE dev/ARCHIVE.md  (score 122.195)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 110.493)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.758)
- CANDIDATE dev/literature/devlin-II5.md  (score 43.075)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.762)
- CANDIDATE dev/literature/geology.md  (score 35.140)
- CANDIDATE dev/literature/digest.md  (score 34.040)

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
  changed_files_any = ["agents/tasks/LJ-1-419/Probe419.agda"]
  changed_files_none = ["agents/tasks/LJ-1-419/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-419/review-of-*.md"]

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
