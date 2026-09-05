# LJ-1.436: run the stage-cardinal induction at a TRUNCATED conclusion

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-436/Probe436.agda`:

    step-trunc : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ) → P! α

where `P!` is the chapter's own induction motive
(`src/L/StageCardinal.lagda.md:530-532`) with ONE truncation added around its
Sigma and nothing else changed:

    P! : S → Type (ℓ-suc ℓ)
    P! α = IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
         → ∥ Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
               ((u v : ⟪ Lset α ⟫) → f u ≡ f v → u ≡ v) ∥₁

ONE module hypothesis, and it is the truncated square law at the type
`[LJ-1.407]` DELIVERED, taken from that task's PROBE and never from its brief
(`agents/tasks/LJ-1-407/Probe407.agda:262-265`):

    sq-trunc : (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁

**NO OTHER HYPOTHESIS.** No pairing as data, no injection as data, no choice
principle, no new postulate.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-436/Probe436.agda::step-trunc"]

## SCOPE (write)
- agents/tasks/LJ-1-436/Probe436.agda
- agents/tasks/LJ-1-436/lj-1.436-report.md
- agents/tasks/LJ-1-436/review-of-step-trunc.md

## PREMISES
- The chapter's induction motive is a Sigma and not a truncation. Basis: src/L/StageCardinal.lagda.md:530
- The step function is the whole content of the induction, and the conclusion is one application of it. Basis: src/L/StageCardinal.lagda.md:561
- The conclusion of the induction is that step under an ∈-induction. Basis: src/L/StageCardinal.lagda.md:566
- The step spends the pairing at ONE ordinal, its own. Basis: src/L/StageCardinal.lagda.md:283
- The step spends the induction hypothesis through a FAMILY over the members of that ordinal. Basis: src/L/StageCardinal.lagda.md:534
- That family is the argument the limit step consumes. Basis: src/L/StageCardinal.lagda.md:396
- One case of the family reads the induction hypothesis at a member. Basis: src/L/StageCardinal.lagda.md:557
- The finite case of the family needs no induction hypothesis at all. Basis: src/L/StageCardinal.lagda.md:548
- `[LJ-1.407]` delivers the truncated square law with NO residue, at that same band. Basis: agents/tasks/LJ-1-407/lj-1.407-report.md:18
- Its delivered term is a family of truncations and not a truncated family. Basis: agents/tasks/LJ-1-407/Probe407.agda:262
- `[LJ-1.391]` measured the POINTWISE untruncation and named the missing principle a `2-Constant` endomap. Basis: agents/tasks/LJ-1-391/lj-1.391-report.md:38
- `[LJ-1.408]` refuted a pairing read twice under two truncations, which is why one opened witness per step is the shape to try. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:26
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE UNTRUNCATED INDUCTION.** `Upper.step` and `Upper.stage-card-upper` are
green in the tree (`src/L/StageCardinal.lagda.md:561-566`), with the pairing as a
module parameter.

**THE TRUNCATED SQUARE LAW.** `[LJ-1.407]`, GO, no residue.

**THE PLUMBING THE STEP NEEDS.** `limit-step` (`:396`), `fin-inj` (`:488`),
`Emb` (`:504`), `WOEmb` (`:518`) and `comp-inj` (`:500`) are all in the chapter
and none of them mentions the motive.

## WHAT IS MISSING

**THE CAMPAIGN HAS ONLY EVER TRIED TO UNTRUNCATE THE INPUT.** `[LJ-1.391]`,
`[LJ-1.422]`, `[LJ-1.424]` and `[LJ-1.431]` all ask for a witness as data.
**Nobody has asked whether the CONSUMER can be run with a truncated conclusion
instead**, which needs no untruncation anywhere.

The answer is not obvious in either direction, and that is why it is worth one
dispatch:

- The step's goal becomes an hProp, so `PT.rec` may open `sq-trunc` ONCE per
  step, and the two readings `[LJ-1.408]` refuted never arise.
- **AGAINST IT:** the step spends its induction hypothesis through `branch`
  (`src/L/StageCardinal.lagda.md:534-536`), which returns a FUNCTION over
  `⟪ α ⟫`. A family of truncated values is not a truncated family, and the tree
  has no principle that swaps them. **This task measures whether that Pi is
  really in the way.** It does not repair it.

**THIS TASK DECIDES WHICH.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, the type of
`branch` and the type `limit-step` demands of its last argument. State in one
sentence whether the truncation can pass through that Pi. **If you can state
that it cannot, say so, write the W3 term, and stop: that is a full return.**

**STEP ONE, W3, THE BRANCH FAMILY.** See below. Typecheck it ALONE.

**STEP TWO, THE OBLIGATION.** Only if step one closes. Rebuild the spine in the
probe: import `L.StageCardinal` and use `limit-step`, `fin-inj`, `Emb`, `WOEmb`
and `comp-inj` from it, restate `P!`, and write `step-trunc`.

**A REQUIRED REPORT SECTION, `## WHO OWES WHAT`.** `[LJ-1.435]` owes a limit step
that consumes a POINTWISE truncated branch family. **Do not import its probe, do
not copy a type out of its brief, and do not assert its statement as a fact.** In
that section, name it, say what it owes, and say whether its REPORT is in your
tree today. A report you cannot open is a report you may not cite. **If your W3
term fails, say in one line that the repair is owed there, and stop.**

**A REQUIRED REPORT SECTION, `## THE FIRST TERM THAT NEEDS DATA`.** Name, at
`file:line` in `src/L/StageCardinal.lagda.md`, the FIRST term that does not
typecheck when the motive carries a truncation, and give the type it needs, as a
type. **If every term closes, write `NONE` under that heading and say so
plainly.** That named type is this task's deliverable to `[LJ-2.5]`, and it is
worth more than the term itself.

**W2 (DD4).** Generic in `α`. Do not fix a band ordinal, do not fix `α₀`, and do
not add an infiniteness hypothesis the chapter does not have.

**DO NOT EDIT `src/`.** Do not weaken `P!` to make it close. A motive that drops
injectivity, or that truncates a different Sigma, measures a different statement
and is a hollow GO of exactly the shape audit findings F1 and F3 measured
(`dev/pod/audit-2026-08-20.md:34`).

**W3, THE WIDEST UNMEASURED TERM.**

    branch-trunc :
        (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
        (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ)
      → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫

**THE PROBE.** Typecheck `branch-trunc` ALONE, with the obligation omitted,
before anything else. It is the chapter's `branch` (`:534-536`) with the motive
truncated and NOTHING else changed. **This one term decides the DIRECT route**:
if it closes, the whole induction closes at once. **If it does not close, that is
a full return and not a failure**, because the repair is not this task's: it is a
limit step that takes the family truncated POINTWISE, which is owed elsewhere and
which you may not assume. Report wall
seconds and peak RSS at the caliber the program set on your pane, one Agda
process, three forced rechecks, and the median. Quote the elaborator at
`file:line`. A heap event is a WALL event: report it and stop.

ESTIMATE for the Agda: about 70 code lines. BASIS:
`src/L/StageCardinal.lagda.md:530-566` is the motive, the family and the step in
37 lines, and the probe restates them with the truncation plus the imports and
one `PT.rec` per case. **Comparables of SHAPE and never of size, and nothing may
be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO ENDS THE UNTRUNCATION CAMPAIGN.** It says the stage-cardinal upper bound
holds in truncated form from `[LJ-1.407]` alone, with no arrow as data anywhere,
and every open task that hunts an untruncated arrow becomes optional. **Say that
plainly and do NOT claim the trophy**: the trophy needs the consumer of that
bound, which `[LJ-1.434]` measures separately.

**A NO-GO IS THE MEASUREMENT `[LJ-2.5]` ASKS FOR.** It names, as a type, the one
principle the architecture needs: a swap of a Pi and a truncation over the
members of an ordinal. Clause W1 says only a measurement changes the
architecture. This is that measurement, and a NO-GO delivers it in full.

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
  changed_files_any = ["agents/tasks/LJ-1-436/Probe436.agda"]
  changed_files_none = ["agents/tasks/LJ-1-436/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-436/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 151.700)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 117.216)
- CANDIDATE archive/dev/JOURNAL.md  (score 115.722)
- CANDIDATE dev/ARCHIVE.md  (score 113.313)
- CANDIDATE archive/dev/DD-archived.md  (score 104.125)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 71.041)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.046)
- CANDIDATE dev/literature/devlin-II5.md  (score 39.723)
- CANDIDATE dev/literature/digest.md  (score 33.538)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 25.113)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
