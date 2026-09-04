# LJ-1.769-SPLIT: Cy.push of matrix₃ at bound variables, no call site

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-769-SPLIT/Probe769Split.agda`:

    push-matrix3-at-vars :
      (x₁ x₂ x₃ : S)
      → ⟨ x₁ ∈ˢ HS.M ⟩ → ⟨ x₂ ∈ˢ HS.M ⟩ → ⟨ x₃ ∈ˢ HS.M ⟩
      → ⟨ (x₁ ∷ x₂ ∷ x₃ ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
      → ⟨ (HS.C.π x₁ ∷ HS.C.π x₂ ∷ HS.C.π x₃ ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

Transcribe `[LJ-1.769]`'s green Frame769 and HullHalf769. Start from Split4's `core` push. Drop `commute-from-reading`. Drop every application of the helper to `fst (val _)`. The body is `Cy.push P667.Δ₀-matrix₃ ((x₁ , m₁) ∷ (x₂ , m₂) ∷ (x₃ , m₃) ∷ []) rd`. Do not copy `Carry`. Do not inhabit `commute-from-reading`. Do not restore the pinned Sigma. Do not restore `amb`. Do not ascribe `conv0`. Do not hypothesise `Convert`. Do not inhabit `conv-at-Lδ`. Do not restore `mkWit`'s spelled codomain. Export `push-matrix3-at-vars` at the file's top level. Land nothing in `src/`.

Floor the helper first. Then rename to `.agda` and run. ONE Agda process, pane caliber, cap 1800 s.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-769-SPLIT` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-769-SPLIT/Probe769Split.agda::push-matrix3-at-vars"]

## SCOPE (write)
- agents/tasks/LJ-1-769-SPLIT/Probe769Split.agda
- agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md
- agents/tasks/LJ-1-769-SPLIT/review-of-push-matrix3-at-vars.md
- agents/tasks/LJ-1-769-SPLIT/runs/

## PREMISES

1. **THE FLOOR OF `commute-from-reading` IS GREEN.** The goal type is cheap. Basis: agents/tasks/LJ-1-769/lj-1.769-report.md:98
2. **`Cy.push` OF `matrix₃` WALLS WHEN THE MODULE STILL APPLIES TO `fst (val _)`.** Four shapes. Basis: agents/tasks/LJ-1-769/lj-1.769-report.md:10
3. **A NEXT BRIEF NEEDS VARIABLES AT THE CALL SITE, OR A NEW CROSSING.** Do not call `Cy.push` on `fst (val _)`. Basis: agents/tasks/LJ-1-769/lj-1.769-report.md:228
4. **`Carry.push` AT VARIABLE ENTRIES IS GREEN IN `Probe652`.** Whole file 4.96 s. Basis: agents/tasks/LJ-1-652/Probe652.agda:185

## MEASURED TODAY

- dependents: L.Hull => 2
- supply: push-matrix3-at-vars => 0

## WHAT IS DELIVERED ALREADY

Frame green. Hull half green. Floor of the Commute type green. `Carry.push` at variables green on a smaller formula. `push-matrix3-at-vars` has supply 0.

## THE REASONING

This is not a retry of `commute-from-reading`. The neighbour is `Cy.push` on `fst (val _)`. The obligation is that push at bound variables, with no call site in the file. Named reading about 8k tokens at 4 B per token: this brief; 769 report HEAD and section 5; Probe652.agda:185-192. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether `Cy.push` of `Δ₀-matrix₃` at bound variables checks at `-M4g` with no `fst (val _)` in the file. Estimate Probe652's 4.96 s if formula size does not bite; if it bites, the Split4 wall. Basis: agents/tasks/LJ-1-769/lj-1.769-report.md:225

## WHAT GO AND NO-GO EACH EARN

**GO** is `push-matrix3-at-vars` on the meter. Then a later brief applies this helper, abstract, to assemble `commute-from-reading`. **NO-GO** that is a heap wall means `matrix₃` walls at variables; do not assemble `commute-from-reading`. Do not shrink the formula to Probe652's. Do not restore `amb`. Do not write a `review-of` for a resource wall.

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
id = "transfer-park"
priority = 11
action = "park_and_split"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  heap_wall = false
  changed_files_any = ["agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-769-SPLIT/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-769-SPLIT/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-769-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-769-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-769-SPLIT/Probe769Split.agda"]
  changed_files_none = ["agents/tasks/LJ-1-769-SPLIT/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-769-SPLIT/review-of-*.md"]

[[branch]]
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 207.270)
- CANDIDATE archive/dev/DD-archived.md  (score 194.448)
- CANDIDATE archive/dev/PLAN-archived.md  (score 180.945)
- CANDIDATE archive/dev/STATUS-archived.md  (score 152.087)
- CANDIDATE archive/dev/TASKS-archived.md  (score 146.339)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 36.524)
- CANDIDATE dev/literature/primary-sources.md  (score 31.862)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 28.485)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 27.933)
- CANDIDATE dev/literature/devlin-errata.md  (score 27.617)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
