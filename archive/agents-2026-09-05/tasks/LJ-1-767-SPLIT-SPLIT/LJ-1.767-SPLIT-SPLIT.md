# LJ-1.767-SPLIT-SPLIT: grounded-from-complete, reading the only packed factor

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-767-SPLIT-SPLIT/Probe767SplitSplit.agda`:

    grounded-from-complete :
      Completeness
      → ((a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ → IsOrd p → a ≡ Lset p)
      → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
      → ∥ Σ[ ca ∈ Code ] Σ[ cp ∈ Code ] Σ[ z ∈ S ]
           ⟨ (fst (val ca) ∷ fst (val cp) ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ ∥₁

Transcribe `VendorFrame.agda.txt` and `VendorHull.agda.txt`. Start from `VendorPack.agda.txt`. Pack only the reading. Do not pack `⟨ Lset δ ∈ˢ HS.M ⟩`, membership, or either code equation. The first factor is `conv0`; nothing further is real. `VendorS5.agda.txt` is that shape, green. Do not restore `mkWit`'s spelled codomain. Do not subst along the code equations. Do not ascribe `conv0`. Do not hypothesise `Convert`. Do not inhabit `conv-at-Lδ`. Take `Completeness` as a HYPOTHESIS. Export `grounded-from-complete` at the file's top level. Land nothing in `src/`.

Re-measure S5 at this site first. Floor the new type next. Then rename to `.agda` and run. ONE Agda process, pane caliber, cap 1800 s.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-767-SPLIT-SPLIT` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/Probe767SplitSplit.agda::grounded-from-complete"]

## SCOPE (write)
- agents/tasks/LJ-1-767-SPLIT-SPLIT/Probe767SplitSplit.agda
- agents/tasks/LJ-1-767-SPLIT-SPLIT/lj-1.767-SPLIT-SPLIT-report.md
- agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-grounded-from-complete.md
- agents/tasks/LJ-1-767-SPLIT-SPLIT/runs/

## PREMISES

1. **THE WALL IS THE FIRST FACTOR PLUS ANY FURTHER REAL COMPONENT.** Dropping membership did not move the wall. Basis: agents/tasks/LJ-1-767-SPLIT/lj-1.767-SPLIT-report.md:4
2. **GREEN IFF THE FIRST FACTOR IS A HOLE, OR IS THE ONLY REAL SLOT.** Basis: agents/tasks/LJ-1-767-SPLIT/lj-1.767-SPLIT-report.md:173
3. **THE NEXT TYPE DROPS THE FIRST FACTOR OR MAKES IT THE ONLY PACKED SLOT.** That is a type change. Basis: agents/tasks/LJ-1-767-SPLIT/lj-1.767-SPLIT-report.md:236
4. **UN-ASCRIBED `conv0` IS GREEN.** Basis: agents/tasks/LJ-1-764/lj-1.764-report.md:4
5. **`conv-at-Lδ` IS UNINHABITED.** Do not retry it. Do not retry `amb`. Basis: agents/tasks/LJ-1-765-SPLIT/lj-1.765-SPLIT-report.md:10

## MEASURED TODAY

- dependents: L.Hull => 2
- supply: grounded-from-complete => 0

## WHAT IS DELIVERED ALREADY

Frame and hull half green. Floor green. S5 greens with one real packed slot. A complete tuple under the two `PT.rec` binders walls. `grounded-from-complete` has supply 0.

## THE REASONING

This is not a retry of the 767-SPLIT packing. The neighbour is a real first factor with further real components. The obligation packs only the reading. Named reading about 12k tokens at 4 B per token: this brief; 767-SPLIT report HEAD and section 3; 764 report HEAD; 765-SPLIT report HEAD; VendorS5.agda.txt. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether `grounded-from-complete` at this Sigma checks at `-M4g` with the reading the only packed factor. Estimate S5 plus `conv0` in that slot. Basis: agents/tasks/LJ-1-767-SPLIT/lj-1.767-SPLIT-report.md:180

## WHAT GO AND NO-GO EACH EARN

**GO** is `grounded-from-complete` on the meter at this Sigma. Then a later brief prices `LsetGrounded` from this reading, without packing a second real factor under the two `PT.rec` binders. **NO-GO** that is a heap wall stops this Sigma at `-M4g`. Do not restore a second packed factor. Do not restore `mkWit`'s spelled codomain. Do not restore `amb`. Do not write a `review-of` for a resource wall.

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
  changed_files_any = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/lj-1.767-SPLIT-SPLIT-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-LJ-*-*.md"]

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
  changed_files_none = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/Probe767SplitSplit.agda"]
  changed_files_none = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-767-SPLIT-SPLIT/review-of-*.md"]

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
- CANDIDATE archive/dev/DD-archived.md  (score 201.814)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 186.667)
- CANDIDATE archive/dev/PLAN-archived.md  (score 182.886)
- CANDIDATE archive/dev/STATUS-archived.md  (score 147.504)
- CANDIDATE archive/dev/TASKS-archived.md  (score 140.747)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 39.658)
- CANDIDATE dev/literature/primary-sources.md  (score 29.138)
- CANDIDATE dev/literature/fine-structure.md  (score 27.947)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 26.321)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 25.783)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
