# LJ-1.728-SPLIT: grounded-from-complete at heavy

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda`:

    grounded-from-complete :
      Completeness
      → ((a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ → IsOrd p → a ≡ Lset p)
      → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
      → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ Lset δ ∈ˢ HS.M ⟩
                    × ⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩) ∥₁

Transcribe `[LJ-1.728]`'s written term (`Probe728.agda.txt:196-210`). Import `[LJ-1.692]`'s `hull-convert-at-matrix`. Do not hypothesise `Convert`. Take `Completeness` as a HYPOTHESIS. Export the name at the file's top level. Land nothing in `src/`.

**FLOOR THE PROBE WITH ONE AGDA PROCESS AT THE PANE CALIBER BEFORE YOU CLAIM GO.**

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda::grounded-from-complete"]

## SCOPE (write)
- agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda
- agents/tasks/LJ-1-728-SPLIT/lj-1.728-SPLIT-report.md
- agents/tasks/LJ-1-728-SPLIT/review-of-grounded-from-complete.md
- agents/tasks/LJ-1-728-SPLIT/runs/

## PREMISES

1. **`[LJ-1.728]` DID NOT INHABIT THE NAME AT WIDE.** The term is written. The probe is `.agda.txt` because it cannot typecheck at `-M2g`. Basis: agents/tasks/LJ-1-728/lj-1.728-report.md:9
2. **THE WALL IS NOT CONVERT'S BODY.** Every walling run hole-shielded the conversion and still died. Basis: agents/tasks/LJ-1-728/lj-1.728-report.md:90
3. **THE FRAME WITH A HOLE BODY SITS AT 1.62 GB.** Membership adds 0.06 GB. Any shape that applies `hull-closed` and assembles the ambient slot exceeds 2 GB. Basis: agents/tasks/LJ-1-728/lj-1.728-report.md:19
4. **`[LJ-1.692]` INHABITS `Convert` BY CONSTRUCTION.** Basis: agents/tasks/LJ-1-692/Probe692.agda:63
5. **THE 718 CRITIC ALREADY NAMED A HEAVY RUN OF THIS COMPOSITION.** Basis: agents/tasks/LJ-1-718/review-of-LJ-1-718-1.md:103

## MEASURED TODAY

- dependents: L.Hierarchy => 7
- supply: grounded-from-complete => 0

## WHAT IS DELIVERED ALREADY

The term, at shape 4, in the 728 worktree. Wide cannot close it. This obligation has supply 0.

## THE REASONING

This is not a fourth Convert wrap. The neighbour is 728's wide wall. The obligation is the same term at the heavy cap the 718 critic named. Named reading about 14k tokens at 4 B per token: this brief, the 728 report HEAD and sections 3 and 5, Probe728.agda.txt at the obligation lines, Probe692.agda:63-66, review-of-LJ-1-718-1.md:103-114. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether the written composition checks at `-M4g`. Estimate the 728 term unchanged, plus one heavy floor. Basis: agents/tasks/LJ-1-728/lj-1.728-report.md:144

## WHAT GO AND NO-GO EACH EARN

**GO** is `grounded-from-complete` on the meter at heavy. **NO-GO** that is a heap wall means the frame is the defect: split `hull-closed` from the ambient-slot assembly. Do not retry Convert. Do not write a `review-of` for a resource wall.

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
  changed_files_any = ["agents/tasks/LJ-1-728-SPLIT/lj-1.728-SPLIT-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-728-SPLIT/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-728-SPLIT/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-728-SPLIT/review-of-LJ-*-*.md"]

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
  changed_files_none = ["agents/tasks/LJ-1-728-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda"]
  changed_files_none = ["agents/tasks/LJ-1-728-SPLIT/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-728-SPLIT/review-of-*.md"]

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
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 180.753)
- CANDIDATE archive/dev/DD-archived.md  (score 179.520)
- CANDIDATE archive/dev/PLAN-archived.md  (score 167.043)
- CANDIDATE archive/dev/STATUS-archived.md  (score 144.592)
- CANDIDATE archive/dev/TASKS-archived.md  (score 140.156)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 30.565)
- CANDIDATE dev/literature/devlin-errata.md  (score 27.395)
- CANDIDATE dev/literature/primary-sources.md  (score 26.006)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 23.991)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 23.569)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
