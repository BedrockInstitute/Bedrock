# LJ-1.748: a pair of stage members sits in the same stage, under closedω

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-748/Probe748.agda`:

    pr-in-Lset-lim :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        (x y : V ℓ)
        → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
        → ⟨ pr x y ∈ˢ Lset γ ⟩

Instantiate `BoundOver.pr∈λ` (`src/L/Coding/Bound.lagda.md:69-70`) at `T := Lset`, `lam := γ`. `T-pr` is `pr∈Lset-suc` (`src/L/Axioms/Basic.lagda.md:596-598`). `succλ` is `Closer.suc∈γ` (`Probe737Split.agda:125-127`). Export the name at the file's top level. Do not inhabit `pair-in-Lγω`. Do not inhabit `table-sat`. Land nothing in `src/`.

ONE Agda process at a time. Floor first. Prefer `src/` imports plus the 737-SPLIT closer; do not import the 724-SPLIT chain.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-748` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-748/Probe748.agda::pr-in-Lset-lim"]

## SCOPE (write)
- agents/tasks/LJ-1-748/Probe748.agda
- agents/tasks/LJ-1-748/lj-1.748-report.md
- agents/tasks/LJ-1-748/review-of-pr-in-Lset-lim.md
- agents/tasks/LJ-1-748/runs/

## PREMISES

1. **737's GRAPH WITNESS IS A PAIR IN `Lset γ`.** Generic pairing of two stage members is the BoundOver law at closedω. Basis: agents/tasks/LJ-1-737/lj-1.737-report.md:42
2. **`pr∈λ` ALREADY CLOSES PAIRING AT A LIMIT.** The missing piece is the closedω telescope. Basis: src/L/Coding/Bound.lagda.md:69
3. **`pr∈Lset-suc` PLACES THE PAIR TWO SUCCESSORS UP.** closedω absorbs those successors. Basis: src/L/Axioms/Basic.lagda.md:596
4. **`Closer.suc∈γ` IS THE `succλ` THAT BOUND TAKES.** Basis: agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:125
5. **THIS IS NOT `pair-in-Lγω`.** That term places `pr x (Lset x)` for `x ∈ γ`. This term places `pr x y` for `x, y ∈ Lset γ`. Basis: agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:151

## MEASURED TODAY

- dependents: L.Coding.Bound => 4
- supply: pr-in-Lset-lim => 0

## WHAT IS DELIVERED ALREADY

`pr∈λ` at a limit, `pr∈Lset-suc`, `suc∈γ`. This obligation has supply 0. It does not wait on `[LJ-1.747]`.

## THE REASONING

This is not a second `pair-in-Lγω`. The neighbour is that member-pair. The obligation is BoundOver pairing of two stage members, the graph leaf 737's recording unfolds. Named reading about 11k tokens at 4 B per token: this brief; Bound.lagda.md:67-78; Basic.lagda.md:596-598; Probe737Split.agda:105-127 and :151-154; 737 report witness list. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether BoundOver's `pr∈λ` converts at `lam := γ` under closedω. Estimate 20 to 80 lines. Basis: src/L/Coding/Bound.lagda.md:69

## WHAT GO AND NO-GO EACH EARN

**GO** is the pairing closure the tower graph consumes. **NO-GO** names the missing `succλ` or `T-out` step. Do not inhabit `table-sat`. Do not inhabit `pair-in-Lγω`.

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
  changed_files_any = ["agents/tasks/LJ-1-748/lj-1.748-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-748/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-748/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-748/review-of-LJ-*-*.md"]

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
  changed_files_none = ["agents/tasks/LJ-1-748/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-748/Probe748.agda"]
  changed_files_none = ["agents/tasks/LJ-1-748/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-748/review-of-*.md"]

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
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 174.393)
- CANDIDATE archive/dev/DD-archived.md  (score 171.620)
- CANDIDATE archive/dev/PLAN-archived.md  (score 157.190)
- CANDIDATE archive/dev/TASKS-archived.md  (score 126.679)
- CANDIDATE archive/dev/STATUS-archived.md  (score 123.689)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 40.329)
- CANDIDATE dev/literature/primary-sources.md  (score 33.153)
- CANDIDATE dev/literature/devlin-errata.md  (score 31.352)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 29.719)
- CANDIDATE dev/literature/formalizations-landscape.md  (score 25.534)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
