# LJ-1.754: BoundedFo of tagAtL at a closedω stage

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-754/Probe754.agda`:

    tagAtL-bounded-at-γ :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → ⟨ ω ∈ˢ γ ⟩
        → {n : ℕ}
        → (s : Fin n)
        → (k : ℕ)
        → (x : Fin n)
        → BoundedFo (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (tagAtL s k x)

`tagAtL` is `src/L/Coding/Model.lagda.md:585`. `BoundedFo` is `src/FOL/Manipulation/Bounding.lagda.md:67`. Take `[LJ-1.747]`'s `numeralL-in-carrier-lim` as a report. Import `LJ-1-747.Probe747` if the include path resolves; if this worktree HEAD lacks that probe, take the leaf as a TYPE. Do not transcribe the 747 closer. Export the name at the file's top level. Do not inhabit `table-sat`. Do not inhabit `mkBoundedFo`. Land nothing in `src/`.

ONE Agda process at a time, pane caliber. Floor first.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-754` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-754/Probe754.agda::tagAtL-bounded-at-γ"]

## SCOPE (write)
- agents/tasks/LJ-1-754/Probe754.agda
- agents/tasks/LJ-1-754/lj-1.754-report.md
- agents/tasks/LJ-1-754/review-of-tagAtL-bounded-at-γ.md
- agents/tasks/LJ-1-754/runs/

## PREMISES

1. **`[LJ-1.747]` INHABITED `numeralL-in-carrier-lim`.** Basis: agents/tasks/LJ-1-747/lj-1.747-report.md:8
2. **`tagAtL` HAS ONE CONSTANT, `numeralL k`.** The pair reader names none. Basis: src/L/Coding/Model.lagda.md:585
3. **`prAtL` NAMES NO CONSTANTS.** Basis: src/L/Coding/Model.lagda.md:103
4. **DO NOT INHABIT `table-sat`.** Basis: agents/tasks/LJ-1-747/lj-1.747-report.md:11

## MEASURED TODAY

- dependents: FOL.Manipulation.Bounding => 6
- supply: tagAtL-bounded-at-γ => 0

## WHAT IS DELIVERED ALREADY

The numeral leaf at Probe747.agda:111. `BoundedFo`. `tagAtL`. This obligation has supply 0.

## THE REASONING

This is not a second numeral bound. The neighbour is 747's membership. The obligation is the `BoundedFo` certificate of `tagAtL`, the first occurs-in leaf 737 named. Named reading about 10k tokens at 4 B per token: this brief; 747 report HEAD; Model.lagda.md:585-586 and :103; Bounding.lagda.md:67-79. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether `BoundedFo` of `tagAtL` assembles from 747's leaf and the empty certificate of `prAtL`. Estimate 20 to 80 lines. Basis: src/FOL/Manipulation/Bounding.lagda.md:67

## WHAT GO AND NO-GO EACH EARN

**GO** is the syntax certificate later key-arity and tag-pair briefs consume. **NO-GO** names whether `prAtL`'s lift introduces a constant, or whether `∈ˢ` fails as the predicate. Do not inhabit `table-sat`. Do not inhabit `mkBoundedFo`.

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
  changed_files_any = ["agents/tasks/LJ-1-754/lj-1.754-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-754/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-754/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-754/review-of-LJ-*-*.md"]

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
  changed_files_none = ["agents/tasks/LJ-1-754/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-754/Probe754.agda"]
  changed_files_none = ["agents/tasks/LJ-1-754/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-754/review-of-*.md"]

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
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 171.080)
- CANDIDATE archive/dev/DD-archived.md  (score 165.144)
- CANDIDATE archive/dev/PLAN-archived.md  (score 148.201)
- CANDIDATE archive/dev/STATUS-archived.md  (score 117.771)
- CANDIDATE archive/dev/TASKS-archived.md  (score 114.777)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.751)
- CANDIDATE dev/literature/devlin-errata.md  (score 28.159)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 25.129)
- CANDIDATE dev/literature/primary-sources.md  (score 25.010)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 21.623)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
