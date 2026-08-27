# LJ-1.633: is omega an L-cardinal

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-633/Probe633.agda`:

    omega-is-L-cardinal : IsCardinalL ωʟ

Land nothing in `src/`.

`IsCardinalL` is `src/L/Cardinal.lagda.md:230-233`:

    IsCardinalL κ =
      (δ : S) → ⟨ fst δ ∈ fst κ ⟩
              → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

`ωʟ : S` is `src/L/Axioms/Infinity.lagda.md:69-70`. `InjCode` is
`src/L/Cardinal.lagda.md:223-228`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-633/Probe633.agda::omega-is-L-cardinal"]

## SCOPE (write)
- agents/tasks/LJ-1-633/Probe633.agda
- agents/tasks/LJ-1-633/lj-1.633-report.md
- agents/tasks/LJ-1-633/review-of-omega-is-L-cardinal.md
- agents/tasks/LJ-1-633/runs/

## PREMISES

1. `[LJ-1.629]` proved `target-false : IsCardinalL ωʟ → SiteIsInit → Empty.⊥`,
   green. Basis: agents/tasks/LJ-1-629/Probe629.agda:139-140
2. It could not discharge `IsCardinalL ωʟ` and left it a hypothesis, with the
   proof sketched and priced at 60 to 100 lines. Basis:
   agents/tasks/LJ-1-629/Probe629.agda:133-137
3. The sketch: a code at a member `δ ∈ ω` reads back to an ambient injection
   `ω ↪ δ` with `δ ≡ # n`, and the tree's own pigeonhole refutes it. Basis:
   src/L/Ordinal/SquareLaw.lagda.md:604-610, `no-inj`
4. `numeral-wit : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → Σ[ n ∈ ℕ ] (# n ≡ δ)` supplies the
   `δ ≡ # n` step untruncated. Basis: src/L/StageCardinal.lagda.md:439

## WHAT IS DELIVERED ALREADY

Premises 1 and 4 are terms. Nothing in `src/` carries `IsCardinalL ωʟ`.

## THE REASONING

`[LJ-1.629]` closed NO-GO because `Init` is false at `ωʟ` while the bill admits
`κ ≡ ω`. That refutation is conditional on this one fact. Discharge it and the
refutation becomes unconditional, which settles whether `via-col-square` can
ever serve the bill. Leave it undischarged and the campaign is arguing.

## W3, THE WIDEST UNMEASURED TERM

`omega-is-L-cardinal` itself. Estimate 60 to 100 lines, basis: `[LJ-1.629]`'s
own pricing of the same sketch (agents/tasks/LJ-1-629/lj-1.629-report.md:202-206).
The probe measures it.

## WHAT GO AND NO-GO EACH EARN

**GO** earns the term and makes `[LJ-1.629]`'s refutation unconditional.
**NO-GO** is worth as much and is the more interesting outcome: if `ω` is NOT
an L-cardinal in this tree's sense, say which conjunct fails and stop, because
the bill then quantifies over a `κ` it cannot instantiate at `ω`.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-633/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-633/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-633/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-633/Probe633.agda"]
  changed_files_none = ["agents/tasks/LJ-1-633/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-633/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# CLOSES BACKLOG ITEM 30, MEASURED ON LJ-1.630 2026-08-25. A REAL failed
# landing carries a named Agda error and NEITHER companion file: the coder
# edits the target directly and leaves ad-hoc runs/*.out. Both rows above
# demand a companion (Probe or review-of), so that return matched NOTHING
# and the task parked with its evidence invisible. This row is the catch-all
# and it sits BELOW heap-wall-park, so a wall still parks.
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

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 164.296)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 136.233)
- CANDIDATE archive/dev/JOURNAL.md  (score 116.406)
- CANDIDATE dev/ARCHIVE.md  (score 96.862)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 93.309)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 38.170)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 35.280)
- CANDIDATE dev/literature/devlin-errata.md  (score 25.315)
- CANDIDATE dev/literature/digest.md  (score 24.802)
- CANDIDATE dev/literature/geology.md  (score 22.808)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
