# LJ-1.639: write the residue's identification down as a term

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-639/Probe639.agda`:

    residue-is-kappa-inj :
      <a row proving `[LJ-1.618]`'s `Inj-extract` is EXACTLY the untruncation
       of `src/L/SquareLawClosed.lagda.md`'s `κ-injL`, at the same `a` and `oa`,
       stated so that `refl` closes it if the two types agree>

Land nothing in `src/`. **This RECORDS a fact. It attacks nothing.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-639/Probe639.agda::residue-is-kappa-inj"]

## SCOPE (write)
- agents/tasks/LJ-1-639/Probe639.agda
- agents/tasks/LJ-1-639/lj-1.639-report.md
- agents/tasks/LJ-1-639/review-of-residue-identification.md
- agents/tasks/LJ-1-639/runs/

## PREMISES

1. `κ-injL : (a : S) (oa : IsOrd (fst a)) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁`
   is in `src/`. Basis: src/L/SquareLawClosed.lagda.md:82
2. `Inj-extract` takes that exact type and returns it untruncated. Basis:
   agents/tasks/LJ-1-618/Probe618.agda:151
3. The truncation is introduced by `leastOf`'s INTERFACE, not by the injection:
   `InjP γ = ∥ Inj γ ∥₁ , squash₁` exists because `leastOf` takes an
   hProp-valued predicate and `Inj γ` is not one. Basis:
   src/L/Cardinal.lagda.md:66
4. `κ-inj` is the MEMBERSHIP half of `IsLeast` alone, `fst (snd least)`; the
   minimality half `κ-min` is `snd (snd least)`. Basis:
   src/L/Cardinal.lagda.md:133

## WHAT IS DELIVERED ALREADY

Both types, in the two files premises 1 and 2 name. **No term ties them.** The
identification exists only in prose, in this brief.

## THE REASONING

`[LJ-1.623]` tied `SiteFiber` to `PairingAt` with one `refl` row and that row is
why the campaign stopped attacking the same object twice. This is the same move
one level up, at the term `src/` actually carries. A fact stated only in a report
is re-derived; a fact stated as a `refl` row is not.

## W3, THE WIDEST UNMEASURED TERM

Whether the two types agree on the nose or up to an unfolding. `[LJ-1.623]`'s
comparable row closed by `refl` at 95-96 of its probe. Estimate 30 to 60 lines,
basis: agents/tasks/LJ-1-623/Probe623.agda:95. If `refl` does not close it, the
DIFFERENCE is the deliverable and you state it as a type.

## WHAT GO AND NO-GO EACH EARN

**GO** puts the campaign's residue on one line that a later brief can cite
instead of re-deriving. **NO-GO** means the two are NOT the same object, which
would refute a premise three dispatches have leaned on and is worth far more.
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
  changed_files_any = ["agents/tasks/LJ-1-639/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-639/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-639/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-639/Probe639.agda"]
  changed_files_none = ["agents/tasks/LJ-1-639/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-639/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 156.385)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 136.943)
- CANDIDATE dev/ARCHIVE.md  (score 117.327)
- CANDIDATE archive/dev/JOURNAL.md  (score 107.828)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 105.351)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 73.074)
- CANDIDATE dev/literature/devlin-II5.md  (score 39.472)
- CANDIDATE dev/literature/digest.md  (score 32.124)
- CANDIDATE dev/literature/terms-2026-08.md  (score 28.990)
- CANDIDATE dev/literature/fine-structure.md  (score 27.633)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
