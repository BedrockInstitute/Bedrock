# LJ-1.644: is the bill's kappa the site the producer chooses

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-644/Probe644.agda`:

    kappa-is-chosen : (κ : S) → IsOrd (fst κ) → IsCardinalL κ
                    → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
                    → <the statement that `fst κ` IS the `θ` that
                       `cardAboveAt` chooses at some `a`, or the term naming
                       the one input that statement needs>

Land nothing in `src/`. **Do not build `IsCardinal` and do not bridge an
ambient injection to a code.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-644/Probe644.agda::kappa-is-chosen"]

## SCOPE (write)
- agents/tasks/LJ-1-644/Probe644.agda
- agents/tasks/LJ-1-644/lj-1.644-report.md
- agents/tasks/LJ-1-644/review-of-kappa-is-chosen.md
- agents/tasks/LJ-1-644/runs/

## PREMISES

1. **THE JOIN DEFECT, IN TWO LINES.** `BoundedSubsetAt` takes
   `(cardκ : IsCardinal κ)`, the AMBIENT predicate, while `GCHStatement` gives
   `IsCardinalL κ`, the CODED one. The bill cannot feed its own chapter. Basis:
   src/L/BoundedSubset.lagda.md:1386
2. `[LJ-1.643]` censused every producer of ambient `IsCardinal`: there are
   THREE, all in `src/L/CardinalAbove.lagda.md`, and every one produces it only
   at a site IT chose, never at a site handed in. Basis:
   agents/tasks/LJ-1-643/lj-1.643-report.md:45
3. `cardAboveAt` is UNTRUNCATED and its chosen `θ` comes with `IsOrd θ`,
   `IsCardinal θ` and `⟨ a ∈ˢ θ ⟩`. Basis: src/L/CardinalAbove.lagda.md:207
4. Its one external input is inhabited in the tree: `noInjOrd : NoInjOrd`.
   Basis: src/L/CardinalAbove.lagda.md:575
5. `[LJ-1.640]` proved being an ambient cardinal and being a least-cardinal site
   are the SAME condition at an ordinal L-element, so pinning `fst κ` as the
   chosen site is exactly what the above-`ω` half still owes. Basis:
   agents/tasks/LJ-1-640/Probe640.agda:182
6. **THE ONE WAY TO WASTE THIS DISPATCH.** Do not try `IsCardinalL κ →
   IsCardinal κ`. That is ambient-from-coded, `[LJ-1.533]`'s "Code buys ambient.
   Ambient buys nothing", and `[LJ-1.615]`'s shelve. Basis:
   agents/tasks/LJ-1-533/lj-1.533-report.md:1

## WHAT IS DELIVERED ALREADY

Premises 2, 3 and 4 are terms in `src/`, landed this week by the `CardinalAbove`
chain. Nothing connects a producer's CHOSEN site to a site the bill NAMES.

## THE REASONING

Every producer chooses its site, and the bill names one. Either the bill's `κ`
is reachable as a chosen site, or the campaign must restate the bill. This
measures which, and it is the last unmeasured step of the above-`ω` half.

## W3, THE WIDEST UNMEASURED TERM

Whether `IsCardinalL κ` plus ordinality pins `fst κ` against a chosen `θ`.
Estimate 70 to 140 lines, basis: `[LJ-1.640]`'s comparable analysis was 89 code
lines in a 188-line probe (agents/tasks/LJ-1-640/lj-1.640-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** closes the above-`ω` half, or names its one remaining input.
**NO-GO** means the bill's `κ` is NOT reachable as a chosen site, and that is a
stop worth having: it says the bill must be restated, which is my call and not
yours, and you hand me the evidence for it.
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
  changed_files_any = ["agents/tasks/LJ-1-644/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-644/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-644/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-644/Probe644.agda"]
  changed_files_none = ["agents/tasks/LJ-1-644/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-644/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 139.838)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 115.713)
- CANDIDATE dev/ARCHIVE.md  (score 108.775)
- CANDIDATE archive/dev/DD-archived.md  (score 101.024)
- CANDIDATE archive/dev/JOURNAL.md  (score 100.620)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.594)
- CANDIDATE dev/literature/devlin-II5.md  (score 34.383)
- CANDIDATE dev/literature/digest.md  (score 28.671)
- CANDIDATE dev/literature/devlin-errata.md  (score 23.558)
- CANDIDATE dev/literature/terms-2026-08.md  (score 23.009)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
