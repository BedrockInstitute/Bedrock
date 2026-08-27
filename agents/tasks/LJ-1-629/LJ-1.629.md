# LJ-1.629: is the bill's site an INITIAL ordinal, because the tree PROVES sq there

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-629/Probe629.agda`:

    site-is-init : <the bill's own site hypotheses> → Init <the site>

with `Init` as `src/L/Ordinal/SquareLaw.lagda.md:692-698` states it, **or the
term naming exactly which conjunct is not reachable and what it needs.** Land
nothing in `src/`.

**ITS HOME, IF IT HOLDS.** `src/L/Ordinal/SquareLaw.lagda.md`, beside `Init`, or
`src/L/StageCardinal.lagda.md` beside the site. **Say which in your report.**

**THE OWNER HAS RULED THAT NO AXIOM WILL BE ADDED, EVER.** `[LJ-1.623]` left
ingredient (iii) two reopeners; `[LJ-1.627]` closed the first by measurement
(leastness at `κL` "buys a comparison discipline, and nothing else"), and the
second was `AmbientToCoded` as an owner-ruled axiom. **That one is now
permanently refused. So (iii) must be a construction or it is nothing, and this
brief is the construction nobody has checked.**

**THE TREE PROVES THE SQUARE LAW, IT DOES NOT ONLY ASSUME IT.**
`via-col-square : (α : S) → Init α → sq α` (`src/L/Ordinal/SquareLaw.lagda.md:960-961`)
is a THEOREM in `src/`. `[LJ-1.623]` listed "through the initial ordinals" as
one of the three ways the tree pays at the site grain, **and then said an
arbitrary site is not one of them. THE BILL'S SITE IS NOT ARBITRARY.**

**`Init` IS FOUR CONJUNCTS AND THE BILL MAY ALREADY CARRY THREE.**

    Init α = IsOrd α
           × ⟨ ω ∈ˢ α ⟩
           × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
           × <α injects into no infinite member's square>

`[LJ-1.589]` fixed the bill's spelling as `IsOrd (fst κ)`, `IsCardinalL κ` and
`(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`. **Conjuncts 1 and 2 look immediate from those and
conjunct 3 is successor-closure at an infinite cardinal. Conjunct 4 is the
question, and I do not know its answer.**

**MY READING, AND IT IS A READING.** Conjunct 4 is an AMBIENT non-injection,
while `IsCardinalL` is INTERNAL, stated by `InjCode` (`src/L/Cardinal.lagda.md:230`).
**If conjunct 4 needs ambient cardinality, it is row 1 of `[LJ-1.564]`'s bill,
`AmbientCardAtSucc`, and (iii) and row 1 are the same demand.** That would be
worth knowing: it would turn two open rows into one. **Measure it. Do not agree
with me: three of my readings have been refuted by measurement this week.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-629/Probe629.agda::site-is-init"]

## SCOPE (write)
- agents/tasks/LJ-1-629/Probe629.agda
- agents/tasks/LJ-1-629/lj-1.629-report.md
- agents/tasks/LJ-1-629/review-of-site-is-init.md
- agents/tasks/LJ-1-629/runs/

## PREMISES

1. `Init` is four conjuncts. Basis: src/L/Ordinal/SquareLaw.lagda.md:692
2. `via-col-square` proves `sq` at every initial ordinal. Basis: src/L/Ordinal/SquareLaw.lagda.md:960
3. `[LJ-1.623]` names the initial ordinals as one of three site-grain payers. Basis: agents/tasks/LJ-1-623/review-of-site-fiber.md:85
4. `[LJ-1.627]` closed the leastness reopener. Basis: agents/tasks/LJ-1-627/LJ-1.627.md:1
5. `[LJ-1.589]` fixed the bill's three site hypotheses. Basis: agents/tasks/LJ-1-589/Probe589.agda:243
6. `IsCardinalL` is stated by `InjCode`, internally. Basis: src/L/Cardinal.lagda.md:230
7. Row 1 of the bill is the ambient cardinality. Basis: agents/tasks/LJ-1-550/Probe550.agda:301
8. `[LJ-1.564]`'s bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
9. `sq` is a Π-bound parameter at the one instantiation. Basis: src/L/BoundedSubset.lagda.md:1388
10. `[LJ-1.617]` measured the demand at the site grain. Basis: agents/tasks/LJ-1-617/lj-1.617-report.md:1
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A proved square law at the initial ordinals, in `src/`, and a bill whose site
carries three hypotheses nobody has compared against `Init`.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FOUR CONJUNCTS ONE BY ONE.** For each,
say at `file:line` whether the bill's own hypotheses give it, and if not, what is
missing. **Report all four even if the first fails.** A table of four is the
deliverable even without the term.

**CONJUNCT 4 IS THE ONE THAT MATTERS AND THE ONE I CANNOT PREDICT.** Say whether
it is ambient or internal, and if ambient, **say whether it is row 1 of the bill
or something weaker.** `[LJ-1.550]`'s `AmbientCardAtSucc` is at
`agents/tasks/LJ-1-550/Probe550.agda:301-302`; compare them directly.

**DO NOT ADD AN AXIOM AND DO NOT POSTULATE.** The owner has ruled the axiom
surface closed permanently. **If this route needs one, it is dead and you say so
plainly.**

**DO NOT REBUILD THE SQUARE LAW.** `via-col-square` is a theorem in `src/`.
**Consume it.**

**MEASURE THE FLOOR FIRST, PEAK RSS AND SECONDS, AND SET AND REPORT YOUR OWN
WALL-CLOCK CAP.**

**DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FOUR CONJUNCTS`.** One row each: given by the
bill, or missing and what it needs.

**REQUIRED REPORT SECTION `## IS (iii) ROW 1`.** Two sentences. **Say whether
ingredient (iii) and the bill's row 1 are the same demand.** If they are, the
campaign has one open row where it thought it had two.

ESTIMATE: about 150 lines in the probe, of which the obligation is about 35.
BASIS: `[LJ-1.617]` and `[LJ-1.621]` compared hypotheses at comparable sizes.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is conjunct 4 at the bill's site.

    -- Init's fourth conjunct, instantiated at the bill's κ, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** Everything else in this brief is
bookkeeping around that one type. ESTIMATE: about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS INGREDIENT (iii) FROM A THEOREM ALREADY IN `src/`**, with no axiom
and no new construction, and completes `class-pred`'s five supplies.

**A NO-GO NAMING CONJUNCT 4 AS ROW 1 MERGES TWO OPEN ROWS INTO ONE**, which is
worth nearly as much: the bill would be four rows and one of them would be doing
two jobs.

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
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-629/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-629/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-629/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-629/Probe629.agda"]
  changed_files_none = ["agents/tasks/LJ-1-629/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-629/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 179.761)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 168.063)
- CANDIDATE archive/dev/JOURNAL.md  (score 155.466)
- CANDIDATE archive/dev/DD-archived.md  (score 135.940)
- CANDIDATE dev/ARCHIVE.md  (score 130.070)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 49.120)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 48.557)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.871)
- CANDIDATE dev/literature/digest.md  (score 39.460)
- CANDIDATE dev/literature/geology.md  (score 31.793)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
