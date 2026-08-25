# LJ-1.542: the twelve numK rows, the largest single family

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-542/Probe542.agda`:

    numK-frame-inhabited :
        (the extra hypotheses the TWELVE numK forms take, collected as one
         telescope)
      → (a witness of that telescope at KValue's frame)

**the `numK0` to `numK11` family, twelve fields.** Land nothing in `src/`.

**TWO FAMILIES ARE COLLECTED AND THE HEAP IS FLAT.** `[LJ-1.538]` took the nine
env forms at **3.56 s and 722,698,240 B**; `[LJ-1.539]` took the `subK` forms at
**3.49 s and 749,125,632 B**. **Two families, near-identical cost, where
`[LJ-1.534]`'s attempt at all sixteen extra hypotheses at once walled four
times.** One family at a time is the method and it is now measured twice.

**THE FORM IS DELIVERED AND IT IS ONE LINE.** `SupplyEnv.#∈λ`
(`src/L/Coding/EnvSupply.lagda.md:229`) is `(n : ℕ) → ⟨ # n ∈ Lset lam ⟩`, and
`Bound.num∈λ` (`src/L/Coding/Bound.lagda.md:139`) is the same statement on the
`fst (numeralL k)` side. **`numeralL-fst`
(`src/L/Axioms/Numerals.lagda.md:179`) is the transport between them, one
line.**

**AND THE RECORD'S TWELVE ARE ONE STATEMENT AT TWELVE NUMERALS.**
`TFacts.numK0` to `numK11` (`src/L/Condensation/TwelveAgree.lagda.md:145-156`)
differ only in the numeral. **If the family collects at all, it collects
twelve-for-one, which is why it is the largest single block of the 41 and worth
taking before the smaller ones.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-542/Probe542.agda::numK-frame-inhabited"]

## SCOPE (write)
- agents/tasks/LJ-1-542/Probe542.agda
- agents/tasks/LJ-1-542/lj-1.542-report.md
- agents/tasks/LJ-1-542/review-of-numK-frame.md
- agents/tasks/LJ-1-542/runs/

## PREMISES

1. `[LJ-1.538]` collected the nine env forms with its figures. Basis: agents/tasks/LJ-1-538/lj-1.538-report.md:26
2. `[LJ-1.539]` collected the `subK` forms with its figures. Basis: agents/tasks/LJ-1-539/lj-1.539-report.md:28
3. `#∈λ` is the delivered form. Basis: src/L/Coding/EnvSupply.lagda.md:229
4. `num∈λ` is the same statement on the other side. Basis: src/L/Coding/Bound.lagda.md:139
5. `numeralL-fst` is the transport. Basis: src/L/Axioms/Numerals.lagda.md:179
6. The record's twelve differ only in the numeral. Basis: src/L/Condensation/TwelveAgree.lagda.md:145
7. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
8. `KValue.facts` is delivered there. Basis: src/L/Condensation.lagda.md:7411
9. `[LJ-1.495]` shifts `KFacts` to the record's indices, and its record ends at `pairK`. Basis: agents/tasks/LJ-1-495/Probe495.agda:199
10. `[LJ-1.534]` walled when all sixteen were collected at once. Basis: agents/tasks/LJ-1-534/LJ-1.534.md:1
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**SIXTEEN OF THE FORTY ONE CHAPTER-DELIVERED FIELDS ARE COLLECTED**, nine by
`[LJ-1.538]` and seven by `[LJ-1.539]`. **These twelve would make twenty
eight.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.495]`'s shift DOES carry `numK0` to `numK11`
among its twenty six: its record ends at `pairK`
(`agents/tasks/LJ-1-495/Probe495.agda:199`) and the `numK` rows are inside it.
**So there may be TWO routes to these twelve: the shift, and `#∈λ`.** Say at
`file:line` which is cheaper and whether they agree. **If the shift already
delivers them, say so and STOP: the family would then need no collection at
all, and that is a better answer than a telescope.**

**IF YOU COLLECT, TRIM FIRST.** `[LJ-1.538]` found one hypothesis carried and
never consumed; `[LJ-1.539]` found its family needed no gate at all. **Audit
before you collect.**

**REPORT THE PEAK RSS BESIDE THE OTHER TWO.** Three families with three figures
tell the mathematician whether the remaining twenty five can be collected in
one pass or must be split again.

**DO NOT COLLECT ANY OTHER FAMILY.** AD12 gives this brief one obligation and
`[LJ-1.534]` measured what happens when the scope is everything.

**DO NOT REBUILD `[LJ-1.495]`'s SHIFT.** Cite it.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## SHIFT OR FORM`.** Which route delivers the
twelve, at `file:line`, and what each costs. **If both work, say which the
mathematician should rule for.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.538]` and `[LJ-1.539]` each collected a family at this
frame and reported their own figures. Comparables are of SHAPE and nothing may
be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the shift already pays them, because if it does the whole task is
a citation and not a collection.

    -- numK7, say, from [LJ-1.495]'s shifted KFacts, at the record's index

**Write it FIRST, and typecheck it ALONE.** One numeral is enough to settle
it. If it goes through, stop and report: the family costs nothing.

ESTIMATE for W3: about 12 lines and under 30 seconds. **Do not fund it against
`[LJ-1.538]`'s or `[LJ-1.539]`'s numbers**: both collected telescopes and this
tries a projection.

## WHAT GO AND NO-GO EACH EARN

**A GO BY THE SHIFT COSTS NOTHING AND PAYS TWELVE FIELDS**, which would be the
cheapest result on this front.

**A GO BY COLLECTION GIVES A THIRD HEAP FIGURE** and takes the collected count
to twenty eight of forty one.

**A NO-GO SAYS THE TWELVE NEED SOMETHING NEITHER ROUTE GIVES**, which after two
clean families would be the first sign that the record does not decompose
evenly.

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
  changed_files_none = ["agents/tasks/LJ-1-542/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-542/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-542/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-542/Probe542.agda"]
  changed_files_none = ["agents/tasks/LJ-1-542/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-542/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park_and_split"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 213.308)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 187.360)
- CANDIDATE archive/dev/JOURNAL.md  (score 168.102)
- CANDIDATE dev/ARCHIVE.md  (score 138.878)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 116.252)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 56.126)
- CANDIDATE dev/literature/digest.md  (score 46.031)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 41.211)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 39.498)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.090)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
