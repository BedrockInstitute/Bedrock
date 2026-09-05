# LJ-1.543: B6, and whether it is the theorem or something cheaper

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-543/Probe543.agda`:

    SubsetIntoStage :
        (κ y : S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
      → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩

**an AMBIENT conclusion. No `InjCode`, no `Formula`.** Land nothing in `src/`.

**`[LJ-1.540]` IS GO AND IT SPLIT THE REMAINING ROWS MECHANICALLY.** B7 is
paid, and its required section counted the code tokens in each remaining row's
own type:

| row | lines | code tokens | verdict |
|---|---|---|---|
| B6 `SubsetIntoStage` | `agents/tasks/LJ-1-523/Probe523.agda:224-228` | 0 | **AMBIENT** |
| B8 `LimitAbove` | `:244-251` | 0 | **AMBIENT** |
| B10 `SuccIntoPower` | `:266-269` | 1, `InjL` | wants a code |

**So B6 and B8 do not touch the coding wall** that `[LJ-1.533]` and
`[LJ-1.535]` closed, and B6 is the cheaper of the two to state.

**THE D-10 IS WHETHER THIS IS THE BOUNDED SUBSET THEOREM OR SOMETHING FAR
CHEAPER, AND I DO NOT KNOW.** `src/L/BoundedSubset.lagda.md:1621` has
`theorem : ⟨ x ∈ˢ Lset κ ⟩`, whose conclusion matches B6's. **But B6's
hypothesis is one level lower**: it takes `z ∈ y` where `y ∈ 𝒫 κ`, so `z` is a
MEMBER of a subset of `κ`, not the subset. **If members of a subset of `κ` are
just ordinals below `κ`, the tower may place them with no theorem at all.**

**SAY WHICH IT IS BEFORE YOU BUILD.** If it is the cheap reading, the row costs
almost nothing and the report should say so plainly. If it is the theorem, the
row inherits `levelIn` and `cover`, which `[LJ-1.523]` recorded as carried into
`BoundedSubsetTheorem` as Π arguments and NOT on this bridge's bill.

**`[LJ-1.540]` ALSO NOTED THE DIRECTION.** B6 "is a crossing in the cheap
direction: model in, ambient out", where B5 wants ambient out of internal and is
the direction that does not pay.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-543/Probe543.agda::SubsetIntoStage"]

## SCOPE (write)
- agents/tasks/LJ-1-543/Probe543.agda
- agents/tasks/LJ-1-543/lj-1.543-report.md
- agents/tasks/LJ-1-543/review-of-SubsetIntoStage.md
- agents/tasks/LJ-1-543/runs/

## PREMISES

1. `[LJ-1.540]` is GO and paid B7. Basis: agents/tasks/LJ-1-540/lj-1.540-report.md:1
2. Its split names B6 as ambient. Basis: agents/tasks/LJ-1-540/lj-1.540-report.md:1
3. B6's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:224
4. Its hypothesis is model-side, at the power set. Basis: agents/tasks/LJ-1-523/Probe523.agda:226
5. Its conclusion is ambient. Basis: agents/tasks/LJ-1-523/Probe523.agda:227
6. The bounded subset theorem's conclusion has the same shape. Basis: src/L/BoundedSubset.lagda.md:1621
7. That theorem sits under `levelIn` and `cover`. Basis: src/L/BoundedSubset.lagda.md:1555
8. `[LJ-1.533]` closed the generic coded route. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
9. `[LJ-1.535]` closed the counting-site route. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
10. `[LJ-1.528]` paid B4 and left six unpaid. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE JOIN HAD SEVEN UNPAID INPUTS THIS MORNING AND HAS FIVE.** `[LJ-1.528]`
paid B4, `[LJ-1.540]` paid B7. **Of the five, two are ambient, two want a code
that needs a fresh formula, and one wants the direction that does not pay.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE READING.** Say at `file:line` what
`z ∈ y ∈ 𝒫 κ` gives you about `z`. **If it makes `z` an ordinal below `κ`,
name the tower lemma that places it and the row is cheap.** If it does not,
say why, and then say whether the bounded subset theorem applies with its two
hypotheses carried.

**DO NOT DISCHARGE `levelIn` OR `cover`.** If the theorem is needed, carry them
as hypotheses. `[LJ-1.523]` recorded that they are not on this bridge's bill.

**DO NOT BUILD AN `InjCode` AND DO NOT LOOK FOR A FORMULA.** The row is ambient
and both coded routes are closed by measurement.

**DO NOT ATTEMPT B8 OR B10.** AD12 gives this brief one obligation.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## CHEAP OR THE THEOREM`.** One paragraph, with
`file:line`, saying which reading is right and what the row actually cost.
**If it is cheap, say the line count: the mathematician has been over-pricing
this bridge and wants to know.**

**REQUIRED REPORT SECTION `## WHAT B8 WANTS`.** `LimitAbove`
(`agents/tasks/LJ-1-523/Probe523.agda:244-251`) is the other ambient row.
**Say in three sentences what it asks and whether this task's method reaches
it.** Do not build it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 35. BASIS: `[LJ-1.540]` built the sibling ambient row in a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is what `z` is, because the whole price turns on whether it is an ordinal
below `κ` or an arbitrary constructible set.

    -- z, from z ∈ y and y ∈ 𝒫 κ, at its strongest delivered characterisation

**Write it FIRST, and typecheck it ALONE.** If `z` is an ordinal below `κ`, the
row is a tower lookup. If it is not, the row is the theorem and the estimate
above is wrong.

ESTIMATE for W3: about 15 lines and under 30 seconds. **Do not fund it against
`[LJ-1.540]`'s numbers**: that built an injection and this reads a membership.

## WHAT GO AND NO-GO EACH EARN

**A GO TURNS FIVE UNPAID INPUTS INTO FOUR**, and if it is the cheap reading it
also tells the mathematician that this bridge has been over-priced.

**A NO-GO SAYS B6 IS THE BOUNDED SUBSET THEOREM AFTER ALL**, which would put
`levelIn` and `cover` back on the join's bill and is worth knowing before B8 is
ordered.

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
  changed_files_none = ["agents/tasks/LJ-1-543/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-543/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-543/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-543/Probe543.agda"]
  changed_files_none = ["agents/tasks/LJ-1-543/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-543/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 189.680)
- CANDIDATE archive/dev/JOURNAL.md  (score 160.427)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 152.785)
- CANDIDATE dev/ARCHIVE.md  (score 134.223)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 133.835)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.046)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.141)
- CANDIDATE dev/literature/digest.md  (score 41.813)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.506)
- CANDIDATE dev/literature/geology.md  (score 33.310)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
