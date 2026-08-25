# LJ-1.540: B7, a stage absorbs one element, and it wants no code

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-540/Probe540.agda`:

    AbsorbsAt :
        (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
      → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫

**an AMBIENT injection. No `InjCode`, no `Formula`.** Land nothing in `src/`.

**`[LJ-1.535]` RE-CLASSIFIED THIS ROW AND THAT IS WHY IT IS QUEUED NOW.** Its
required section reports: "**B7 ... NO DELIVERED SHADOW AT ITS OWN SHAPE, AND
IT WANTS NO CODE.** Its conclusion is `⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`, an
AMBIENT injection." **So B7 is the one row of `[LJ-1.523]`'s list B that the
coding wall does not touch.**

**THE CODING WALL, FOR CONTEXT, AND YOU MUST NOT WALK INTO IT.** `[LJ-1.533]`
proved by a type argument that no term codes an arbitrary ambient injection:
both L-set generators take a `Formula` and `_↪_` carries none. `[LJ-1.535]`
then tried keeping the formula at the counting site and measured that
`count-bound` (`src/L/StageCardinal.lagda.md:124-129`) consumes it through
`code : Formula (⊥* {ℓ}) k → ℕ`, **so the formula becomes a numeral and is not
in the injection's value.** Both routes to a CODED injection are closed. **This
obligation is ambient and needs neither.**

**THE TREE HAS THIS SHAPE ONLY AS A HYPOTHESIS.**
`src/L/BoundedSubset.lagda.md:1392` takes
`(absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)` as a PARAMETER of
`BoundedSubsetAt`. **Nothing delivers it.**

**AND THE NEAR NEIGHBOUR IS A DIFFERENT SHAPE. DO NOT READ ONE AS THE OTHER.**
`absorbs` (`src/L/Absorption.lagda.md:635-638`) delivers
`⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`: a SUCCESSOR ORDINAL into itself, from
`SG.shiftFun` and `SG.shiftFun-inj`. **`[LJ-1.523]` says so at
`Probe523.agda:230-233` and `[LJ-1.535]` refused to conflate them under C-42.
Read its method; do not reuse its statement.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-540/Probe540.agda::AbsorbsAt"]

## SCOPE (write)
- agents/tasks/LJ-1-540/Probe540.agda
- agents/tasks/LJ-1-540/lj-1.540-report.md
- agents/tasks/LJ-1-540/review-of-AbsorbsAt.md
- agents/tasks/LJ-1-540/runs/

## PREMISES

1. `[LJ-1.535]` is a critic-upheld NO-GO that re-classified B7. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
2. B7's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:234
3. The tree has the shape only as a hypothesis. Basis: src/L/BoundedSubset.lagda.md:1392
4. `absorbs` is the near neighbour and a different shape. Basis: src/L/Absorption.lagda.md:635
5. `[LJ-1.523]` records that difference itself. Basis: agents/tasks/LJ-1-523/Probe523.agda:230
6. `[LJ-1.533]` proved no term codes an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
7. `[LJ-1.535]` measured that the counting Gödel-numbers its formula. Basis: src/L/StageCardinal.lagda.md:124
8. `_↪_` is a bare function with an injectivity proof. Basis: src/L/Cardinal.lagda.md:47
9. `[LJ-1.528]` paid B4 and left six unpaid inputs. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE JOIN HAS SIX UNPAID INPUTS AND FIVE OF THEM WANT A CODE.** `[LJ-1.533]`
and `[LJ-1.535]` between them closed both routes to a coded injection. **B7 is
the one that does not need one, and it has never been attempted.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `Lset α ∪ ⁅ x ⁆s` adjoins ONE element to a stage,
and the hypothesis says every member of `x` is already in `Lset α`. **Say at
`file:line` whether `x` itself is in `Lset α`, and if not, why adjoining it
does not increase the cardinality.** If the answer needs `α` to be a limit, say
so: the type as stated does not assume it and that would be a finding about
`[LJ-1.523]`'s row rather than about your term.

**READ `absorbs`'s METHOD.** `SG.shiftFun` and `SG.shiftFun-inj`
(`src/L/Absorption.lagda.md:635-638`) shift a successor into itself. **The
shape differs and the technique may not. Say which parts transfer at
`file:line` and which do not.**

**DO NOT BUILD AN `InjCode` AND DO NOT LOOK FOR A FORMULA.** Both routes are
closed by measurement and this obligation is ambient.

**DO NOT DISCHARGE `BoundedSubsetAt`'s HYPOTHESIS.** That is a landing and this
is a probe. Build the term at its own type.

**DO NOT ASSUME CHOICE.** `[LJ-1.528]` built `CardAboveL` choice-free and
`[LJ-1.94]` recorded its Hartogs the same way. **Say whether yours is.**

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT B6, B8 AND B10 WANT`.** Of the six unpaid
inputs, this task takes B7. **For B6 `SubsetIntoStage`, B8 `LimitAbove` and B10
`SuccIntoPower` (`agents/tasks/LJ-1-523/Probe523.agda:224-228`, `:244-251`,
`:266-268`), say for each whether it wants a CODE or an AMBIENT fact.** Do not
build them. **That split is what the mathematician needs next.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 50. BASIS: `absorbs` is a delivered injection of comparable shape in
`src/`. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is where `x` goes, because the injection must place one extra element inside
a stage that does not obviously have room reserved for it.

    -- the image of ⁅ x ⁆s under the injection, as a term

**Write it FIRST, and typecheck it ALONE.** If no place can be found for `x`
without moving the rest, say what the shift costs, which is exactly what
`absorbs` pays with `shiftFun`.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`absorbs`**: that shifts a successor and this adjoins to a stage.

## WHAT GO AND NO-GO EACH EARN

**A GO TURNS SIX UNPAID INPUTS INTO FIVE** and discharges a hypothesis
`BoundedSubsetAt` has carried unproved since it was written.

**A NO-GO SAYS THE ABSORPTION NEEDS SOMETHING THE STAGE DOES NOT GIVE**, and
with the required section it would still tell the mathematician how the
remaining three rows split between coded and ambient. **That split is worth the
dispatch on its own.**

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
  changed_files_none = ["agents/tasks/LJ-1-540/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-540/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-540/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-540/Probe540.agda"]
  changed_files_none = ["agents/tasks/LJ-1-540/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-540/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 176.452)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 164.435)
- CANDIDATE archive/dev/JOURNAL.md  (score 161.141)
- CANDIDATE dev/ARCHIVE.md  (score 136.737)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 125.948)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 59.032)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.635)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.410)
- CANDIDATE dev/literature/digest.md  (score 42.144)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 33.986)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
