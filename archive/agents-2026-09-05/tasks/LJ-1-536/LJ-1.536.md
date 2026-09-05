# LJ-1.536: StageHigh, which four routes have arrived at

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-536/Probe536.agda`:

    StageHigh : (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩
              → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩

**the level sequence below `γ` lies four stages above `γ`.** No `α`, no limit
hypothesis, no `ω ∈ α`. Land nothing in `src/`.

**FOUR INDEPENDENT ROUTES HAVE ARRIVED AT ONE STATEMENT AND THIS IS ITS
STATABLE FORM.** `[LJ-1.230]` was NO-GO on `hierL δ ∈ Lset α`. `[LJ-1.494]`
measured it again: "the tree does not bound `hierL δ` by `α`"
(`agents/tasks/LJ-1-494/lj-1.494-report.md:66-67`). `[LJ-1.517]` censused every
approximation the tree builds and found no second witness. **And `[LJ-1.532]`
has just shown that row six of the condensation chain reduces to the SAME
statement**, `HierInK` (`agents/tasks/LJ-1-532/Probe532.agda:274-277`).

**`[LJ-1.519]` REDUCED IT TO THIS TASK AND THE REDUCTION IS GREEN.**
`reduction : StageHigh → StageLow → HierInStageLimit`
(`agents/tasks/LJ-1-519/Probe519.agda:235`), total in `γ`. **`StageHigh` is
Devlin's Part B** (`_build/literature/dev2.txt:676-678` through
`agents/tasks/LJ-1-519/review-of-hier-in-stage-limit.md`), the half **Devlin
does not prove**: "We leave all the details to the reader."

**EVERY GATE I PUT ON IT IS NOW OPEN.** At `[LJ-1.519]`'s return I ruled
`StageHigh` orderable but gated on `[LJ-1.522]`, because `𝒟ₒ-intro` wants a
formula and `[LJ-1.494]`'s NO-GO was on the UNGRADED one. **`[LJ-1.520]`
delivered the graded formula and `[LJ-1.522]` paid its ninth hypothesis**
(`agents/tasks/LJ-1-522/Probe522.agda:356-364`). Both are GO.

**AND THE TARGET IS NOT VACUOUS.** `[LJ-1.532]` proved `hier-is-approx`
(`agents/tasks/LJ-1-532/Probe532.agda:346-349`): the canonical witness IS an
approximation. **So this is a statement about an inhabited class**, which is
the check `[LJ-1.507]` taught this campaign to make first.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-536/Probe536.agda::StageHigh"]

## SCOPE (write)
- agents/tasks/LJ-1-536/Probe536.agda
- agents/tasks/LJ-1-536/lj-1.536-report.md
- agents/tasks/LJ-1-536/review-of-StageHigh.md
- agents/tasks/LJ-1-536/runs/

## PREMISES

1. `[LJ-1.519]`'s reduction is green and total in `γ`. Basis: agents/tasks/LJ-1-519/Probe519.agda:235
2. `StageHigh` is stated there. Basis: agents/tasks/LJ-1-519/Probe519.agda:218
3. `[LJ-1.532]` showed row six reduces to the same statement. Basis: agents/tasks/LJ-1-532/Probe532.agda:274
4. It proved the canonical witness is an approximation. Basis: agents/tasks/LJ-1-532/Probe532.agda:346
5. It refuted the ∀-form, which fails only on junk. Basis: agents/tasks/LJ-1-532/Probe532.agda:206
6. `[LJ-1.494]` measured the tree does not bound `hierL δ`. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:127
7. `[LJ-1.520]` delivered the graded formula. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:237
8. `[LJ-1.522]` paid its ninth hypothesis. Basis: agents/tasks/LJ-1-522/Probe522.agda:356
9. `Lset-in` is the tree's route into a stage. Basis: src/L/Constructible.lagda.md:319
10. `𝒟ₒ-intro` is what it demands. Basis: src/L/Constructible.lagda.md:301
11. `hierL` is the canonical witness. Basis: src/L/Hierarchy.lagda.md:621
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CONDENSATION LEG HAS SPENT TWELVE DISPATCHES REACHING THIS ONE
STATEMENT FROM FOUR SIDES.** The formula is graded, its hypotheses are paid,
the chain's other rows are built, and the target is known non-vacuous. **This is
the statement itself.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** The route into a stage is `Lset-in`
(`src/L/Constructible.lagda.md:319`) through `𝒟ₒ-intro` (`:301`), which wants a
`Formula` over the stage whose `defSet` is the sequence. **Say at `file:line`
whether `[LJ-1.520]`'s graded formula is that formula, or whether it says
something adjacent.** If it is adjacent, name the difference and STOP: four
routes have arrived here and a fifth built on a mismatch would be the worst
outcome available.

**THE STAGE IS `step 4 γ`, NOT `α`.** That is the whole point of `[LJ-1.519]`'s
reduction: no `α`, no limit hypothesis, no `ω ∈ α`. **A term that needs any of
them is not `StageHigh` and does not compose with the reduction.**

**W8. DEVLIN DOES NOT PROVE THIS AND THE BRIEF SAYS SO.** `[LJ-1.519]` read the
primary text and found "We leave all the details to the reader". **You may cite
the source for the TARGET and must price the ROUTE from the tree.** That is the
standing rule this campaign wrote after `[LJ-1.519]`.

**DO NOT REBUILD THE REDUCTION, THE GRADED FORMULA OR THE CLOSURE.** All three
are delivered.

**DO NOT ATTEMPT `StageLow`.** AD12 gives this brief one obligation, and
`[LJ-1.519]` states `StageLow` separately as the `γ ≤ ω` tail.

**DO NOT POSTULATE AND DO NOT ADD A REFLECTION HYPOTHESIS.**

**REQUIRED REPORT SECTION `## WHAT THE FOUR ROUTES GET`.** If this lands, say
what `[LJ-1.494]`'s `hier-in-stage`, `[LJ-1.532]`'s `HierInK`, row six of the
chain, and `[LJ-1.519]`'s `HierInStageLimit` each get from it, at `file:line`.
**If it does not land, say which of the four is furthest from the term you did
build.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 220 lines in the probe, of which the obligation is
about 60. BASIS: `[LJ-1.532]` built a refutation, a counterexample and two
directions of a pair characterisation in a comparable file. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the formula at `𝒟ₒ-intro`, because that is the one door into a stage and
every route here has stopped in front of it.

    -- [LJ-1.520]'s graded formula, applied at 𝒟ₒ-intro for the sequence

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
graded formula does not fit the door, say what shape the door wants and STOP.
**That would be the sharpest statement this leg could make and it would end
twelve dispatches of circling.**

ESTIMATE for W3: about 30 lines and under 50 seconds. **Do not fund it against
`[LJ-1.532]`'s numbers**: that refuted a statement and this opens a door.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS FOUR ROUTES AT ONCE** and, with `[LJ-1.519]`'s reduction, delivers
the condensation leg's last named blocker.

**A NO-GO AT THE DOOR NAMES WHAT `𝒟ₒ-intro` WANTS THAT THE TREE DOES NOT
HAVE**, which after twelve dispatches is a ruling-grade finding and not a
failure.

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
  changed_files_none = ["agents/tasks/LJ-1-536/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-536/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-536/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-536/Probe536.agda"]
  changed_files_none = ["agents/tasks/LJ-1-536/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-536/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 197.673)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 185.547)
- CANDIDATE archive/dev/JOURNAL.md  (score 165.830)
- CANDIDATE dev/ARCHIVE.md  (score 149.953)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 144.700)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 71.505)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 50.169)
- CANDIDATE dev/literature/digest.md  (score 46.625)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 36.745)
- CANDIDATE dev/literature/geology.md  (score 35.215)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
