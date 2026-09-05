# LJ-1.519: hier-in-stage at a limit, which is the statement with a source

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-519/Probe519.agda`:

    hier-in-stage-limit :
        (α : V ℓ) → IsOrd α → IsLimit α → ⟨ ω ∈ α ⟩
      → (γ : V ℓ) → ⟨ γ ∈ α ⟩
      → ⟨ (the sequence of tower values at δ ≤ γ) ∈ Lset α ⟩

**at a LIMIT `α > ω`, and not at an arbitrary `α`.** Land nothing in `src/`.

**`[LJ-1.517]` IS A CRITIC-UPHELD NO-GO THAT DID MORE THAN ITS BRIEF ASKED.**
It censused every approximation the tree builds, seven rows, each re-declared
in the probe so a green row is checked evidence and not a comment
(`agents/tasks/LJ-1-517/runs/w3-1.out`, exit 0). Two of its findings set this
task:

1. **THERE IS NO SECOND WITNESS TO FIND.** The witness slot is generic
   (`src/L/Hierarchy.lagda.md:382`) and the orthodox witness is the level
   sequence (`dev/literature/devlin-II5.md:216`). **`[LJ-1.494]`'s clause "or
   until a brief names a different witness than `hierL`" is RETIRED.**
2. **THE STATEMENT I HAVE BEEN ORDERING HAS NO SOURCE.** `hier-in-stage` at an
   arbitrary `α` with `δ ∈ Lset α` is unsourced. **At a limit `α > ω` it is
   Devlin 2.6(ii)** (`dev/literature/devlin-II5.md:218`, `:221`): the sequence
   `(L_δ | δ ≤ γ)` lies in `L_α` for `γ < α`. **That is the statement to
   order, and the change is mine, not the coder's.**

**PRICE IT FROM THE WITNESS, NOT FROM `levelIn`.** `[LJ-1.517]` measured that
unfolding the stage twice (`src/L/Constructible.lagda.md:340`, `:313`) puts the
tower's value at a stage `γ` with `γ ∈ β ∈ α`
(`agents/tasks/LJ-1-517/Probe517.agda:204`). **The witness does not want room
in `Lset α`. It wants room two membership steps below `α`.** A brief that
budgets only `levelIn` under-prices this and mine says so.

**THE LIMIT IS WHAT BUYS THE ROOM.** At a limit every `β ∈ α` has a successor
in `α`, so two steps below `α` is reachable where at an arbitrary `α` it is
not. **That is why the source states it at a limit and why the arbitrary
spelling failed.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-519/Probe519.agda::hier-in-stage-limit"]

## SCOPE (write)
- agents/tasks/LJ-1-519/Probe519.agda
- agents/tasks/LJ-1-519/lj-1.519-report.md
- agents/tasks/LJ-1-519/review-of-hier-in-stage-limit.md
- agents/tasks/LJ-1-519/runs/

## PREMISES

1. `[LJ-1.517]` is a critic-upheld NO-GO with a seven row census. Basis: agents/tasks/LJ-1-517/lj-1.517-report.md:184
2. It reports there is no second witness to find. Basis: agents/tasks/LJ-1-517/lj-1.517-report.md:185
3. It names the limit statement and its source. Basis: agents/tasks/LJ-1-517/lj-1.517-report.md:188
4. The witness needs room two membership steps below the stage. Basis: agents/tasks/LJ-1-517/Probe517.agda:204
5. The stage unfolds twice at these two sites. Basis: src/L/Constructible.lagda.md:340
6. The witness slot in the tree is generic. Basis: src/L/Hierarchy.lagda.md:382
7. `hierL` is the tree's own witness and is not stage bounded. Basis: src/L/Hierarchy.lagda.md:621
8. `[LJ-1.494]` measured that non-bounding. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:127
9. The orthodox witness is the level sequence. Basis: dev/literature/devlin-II5.md:216
10. The limit statement is 2.6(ii). Basis: dev/literature/devlin-II5.md:221
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**NINE CONDENSATION DISPATCHES, AND THIS IS THE FIRST WITH A SOURCE FOR ITS
TARGET.** `[LJ-1.514]` removed the Formula-carrier wall for the family,
`[LJ-1.516]` is transporting the satisfaction, and `[LJ-1.517]` closed the
second-witness question and found the sourced spelling. **`hier-in-stage` is
the leg's remaining blocker and this is its statable form.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE LIMIT.** Say at `file:line` what the
tree's `IsLimit` is and whether it gives, for each `β ∈ α`, a successor in `α`.
**If it does not, the two membership steps are not bought and the limit
spelling fails for the same reason the arbitrary one did.** Say so and STOP:
that would mean Devlin 2.6(ii) is not transcribable at this tower and the
condensation leg needs a ruling, not a tenth dispatch.

**W8. READ `dev/literature/devlin-II5.md` AND SAY WHAT YOU TOOK.** This is the
first condensation brief whose target has a source. Quote the lines you use at
`file:line`, and **check them against `dev/literature/devlin-errata.md`
before you rely on them**: that file records the known errors in the primary
text and Chapter II is among them.

**DO NOT ORDER OR REBUILD A SECOND WITNESS.** `[LJ-1.517]` settled it. Use the
level sequence.

**DO NOT WEAKEN THE STATEMENT TO AN ARBITRARY `α`.** That spelling is what nine
dispatches could not close and it has no source.

**DO NOT ATTEMPT `GraphSatAtStage`, `cover` OR `levelIn`.** AD12 gives this
brief one obligation and `[LJ-1.516]` holds the transport.

**DO NOT POSTULATE AND DO NOT ADD A REFLECTION HYPOTHESIS.**

**REQUIRED REPORT SECTION `## WHAT THE LIMIT BOUGHT`.** State, as types, what
the limit hypothesis makes available that an arbitrary `α` does not, and
whether it is enough for the two steps. **This section is the deliverable even
if the obligation is not built.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 200 lines in the probe, of which the obligation is
about 55. BASIS: `[LJ-1.517]` built a seven row census and four types in a
comparable file, and this is one term with a source rather than a census.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the two steps, because `[LJ-1.517]` measured that the witness wants them
and nobody has shown a limit supplies them.

    two-below : (α : V ℓ) → IsOrd α → IsLimit α → (γ : V ℓ) → ⟨ γ ∈ α ⟩
              → ∥ Σ[ β ∈ V ℓ ] (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩) ∥₁

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If a
limit does not supply the intermediate `β`, the task stops at its cheapest
point and the leg needs a ruling.

ESTIMATE for W3: about 20 lines and under 35 seconds. **Do not fund it against
`[LJ-1.517]`'s census run**: that re-declared seven types and this proves one
ordinal fact.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO DELIVERS THE CONDENSATION LEG'S REMAINING BLOCKER**, and with
`[LJ-1.516]`'s transport it would leave `GraphSatAtStage` with every input in
hand.

**A NO-GO AT THE TWO STEPS SAYS DEVLIN 2.6(ii) IS NOT TRANSCRIBABLE AT THIS
TOWER**, which after nine dispatches is a ruling-grade finding and not a
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
  changed_files_none = ["agents/tasks/LJ-1-519/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-519/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-519/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-519/Probe519.agda"]
  changed_files_none = ["agents/tasks/LJ-1-519/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-519/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 219.404)
- CANDIDATE archive/dev/JOURNAL.md  (score 219.234)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 199.438)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 175.554)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 166.271)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 72.334)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 62.288)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 50.689)
- CANDIDATE dev/literature/digest.md  (score 49.885)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.154)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
