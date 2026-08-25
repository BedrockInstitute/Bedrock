# LJ-1.533: B9, coding an ambient injection the tree already has

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-533/Probe533.agda`:

    StageCountedCoded :
        (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
      → InjL Lδ δ

**the stage injects into its own index, as an L-CODED injection.** Land nothing
in `src/`.

**`[LJ-1.528]` IS GO AND B4 IS PAID.** `CardAboveL` is a term
(`agents/tasks/LJ-1-528/Probe528.agda:638-643`), `succCardExists` is green
(`:696-697`), and `[LJ-1.523]`'s seven unpaid inputs are **six**. **B9 is next
because its ambient shadow is already delivered.**

**THE AMBIENT SHADOW.** `stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-565`) gives `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, an
AMBIENT injection, under two side conditions: `⟨ α ∈ˢ sucV α₀ ⟩` and
`⟨ α ∈ˢ ω ⟩ → Empty.⊥`. **`[LJ-1.523]` recorded it as B9's shadow
(`agents/tasks/LJ-1-523/lj-1.523-report.md`, list B). Nobody has coded it.**

**AND THE AMBIENT-TO-INTERNAL DIRECTION IS THE ONE THAT PAYS.** `[LJ-1.526]`
built the bridge and `[LJ-1.528]` spent it, at one line: `ordL`
(`agents/tasks/LJ-1-528/Probe528.agda:93-94`) says every ordinal is an
L-element. **`[LJ-1.528]` calls that the highest-value thing in its file and
says any task priced against "the set must be shown constructible" should be
re-priced against it.** This is such a task.

**BUT `InjL` WANTS A CODE, NOT A FUNCTION.**
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`).
**`ordL` makes the CARRIER constructible; it does not make the FUNCTION
coded.** That difference is this task's whole risk and the brief will not let
you skip it.

**DO NOT ASSUME THE CODING LEG'S `F` IS YOURS.** `[LJ-1.524]`, `[LJ-1.529]` and
`[LJ-1.531]` are building `InjCode`'s four conjuncts over the RANK carve, for a
different function. **Read what they deliver, use what fits, and say at
`file:line` what does not.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-533/Probe533.agda::StageCountedCoded"]

## SCOPE (write)
- agents/tasks/LJ-1-533/Probe533.agda
- agents/tasks/LJ-1-533/lj-1.533-report.md
- agents/tasks/LJ-1-533/review-of-StageCountedCoded.md
- agents/tasks/LJ-1-533/runs/

## PREMISES

1. `[LJ-1.528]` is GO and B4 is paid. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
2. `succCardExists` is green there. Basis: agents/tasks/LJ-1-528/Probe528.agda:696
3. `ordL` makes every ordinal an L-element in one line. Basis: agents/tasks/LJ-1-528/Probe528.agda:93
4. B9's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:258
5. Its ambient shadow is delivered. Basis: src/L/StageCardinal.lagda.md:564
6. `InjL` wants a code. Basis: src/L/GCH.lagda.md:37
7. `InjCode` is the coded injection. Basis: src/L/Cardinal.lagda.md:223
8. `[LJ-1.524]` closed the first conjunct over a different carve. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:1
9. `[LJ-1.529]` closed the second and paid the re-basing. Basis: agents/tasks/LJ-1-529/Probe529.agda:101
10. `[LJ-1.526]` built the ambient-to-internal bridge. Basis: agents/tasks/LJ-1-526/Probe526.agda:285
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE JOIN HAD SEVEN UNPAID INPUTS THIS MORNING AND HAS SIX.** `[LJ-1.523]`
priced it at the owner's instruction, `[LJ-1.526]` reduced B4 to one statement,
`[LJ-1.528]` built that statement. **B9 is the next with a delivered
predecessor.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `stage-card-upper` carries two side conditions,
`⟨ α ∈ˢ sucV α₀ ⟩` and `α ∉ ω`. **Say at `file:line` what `α₀` is and whether
B9's `δ` satisfies the first.** If B9's binding cannot supply it, the shadow
does not reach the obligation and you must say what would.

**THEN THE REAL QUESTION: CAN THE FUNCTION BE CODED.** An ambient `↪` is a
function with an injectivity proof. `InjCode F a b` asks for a SET `F` in the
model whose four conjuncts say the same thing. **Say at `file:line` what
delivers a code for an arbitrary ambient injection, or say NOTHING DOES.** If
nothing does, that is the finding, and it would say B9 needs the same coding
machinery the rank carve is building, at a second site.

**DO NOT WEAKEN `InjL` TO AN AMBIENT INJECTION.** The statement GCH consumes is
the coded one. An ambient injection pays nothing.

**DO NOT REBUILD `stage-card-upper` OR `ordL`.** Both are delivered; cite them.

**DO NOT TOUCH B5.** `[LJ-1.526]` and `[LJ-1.528]` both record that B5 wants an
AMBIENT fact out of an INTERNAL one, which is the direction that does not pay.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT CODES AN AMBIENT INJECTION`.** Name every
term in `src/` or in a probe that turns an ambient function into an `InjCode`,
at `file:line`, or say NONE. **This section is the deliverable even if the
obligation is not built, and it prices B7 and B10 as well, which are the same
shape.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 50. BASIS: `[LJ-1.528]` opened both carriers and built a cardinal
statement in a comparable file. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the coding of the function, because the carrier side is one line and the
function side is unmeasured.

    -- an InjCode for stage-card-upper's injection, or the reason there is none

**Do this FIRST, before the obligation, and write it into the report as you
go.** If no delivered term codes an ambient injection, three rows of
`[LJ-1.523]`'s list B are blocked by one missing piece and that is worth more
than this obligation.

ESTIMATE for W3: about 30 lines and under 45 seconds. **Do not fund it against
`[LJ-1.528]`'s numbers**: that built a cardinal and this codes a function.

## WHAT GO AND NO-GO EACH EARN

**A GO TURNS SIX UNPAID INPUTS INTO FIVE** and confirms the ambient-to-internal
route at a third site.

**A NO-GO NAMES ONE MISSING PIECE THAT BLOCKS THREE ROWS**, since B7 and B10
are the same shape, and that is a better answer than one more term.

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
  changed_files_none = ["agents/tasks/LJ-1-533/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-533/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-533/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-533/Probe533.agda"]
  changed_files_none = ["agents/tasks/LJ-1-533/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-533/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 180.740)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 171.389)
- CANDIDATE archive/dev/JOURNAL.md  (score 157.739)
- CANDIDATE dev/ARCHIVE.md  (score 148.027)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 135.921)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 59.350)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.285)
- CANDIDATE dev/literature/digest.md  (score 42.245)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.319)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 33.218)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
