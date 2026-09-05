# LJ-1.561: are the five walls one wall

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-561/Probe561.agda`:

    one-wall : <a single statement W, together with a proof that W implies
                EACH of the five missing pieces below>

**State `W` yourself. Naming it well IS the deliverable.** Land nothing in
`src/`.

**FIVE DISPATCHES HAVE STOPPED AND EACH NAMED A MISSING PIECE. THEY LOOK LIKE
ONE PIECE AND NOBODY HAS CHECKED.**

| site | stopped by | what it could not get |
|---|---|---|
| B9 `StageCountedCoded` | `[LJ-1.533]` | a code for an ambient injection `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` |
| B7, the counting site | `[LJ-1.535]` | a code out of a bare Σ |
| `Link`, the residue's 4th | `[LJ-1.549]`, `[LJ-1.554]` | a formula describing an ambient assignment |
| the assignment | `[LJ-1.552]` | an L-set out of an ambient injection |
| `StageHigh` | `[LJ-1.536]` | a `Formula ⟪ A ⟫ 1` for `𝒟ₒ-intro` |

**`[LJ-1.552]` ALREADY SAW FOUR OF THE FIVE AS ONE SHAPE** and tabulated them
(`agents/tasks/LJ-1-552/review-of-succ-assignment.md:155`). **`[LJ-1.536]` is
the fifth and it came from the OTHER LEG**, which is why this is worth one task:
if the condensation leg and the GCH leg are blocked on one statement, one
payment clears both.

**TWO REPORTS ALREADY NAME THE SAME MACHINERY.** `[LJ-1.536]` says `𝒟ₒ-intro`
(`src/L/Constructible.lagda.md:301-304`) is the one route into a stage, that
`defSet` reads its formula under the world's INNER satisfaction
(`src/L/Definability.lagda.md:111-112`, `:146-147`) so **"every quantifier in it
ranges over the members of the stage and over nothing else"**, and that the one
bridge from an external formula to that reading is
`L.Axioms.Separation.AtStage` (`src/L/Axioms/Separation.lagda.md:119-135`,
`:199-231`) under two hypotheses: **the formula is Δ₀, and every constant in it
is a member of the stage.** `[LJ-1.557]` says its selection is **"a quantifier
over the whole L-carrier and not over a stage."**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-561/Probe561.agda::one-wall"]

## SCOPE (write)
- agents/tasks/LJ-1-561/Probe561.agda
- agents/tasks/LJ-1-561/lj-1.561-report.md
- agents/tasks/LJ-1-561/review-of-one-wall.md
- agents/tasks/LJ-1-561/runs/

## PREMISES

1. `[LJ-1.552]` tabulates four sites as one shape. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:155
2. `[LJ-1.536]` is a NO-GO at the door. Basis: agents/tasks/LJ-1-536/lj-1.536-report.md:1
3. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
4. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
5. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
6. Its first hypothesis is that the formula is Δ₀. Basis: src/L/Axioms/Separation.lagda.md:199
7. `[LJ-1.557]` is GO and its selection quantifies over the whole L-carrier. Basis: agents/tasks/LJ-1-557/lj-1.557-report.md:1
8. The two generators of an L-set both take a `Formula`. Basis: src/L/Axioms/Full.lagda.md:144
9. `hasReplacementL` takes a `Formula S 2`. Basis: src/L/Axioms/Full.lagda.md:277
10. `[LJ-1.516]` found the Levy grade to be the real obstruction on a sibling row. Basis: agents/tasks/LJ-1-516/lj-1.516-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Five stops, each careful, each green, each naming its own missing piece.
**No term relates any two of them.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER THE FIVE EVEN SHARE A FRAME.** Read
the five stop statements and say at `file:line` what carrier and what arity each
missing piece lives at. **If two of them cannot be stated in one file, say so
and reduce the claim to the ones that can.** A term relating three is worth more
than a claim about five.

**STATE `W` AS WEAKLY AS YOU CAN.** The value is in how little `W` assumes, not
in how much it implies. If `W` has to be as strong as the conjunction of the
five, it is not a finding and you should say so plainly.

**DO NOT BUILD `W`.** This brief asks whether one statement covers the five, not
whether it is true. `[LJ-1.526]` did exactly this half for B4 and `[LJ-1.528]`
built the other half afterwards.

**IF THE FIVE ARE NOT ONE, THAT IS THE RESULT AND IT IS WORTH THE TASK.** Say
which ones group and which stand alone. The campaign has been treating them as
five and would be treating them wrongly either way.

**DO NOT ATTEMPT ANY OF THE FIVE OBLIGATIONS THEMSELVES.** AD12 gives this brief
one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## W, STATED`.** The statement in full, with one
sentence on what it assumes.

**REQUIRED REPORT SECTION `## WHICH OF THE FIVE IT REACHES`.** A row per site,
each marked reached or not, each with the implication's name at `file:line` or
the reason it fails.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 55.
BASIS: `[LJ-1.526]` made a comparable reduction for one site; this attempts
five. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the five missing pieces can be written in one file at all.

    -- the five statements, imported or restated, side by side, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If they will not sit together, every
later claim about them is unmeasurable and you must say so before spending the
estimate. ESTIMATE: about 30 lines, under 3 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO MEANS ONE PAYMENT CLEARS BOTH LEGS**, and the mathematician can fund one
task instead of five.

**A NO-GO THAT SPLITS THE FIVE INTO GROUPS IS ALMOST AS GOOD**, because the
campaign is currently guessing at that grouping and this would measure it.

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
  changed_files_none = ["agents/tasks/LJ-1-561/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-561/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-561/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-561/Probe561.agda"]
  changed_files_none = ["agents/tasks/LJ-1-561/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-561/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 199.305)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 195.698)
- CANDIDATE archive/dev/JOURNAL.md  (score 193.834)
- CANDIDATE dev/ARCHIVE.md  (score 139.244)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 136.095)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 54.101)
- CANDIDATE dev/literature/devlin-II5.md  (score 53.195)
- CANDIDATE dev/literature/terms-2026-08.md  (score 50.973)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.602)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 36.002)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
