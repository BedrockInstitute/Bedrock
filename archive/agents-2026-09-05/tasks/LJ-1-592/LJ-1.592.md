# LJ-1.592: any coded injection of Lset α into α, because the target is a proposition

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-592/Probe592.agda`:

    stage-counted : <`[LJ-1.584]`'s `Reopener`: `InjL (Lset α) α`>

Land nothing in `src/`.

**`[LJ-1.584]` IS A NO-GO, UPHELD, AND IT SAYS MY BRIEF ASKED FOR MORE THAN THE
REOPENER SPENDS.** I asked for `Def` at `stage-card-upper`, a description of the
particular injection the chapter computes. **That is not what is needed.**

**ITS ROUTE 1, IN ITS OWN WORDS:**

> **"AIM AT `Reopener`, NOT AT `Obligation`.** `InjL (Lset α) α` is `sq`-free
> and truncated. A next brief may assume `SqFam α` freely under `PT.rec`,
> because the target is a proposition, and then build ANY coded injection. **It
> does not have to describe the one the chapter happens to compute.**"

**THAT IS THE WHOLE IDEA AND IT DISSOLVES THE WALL FOUR TASKS HIT.**
`[LJ-1.533]`, `[LJ-1.549]`, `[LJ-1.552]` and `[LJ-1.584]` each tried to describe
a given ambient function. **This brief builds a different one.**

**THE PROPOSITIONALITY IS MEASURED, NOT ASSUMED.** `isPropInjCode`
(`agents/tasks/LJ-1-576/Probe576.agda:77-84`) is green at today's tree, and
`InjL` is `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:38`).

**AND THE OBJECT GATES TWO ROWS.** Row 4 of `[LJ-1.564]`'s bill is
`StageCountedCoded` (`agents/tasks/LJ-1-523/Probe523.agda:258-261`), and
`[LJ-1.580]`'s row 1 residue is the stage-cardinality bound coded. **`[LJ-1.585]`
measured that one formula buys at most one of them, so do not claim both.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-592/Probe592.agda::stage-counted"]

## SCOPE (write)
- agents/tasks/LJ-1-592/Probe592.agda
- agents/tasks/LJ-1-592/lj-1.592-report.md
- agents/tasks/LJ-1-592/review-of-stage-counted.md
- agents/tasks/LJ-1-592/runs/

## PREMISES

1. `[LJ-1.584]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:12
2. Its route 1 aims at `Reopener` and not the obligation. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:123
3. It records that the brief asked for more than the reopener spends. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:77
4. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:38
5. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
6. Row 4 is `StageCountedCoded`. Basis: agents/tasks/LJ-1-523/Probe523.agda:258
7. `[LJ-1.585]` measured that one formula buys at most one row. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
8. `[LJ-1.587]` delivered a composite-pair producer at arbitrary L-elements. Basis: agents/tasks/LJ-1-587/Probe587.agda:259
9. It also delivered a subset-pair producer. Basis: agents/tasks/LJ-1-587/Probe587.agda:255
10. `[LJ-1.586]` is GO and coded `absorbs`. Basis: agents/tasks/LJ-1-586/lj-1.586-report.md:1
11. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Two general `InjL` producers from `[LJ-1.587]`, a coded `absorbs` from
`[LJ-1.586]`, and a measured propositionality. **No coded injection at this
pair.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FREEDOM.** Say at `file:line` exactly
what `PT.rec` lets you assume, and confirm the target is an hProp so the
recursion is legal. **If it is not, this route is closed and you say so at
once.**

**BUILD A DIFFERENT INJECTION, NOT A DESCRIPTION OF THE OLD ONE.** That is the
entire point. **If you find yourself describing `stage-card-upper`, you have
drifted back into `[LJ-1.584]`'s obligation, which is refuted.**

**`[LJ-1.587]`'S TWO PRODUCERS ARE THE OBVIOUS MATERIAL.** `injL-from-subset`
(`agents/tasks/LJ-1-587/Probe587.agda:255`) and `injL-compose` (`:259`) are both
at arbitrary L-elements and both conclude `InjL`. **Try them first, and say
whether they suffice.**

**DO NOT CLAIM BOTH ROWS.** `[LJ-1.585]` measured that this object buys at most
one. **Say which one you paid, and do not read a discharge into the other.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHICH INJECTION I BUILT`.** What it is, at
`file:line`, and why it is coded.

**REQUIRED REPORT SECTION `## WHICH ROW THIS PAYS`.** Row 4, row 1's residue, or
neither, with the term. **Do not read a discharge into anything you did not
inhabit.**

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.587]` built two producers at a comparable size and this consumes
them. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the legality of the recursion.

    -- isProp (InjL (Lset α) α), at this frame, INHABITED

**Write it FIRST and typecheck it ALONE.** The whole route rests on it.
ESTIMATE: about 10 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE TWO ROWS THAT HAVE RESISTED FIVE DISPATCHES**, and it
does so by changing the question rather than by out-working the wall.

**A NO-GO SHOWING THE TRUNCATION DOES NOT HELP CLOSES ROUTE 1**, and
`[LJ-1.594]` is already carrying route 2.

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
  changed_files_none = ["agents/tasks/LJ-1-592/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-592/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-592/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-592/Probe592.agda"]
  changed_files_none = ["agents/tasks/LJ-1-592/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-592/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 224.250)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 191.845)
- CANDIDATE archive/dev/JOURNAL.md  (score 179.205)
- CANDIDATE dev/ARCHIVE.md  (score 147.144)
- CANDIDATE archive/dev/DD-archived.md  (score 136.562)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 64.319)
- CANDIDATE dev/literature/digest.md  (score 51.207)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.525)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 32.221)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.032)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
