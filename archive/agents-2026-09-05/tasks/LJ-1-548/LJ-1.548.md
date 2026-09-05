# LJ-1.548: B9 from the coding leg's own code

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-548/Probe548.agda`:

    stage-counted-coded :
        (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
      → InjL Lδ δ

which is B9, `StageCountedCoded` (`agents/tasks/LJ-1-523/Probe523.agda:258-261`).
Land nothing in `src/`.

**THIS BRIEF ASSUMES `[LJ-1.547]` CAME BACK GO.** It was assembling `InjCode`'s
four conjuncts into one value. **If it did not land, or landed NO-GO, STOP AT
THE D-10 AND SAY SO.** Do not assemble the conjuncts yourself.

**WHY THIS IS THE ROW THE CODING LEG WAS ALWAYS BUILDING FOR, AND NOBODY HAS
SAID IT.** B9 wants a CODED injection from `Lset δ` into `δ`
(`src/L/GCH.lagda.md:38` unfolds `InjL` to `InjCode`). **The coding leg has
spent five dispatches building exactly that**: `swo-rank′` (`[LJ-1.515]`),
`rankFo-adequate′` (`[LJ-1.521]`), then `InjCode`'s four conjuncts by
`[LJ-1.524]`, `[LJ-1.529]`, `[LJ-1.531]` and `[LJ-1.541]`. **The rank of a
member of a stage IS an ordinal below that stage's index.** `[LJ-1.546]`
confirmed the shape from the other side: B9's source is `Lset δ` and its target
is already an ordinal, so it needs no target enlargement
(`agents/tasks/LJ-1-546/lj-1.546-report.md`, `## WHAT B9 WANTS`).

**SO THE QUESTION IS NOT WHETHER A CODE EXISTS. IT IS WHETHER THE ASSEMBLED ONE
SITS AT B9'S PAIR.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-548/Probe548.agda::stage-counted-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-548/Probe548.agda
- agents/tasks/LJ-1-548/lj-1.548-report.md
- agents/tasks/LJ-1-548/review-of-stage-counted-coded.md
- agents/tasks/LJ-1-548/runs/

## PREMISES

1. B9's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:258
2. `[LJ-1.544]` counted B9 UNPAID and stated nowhere. Basis: agents/tasks/LJ-1-544/lj-1.544-report.md:1
3. `InjL` unfolds to a truncated `InjCode`. Basis: src/L/GCH.lagda.md:38
4. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
5. `[LJ-1.547]` was dispatched to assemble them. Basis: agents/tasks/LJ-1-547/LJ-1.547.md:1
6. `[LJ-1.546]` says B9's target is already an ordinal. Basis: agents/tasks/LJ-1-546/lj-1.546-report.md:1
7. `[LJ-1.515]` built `swo-rank′`. Basis: agents/tasks/LJ-1-515/lj-1.515-report.md:1
8. `[LJ-1.521]` built `rankFo-adequate′`. Basis: agents/tasks/LJ-1-521/lj-1.521-report.md:1
9. `[LJ-1.537]` built `approx-carve` and pinned its type. Basis: agents/tasks/LJ-1-537/lj-1.537-report.md:16
10. `[LJ-1.533]` measured a wall for a code of an AMBIENT injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

**SEVEN OF `[LJ-1.523]`'S TEN INPUTS ARE PAID**, three in `src/` and four in
probes, counted by `[LJ-1.544]`. **B5, B9 and B10 remain.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Check `[LJ-1.547]`'s outcome and say it at
`file:line`. Then say what pair its assembled `InjCode` sits at, and what pair
B9 wants. **Say whether they are the same pair before you build.**

**`[LJ-1.533]`'S WALL DOES NOT OBVIOUSLY APPLY HERE AND YOU MUST SAY WHETHER IT
DOES.** It measured that no term codes an ARBITRARY AMBIENT injection. B9's
injection is not arbitrary and not ambient: it is the rank, and the coding leg
built a formula for it. **If the wall does apply, name the step where it bites.
If it does not, say why in one sentence.**

**THE HYPOTHESIS `fst Lδ ≡ Lset (fst δ)` IS A PATH, NOT A DEFINITION.** Say how
you transport along it and whether the transport costs anything. `[LJ-1.529]`
measured one re-basing at 33 lines against an estimate of 11, so **do not
promise a transport before you measure it.**

**THE CONCLUSION IS TRUNCATED** (`InjL` is `∥ … ∥₁`, `src/L/GCH.lagda.md:38`).
You may use that.

**DO NOT BUILD B5 OR B10.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE PAIR`.** Say at `file:line` the pair the
assembled code sits at and the pair B9 wants, and what closed the gap.

**REQUIRED REPORT SECTION `## WHAT THE JOIN NOW STANDS AT`.** Count the ten
inputs again and name the unpaid ones. **Count, do not estimate.**

ESTIMATE: about 150 lines in the probe, of which the obligation is about 25 and
the rest transport. BASIS: `[LJ-1.529]`'s re-basing measured 33 lines and there
may be one here. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the pair the assembled code actually sits at.

    -- InjCode F Lδ δ, stated at B9's frame, TYPE ONLY, no inhabitant

**Write it FIRST and typecheck it ALONE.** If the type will not form at B9's
frame, the row is refuted at the top. ESTIMATE: about 12 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE JOIN TO EIGHT OF TEN AND CLOSES THE CODING LEG'S PURPOSE.**
Five dispatches built a code and this is the row it was for.

**A NO-GO NAMES THE GAP BETWEEN THE BUILT CODE AND B9'S PAIR**, which tells the
mathematician whether five dispatches of coding work reach the bridge at all.
That is worth as much as the GO.

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
  changed_files_none = ["agents/tasks/LJ-1-548/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-548/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-548/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-548/Probe548.agda"]
  changed_files_none = ["agents/tasks/LJ-1-548/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-548/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 186.989)
- CANDIDATE archive/dev/JOURNAL.md  (score 173.938)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 167.241)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 143.734)
- CANDIDATE archive/dev/DD-archived.md  (score 138.277)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 47.965)
- CANDIDATE dev/literature/devlin-II5.md  (score 47.076)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 45.964)
- CANDIDATE dev/literature/terms-2026-08.md  (score 42.084)
- CANDIDATE dev/literature/geology.md  (score 29.576)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
