# LJ-1.515: the replacement rank, on the re-based order

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-515/Probe515.agda`:

    swo-rank′ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ

**the rank whose bounding ordinal is taken over the PREDECESSORS**, by the
recursion on the re-based order. Land nothing in `src/`.

**`[LJ-1.513]` IS GO AND IT REMOVED THE OBSTRUCTION.** `preds`
(`agents/tasks/LJ-1-513/Probe513.agda:99-100`) forms, and it is not a weaker
set: `preds-is-a` (`:103-104`) proves `fst (preds a oa) ≡ fst a` by
extensionality, so it has exactly the members of `a`. The `[UnequalSorts]`
error that blocked this is gone.

**`[LJ-1.513]` ALSO NAMED WHAT REMAINS AND HOW.** Its own words: `Rank.go`'s
`boundingOrd` line takes the predecessor index in place of the padded carrier,
and `predAt` and `pred` (`agents/tasks/LJ-1-490/Probe490.agda:129-138`) are
deleted with the padding they exist to supply. **`viaRankFamily`
(`Probe513.agda:190-196`) shows the one line it needs is accepted.** The
recursion itself is not written and that is this task.

**WHY THE REPLACEMENT IS NEEDED AT ALL.** `[LJ-1.497]` is a critic-upheld
NO-GO that REFUTED the adequacy of `rankFo` to `swo-rank`
(`agents/tasks/LJ-1-497/Probe497.agda:435-451`), because `swo-rank` is never
`∅`. **The replacement must be `∅` at a minimal element.** That is the whole
point of taking the bound over the predecessors.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-515/Probe515.agda::swo-rank′"]

## SCOPE (write)
- agents/tasks/LJ-1-515/Probe515.agda
- agents/tasks/LJ-1-515/lj-1.515-report.md
- agents/tasks/LJ-1-515/review-of-swo-rank-prime.md
- agents/tasks/LJ-1-515/runs/

## PREMISES

1. `[LJ-1.513]` is GO and `preds` forms. Basis: agents/tasks/LJ-1-513/Probe513.agda:99
2. `preds` has exactly the members of `a`. Basis: agents/tasks/LJ-1-513/Probe513.agda:103
3. Its report names the recursion as what remains. Basis: agents/tasks/LJ-1-513/lj-1.513-report.md:5
4. `viaRankFamily` shows the needed line is accepted. Basis: agents/tasks/LJ-1-513/Probe513.agda:190
5. `[LJ-1.497]` refuted the old adequacy. Basis: agents/tasks/LJ-1-497/Probe497.agda:435
6. The old rank and its padding are in `[LJ-1.490]`'s probe. Basis: agents/tasks/LJ-1-490/Probe490.agda:129
7. `swo-rank`, the rank being replaced, is there too. Basis: agents/tasks/LJ-1-490/Probe490.agda:147
8. `_∈ₛ_` is delivered. Basis: src/V/Model.lagda.md:48
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**NINE DISPATCHES HAVE BUILT AND THEN CORRECTED THIS ROUTE.** The formula is
sound, its old adequacy is refuted, the obstruction to the predecessor set is
removed, and the one line the recursion needs is accepted. **What is missing is
the recursion.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Say at `file:line` what `Rank.go`'s `boundingOrd`
line reads today and what it must read instead. **If the recursion will not
terminate on the re-based order, name the failing case and STOP**: a rank that
does not terminate is not a rank, and that finding would send the counting leg
back for a ruling rather than to a tenth dispatch.

**DELETE THE PADDING, DO NOT KEEP IT.** `predAt` and `pred` exist to supply the
padded carrier. `[LJ-1.513]` says they go with it. **A recursion that keeps the
padding is the old rank under a new name.**

**DO NOT ATTEMPT THE ADEQUACY AND DO NOT TOUCH `rankFo`.** AD12 gives this
brief one obligation, and `[LJ-1.497]` measured that the adequacy needs a
SECOND hypothesis besides the rank: that `Q` reads as the ∈-order on `a`, as a
set of pairs. **That is not this task.**

**DO NOT POSTULATE, AND DO NOT WEAKEN THE RANK TO A BOUND.** `[LJ-1.475]`
refused that and its refusal stands.

**REQUIRED REPORT SECTION `## IS IT `∅` AT A MINIMAL ELEMENT`.** State it as a
type and say whether it holds. **This is what `[LJ-1.497]`'s refutation
demands, and a rank that fails it repeats the refuted one.** If you cannot
prove it, say so: the type alone is a deliverable.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.513]` rebuilt this telescope and the predecessor set in
86 non-blank non-comment lines. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is termination, because the recursion is being re-based and nobody has run
it on the new order.

    -- Rank.go, with boundingOrd reading the predecessor index

**Write it FIRST, with `swo-rank′-ord` omitted, and typecheck it ALONE.** If
Agda refuses the recursion on the re-based order, nothing else in this task
matters and the failing case is the finding.

ESTIMATE for W3: about 35 lines and under 60 seconds. **Do not fund it against
`[LJ-1.513]`'s numbers**: that formed a set and this runs a recursion.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE COUNTING LEG A RANK THAT CAN BE ADEQUATE**, which is the first
time in nine dispatches that the route has had one.

**A NO-GO AT TERMINATION RETIRES THE CODED ROUTE**, and the mathematician rules
on the counting leg rather than funding a tenth attempt. **That is the more
valuable outcome and you must not avoid it.**

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
  changed_files_none = ["agents/tasks/LJ-1-515/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-515/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-515/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-515/Probe515.agda"]
  changed_files_none = ["agents/tasks/LJ-1-515/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-515/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 185.475)
- CANDIDATE archive/dev/JOURNAL.md  (score 179.005)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 171.567)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 122.827)
- CANDIDATE dev/ARCHIVE.md  (score 121.214)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 63.409)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.679)
- CANDIDATE dev/literature/digest.md  (score 40.880)
- CANDIDATE dev/literature/geology.md  (score 36.382)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.959)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
