# LJ-1.535: keep the formula the stage counting already has

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-535/Probe535.agda`:

    stage-card-upper-coded :
        (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → (a Formula-carrying restatement of stage-card-upper's injection, from
         which an InjCode is reachable)

**at `L.StageCardinal`'s own site, where the formula is still in hand.** Land
nothing in `src/`.

**`[LJ-1.533]` IS A CRITIC-UPHELD NO-GO WITH A TYPE-LEVEL REASON.** It asked
what codes an arbitrary ambient injection and answered **NONE**, not by a count
but by the types: an L-element set comes from exactly two generators,
`hasSeparationL` (`src/L/Axioms/Full.lagda.md:144-146`) and `hasReplacementL`
(`:277-280`), **and both take a `Formula` in their type**. An ambient `_↪_` is
`Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)`
(`src/L/Cardinal.lagda.md:47-48`) and **carries no `Formula`**.

**SO THE ROUTE THAT IS DEAD IS "BUILD AMBIENT, THEN CODE IT". THE ROUTE
`[LJ-1.533]` NAMES AND NOBODY HAS PRICED IS "BUILD CODED AT THE CHAPTER'S OWN
SITE".**

**AND THE FORMULA IS THERE. I CHECKED IT.** `L.StageCardinal` imports
`FOL.Count using ( composed-count; code; shape-count-inj )`
(`src/L/StageCardinal.lagda.md:22`). `formula-bound` (`:177-180`) has DOMAIN
`Formula K 1`. `tuple-g` (`:100-102`) carries the parameters. **The counting is
SYNTACTIC at its origin, and `stage-card-upper` (`:564-565`) throws the formula
away by returning a bare `↪`.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-535/Probe535.agda::stage-card-upper-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-535/Probe535.agda
- agents/tasks/LJ-1-535/lj-1.535-report.md
- agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md
- agents/tasks/LJ-1-535/runs/

## PREMISES

1. `[LJ-1.533]` is a critic-upheld NO-GO and answered NONE with a type reason. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
2. It names this route as unpriced. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
3. `hasSeparationL` takes a `Formula`. Basis: src/L/Axioms/Full.lagda.md:144
4. `hasReplacementL` takes a `Formula`. Basis: src/L/Axioms/Full.lagda.md:277
5. `_↪_` carries no `Formula`. Basis: src/L/Cardinal.lagda.md:47
6. The chapter imports the syntactic counting. Basis: src/L/StageCardinal.lagda.md:22
7. `formula-bound` has domain `Formula K 1`. Basis: src/L/StageCardinal.lagda.md:177
8. `tuple-g` carries the parameters. Basis: src/L/StageCardinal.lagda.md:100
9. `stage-card-upper` returns a bare injection. Basis: src/L/StageCardinal.lagda.md:564
10. `InjCode` is what `InjL` wants. Basis: src/L/Cardinal.lagda.md:223
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**`[LJ-1.533]` CLOSED A ROUTE AND OPENED ANOTHER IN THE SAME REPORT.** The
generic ambient-to-coded bridge does not exist and cannot, and the chapter that
owns B9's shadow builds it from a formula. **Nobody has looked at that formula.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Open `src/L/StageCardinal.lagda.md` and follow
`stage-card-upper` back to the formula. **Say at `file:line` what `Formula`
`formula-bound` is applied to and whether it survives to `:564`.** If the
formula is consumed and discarded before the injection is formed, this route is
as dead as the other and you must say so: that would mean B9, B7 and B10 all
need a formula written from scratch, which is a price the mathematician must
carry.

**DO NOT REBUILD `stage-card-upper`.** It is delivered. **Restate it so the
formula survives**, and say what that restatement costs in lines.

**DO NOT CODE A BARE `↪`.** `[LJ-1.533]` proved it cannot be done and the proof
is a type argument, not a failed search.

**DO NOT BUILD `InjCode` ITSELF.** AD12 gives this brief one obligation, and
`[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.531]` are building the conjuncts over a
different carve. **Say what your term still owes them.**

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## DOES THIS SERVE B7 AND B10`.** `[LJ-1.523]`'s
rows B7 `AbsorbsAt` and B10 `SuccIntoPower` are the same shape as B9. **Say
whether their shadows are also built from a formula, at `file:line`, or say you
did not find them.** Do not build them.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 190 lines in the probe, of which the obligation is
about 55. BASIS: `[LJ-1.533]` opened both carriers and built its refutation in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the formula survives, because everything else follows from it and
the chapter's own type discards it.

    -- the Formula that formula-bound is applied to, at its file:line, still in
    -- scope where the injection is formed

**Do this FIRST, before any term, and write it into the report as you go.** If
the formula does not survive, the task stops at its cheapest point and three
rows of `[LJ-1.523]`'s list B are priced at a formula each.

ESTIMATE for W3: about 20 lines of reading and under 30 seconds of Agda. **Do
not fund it against `[LJ-1.533]`'s numbers**: that refuted a bridge and this
follows a term back to its origin.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS THE ONLY ROUTE `[LJ-1.533]` LEFT** and may serve B7 and B10 as
well, which would turn six unpaid inputs into three.

**A NO-GO SAYS EVERY CODED INJECTION MUST BE WRITTEN FROM ITS OWN FORMULA**,
which is a real price and the mathematician must carry it rather than a coder
discovering it three times.

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
  changed_files_none = ["agents/tasks/LJ-1-535/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-535/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-535/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-535/Probe535.agda"]
  changed_files_none = ["agents/tasks/LJ-1-535/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-535/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 225.718)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 190.030)
- CANDIDATE archive/dev/JOURNAL.md  (score 185.209)
- CANDIDATE dev/ARCHIVE.md  (score 143.992)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 124.414)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.734)
- CANDIDATE dev/literature/terms-2026-08.md  (score 56.088)
- CANDIDATE dev/literature/devlin-II5.md  (score 46.463)
- CANDIDATE dev/literature/digest.md  (score 44.021)
- CANDIDATE dev/literature/geology.md  (score 37.729)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
