# LJ-1.491: can the frame carry the hypothesis that has no home

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-491/Probe491.agda`:

    kvalue-with-omega :
        (lam : V ℓ) (ordλ : IsOrd lam)
        (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
        (∅∈λ : ⟨ ∅ ∈ lam ⟩)
        (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
        (ω∈γ : ⟨ ω ∈ˢ gam ⟩)
      → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv

`KValue`'s own record, rebuilt with `⟨ ω ∈ˢ gam ⟩` added to the telescope and
every existing field unchanged. Land nothing in `src/`.

**THE `someEnv` FIELD NEEDS TWO HYPOTHESES AND ONE OF THEM HAS NO HOME.**
`[LJ-1.488]` is GO: `SupplyEnv.someEnv` applies with both gates in scope and
refuses no argument, and there is no fourth unsourced input
(`agents/tasks/LJ-1-488/lj-1.488-report.md:108`, committed `2227f5a`). But its
costing section measures where each gate can be STATED: the numeral truncation
can go into `someEnvDef` because it mentions only `ar`, while
**`⟨ ω ∈ sucV gam ⟩` cannot be stated there at all, because `someEnvDef` does not
bind `gam`**. It also records that the clause `let`, `PropAgree` and `KValue`
each bind neither.

**`KValue` IS THE ONLY MODULE IN THE CHAIN THAT BINDS `gam`.** So it is the only
place the hypothesis can live. **This task asks whether it can live there without
breaking what `KValue` already delivers.**

**READ `[LJ-1.488]`'s `## WHAT THE DOUBLE GATE COSTS` FIRST.** If its verdict is
not `GO`, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-491/Probe491.agda::kvalue-with-omega"]

## SCOPE (write)
- agents/tasks/LJ-1-491/Probe491.agda
- agents/tasks/LJ-1-491/lj-1.491-report.md
- agents/tasks/LJ-1-491/review-of-kvalue-with-omega.md
- agents/tasks/LJ-1-491/runs/

## PREMISES

1. `[LJ-1.488]` is GO: the supplier applies with both gates and refuses no argument. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:108
2. Its costing measures that `someEnvDef` cannot state `ω∈γ` because it does not bind `gam`. Basis: agents/tasks/LJ-1-488/Probe488.agda:78
3. `KValue` binds `gam` in its telescope. Basis: src/L/Condensation.lagda.md:7380
4. It inhabits `KFacts` with terms and no hole. Basis: src/L/Condensation.lagda.md:7410
5. `[LJ-1.467]` inhabited the negation of `ω∈γ` at `lam = ω`, `gam = ∅`, a legal instance today. Basis: agents/tasks/LJ-1-467/lj-1.467-report.md:60
6. `[LJ-1.485]` measured the same type empty at that instance. Basis: agents/tasks/LJ-1-485/Probe485.agda:115
7. `[LJ-1.457]` is GO on the 24-field prefix transfer at that frame. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
8. `KValue`'s consumer is `KFactsCons`, its own `consed`. Basis: src/L/Condensation.lagda.md:7429
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`KValue` builds the fourteen-slot frame and inhabits `KFacts` at a real bound.
`[LJ-1.457]` transfers 24 of `TFacts`'s fields onto it. `[LJ-1.488]` shows the
supplier applies once both gates are hypotheses. **Only the placement of the
second gate is unsettled.**

## WHAT IS MISSING

Evidence that adding the hypothesis costs nothing. **This is a restriction, and a
restriction can break a consumer.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE POINT OF THE TASK.** Adding `ω ∈ gam` to
`KValue` EXCLUDES instances that are legal today, and `[LJ-1.467]` exhibited one
(`lam = ω`, `gam = ∅`). **So the question is not whether the record still builds;
it is whether anything legitimate needs the excluded instances.**

**Run this first and put the output in the report**:
`grep -rn "KValue" src/` and, for every consumer, say at `file:line` whether the
`gam` it passes is infinite. **If any consumer passes a finite stage, the
restriction is wrong and the task is a NO-GO with that consumer named.** That
answer is the deliverable whether or not the term is written.

**THE SHAPE.** Rebuild `KValue`'s telescope with the extra hypothesis and its
`KFacts` record unchanged. Do not import a probe. **Do not use `ω∈γ` in any
field**: if a field needs it, the record is not what it was and the report must
say so.

**DO NOT EDIT `src/L/Condensation.lagda.md`.** This is a probe that shows the
restricted frame builds; whether to restrict the landed chapter is a mathematical
judgement and it returns to the mathematician.

**DO NOT POSTULATE AND DO NOT WEAKEN A FIELD TO MAKE THE HYPOTHESIS PAY.**

**REQUIRED REPORT SECTION `## WHO LOSES THE EXCLUDED INSTANCES`.** List every
`KValue` consumer at `file:line` with the `gam` it passes and whether that `gam`
is infinite. **That list is the deliverable and it is what the ruling will be
made from.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 60. BASIS: `KValue` is 55 lines including its fourteen index names
(`src/L/Condensation.lagda.md:7380-7434`), and this restates it with one more
binder. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the consumer census, and it is a grep before it is a term.

    consumers : every site that applies KValue

**Run `grep -rn "KValue" src/` FIRST, before any Agda, and put the result in the
report.** If the census shows a consumer at a finite `gam`, **stop there**: the
restriction is refuted and the term would be misleading work. If every consumer
is infinite, say so with the evidence and then build.

ESTIMATE for W3: one grep and a paragraph. **The census decides whether this task
is a build or a refutation, and it costs nothing.**

Report the median wall time and peak RSS over three forced rechecks for the full
file, if a full file is written.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES `ω∈γ` A HOME**, and with `[LJ-1.488]`'s application the `someEnv`
field becomes a two-site repair that the mathematician can rule on.

**A NO-GO NAMES A CONSUMER THAT NEEDS A FINITE STAGE**, which would mean the
hypothesis has no home anywhere in the chain and `TFacts.someEnv` cannot be
inhabited at all as the record is shaped. That is the larger result.

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
# THE ACCEPTANCE ITSELF CAN FAIL, AND NOTHING IN THIS TEMPLATE USED TO MATCH IT.
# MEASURED 2026-08-21 on LJ-1.469: the term was GREEN and its ratio was 0.0055,
# well under the bar, but acceptance conjunct 4 FAILED and the run exited 1.
# Every branch keyed on exit 0 or 42 missed, so the task parked `no-match` with a
# delivered obligation. An acceptance failure is a real event and it routes to a
# critic rather than to silence.
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-491/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-491/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-491-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-491/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-491/Probe491.agda"]
  changed_files_none = ["agents/tasks/LJ-1-491/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-491/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 203.028)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.680)
- CANDIDATE dev/ARCHIVE.md  (score 142.303)
- CANDIDATE archive/dev/DD-archived.md  (score 140.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.645)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.054)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.180)
- CANDIDATE dev/literature/digest.md  (score 42.507)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
