# LJ-1.458: the formula this tree has never written, and both fronts need it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-458/Probe458.agda`:

    LsetAt : ∀ {n} → Fin n → Fin n → Formula S n

together with the one adequacy direction that makes it a description:

    lsetAt-out : ∀ {n} (x d : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ LsetAt x d ⟩
               → fst (lookup x γ) ≡ Lset (fst (lookup d γ))

**INHABIT IT FROM WHAT THE TREE ALREADY DELIVERS, OR REPORT THE INVENTORY AND
STOP.** Land nothing in `src/`.

**THIS IS `[LJ-1.454]`'s SHAPE AND IT IS DELIBERATE.** That task stated a type,
found the chapter did not inhabit it, reported the inventory and stopped, and
the critic upheld it (`agents/tasks/LJ-1-454/lj-1.454-report.md:73`). **A
NO-GO with an inventory is a full return here and the brief asks for it by
name.** Do not force an inhabitant.

**READ ONE REPORT BEFORE ANY AGDA.** `agents/tasks/LJ-1-451/lj-1.451-report.md`
is a critic-upheld NO-GO (`:66`, committed at `9222c45`). It measured that the
hull's `Code` has constructors `base` and `wit` only and that nothing names
`Lset`. Quote it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-458/Probe458.agda::LsetAt"]

## SCOPE (write)
- agents/tasks/LJ-1-458/Probe458.agda
- agents/tasks/LJ-1-458/lj-1.458-report.md
- agents/tasks/LJ-1-458/review-of-LsetAt.md
- agents/tasks/LJ-1-458/runs/

## PREMISES

1. `[LJ-1.451]` is a critic-upheld NO-GO: the hull's language cannot name `Lset`. Basis: agents/tasks/LJ-1-451/lj-1.451-report.md:66
2. The hull's `Code` has exactly two constructors, and `wit` is definable existence with earlier codes as parameters. Basis: src/L/Hull.lagda.md:72
3. `levelIn`, one of the two unpaid condensation hypotheses, asks that the collapse image be closed under `Lset` at its own ordinals. Basis: src/L/BoundedSubset.lagda.md:917
4. `cover`, the other one, concludes with a membership in `Lset γ` INSIDE the model. Basis: src/L/BoundedSubset.lagda.md:919
5. `Lset` is a function on the L-structure's own carrier. Basis: src/L/Constructible.lagda.md:222
6. **NO FORMULA IN THIS TREE NAMES IT.** `grep -rn "LsetAt\|lsetFo\|LsetFo\|isLsetAt\|levelAt" src` returns nothing. Basis: src/L/Constructible.lagda.md:222
7. The tree does build formulas of this class, with adequacy in both directions. Basis: src/L/Coding/Base.lagda.md:285
8. Separation consumes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A refutation measures the site it names and never how far that site extends. Basis: dev/LESSONS.md:3752
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**TWO SEPARATE BLOCKERS REDUCE TO ONE MISSING FORMULA, AND NEITHER REPORT SAID
SO.** `[LJ-1.451]` stopped because the hull cannot name `Lset`. `cover`
(`src/L/BoundedSubset.lagda.md:918-919`) concludes with `⟨ C.π y ∈ˢ Lset γ ⟩`,
a statement about a level, and it has no producer either. **Both want a
description of the constructible level, and this tree has none.**

The tree does know how to build such formulas: `src/L/Coding/Base.lagda.md`
carries `sglAt`, `pairAt`, `prAt` and `tagAt` with their adequacy, and
`src/L/Condensation.lagda.md` is 7,435 lines of formulas of this class with
agreement proofs.

## WHAT IS MISSING

The formula, and an honest price for it.

## THE REASONING

**W8 BINDS THIS TASK AND THE LITERATURE IS NOT DIGESTED FOR THIS HIERARCHY.**
`dev/literature/j-hierarchy.md:1` is titled for the J-hierarchy and its primary
source is Schindler and Zeman on fine structure; it documents condensation for
`J_α`, the RETIRED route's hierarchy. **This tree's `Lset` is not that
hierarchy, and no digest covers its definability.** Read the injected
LITERATURE block first. **If the literature shows this shape is an axiom with
no condition this tree meets, STOP: a literature NO-GO is a full return.**

**D-10, BEFORE ANY AGDA.** Run `grep -rn "LsetAt\|lsetFo\|levelAt\|isLevel" src`
and paste the result. Then inventory, at `file:line`, every formula in
`src/L/Coding/` and `src/L/Condensation.lagda.md` whose satisfaction mentions a
STAGE rather than a pair, a tag or a code. **If the inventory is empty, say so
in one line: that is the measurement this task exists to make.**

**THE SHAPE.** State `LsetAt`. Attempt `lsetAt-out` from the delivered pieces.
Do not import a probe. **Do not write a well-founded recursion inside a formula
by hand**: if the description needs one, name that as the finding.

**DO NOT POSTULATE, DO NOT ADD AN AXIOM, AND DO NOT WEAKEN `Lset` TO A
HYPOTHESIS.** A telescope that grows to close a case is the shape audit findings
F1 and F3 measured (`dev/pod/audit-2026-08-20.md:34`).

**REQUIRED REPORT SECTION `## WHAT BOTH FRONTS OWE`.** State, as types and at
`file:line`, `levelIn` and `cover`, and say in one sentence each whether this
formula would unblock it. **Do not claim it unblocks the condensation lemma**:
`cover` needs more than a formula and this task does not price that.

**REQUIRED REPORT SECTION `## THE PRICE`.** One best-effort figure for building
the formula and its two adequacy directions if this task does not land them,
with its basis named as a probe, a delivered comparable or a survey.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 90 lines if the inventory is empty and the task
stops at the statement; about 300 if the pieces exist and the adequacy runs.
BASIS: `src/L/Coding/Base.lagda.md:248-295` is 47 lines for four formulas with
their adequacy at a flat shape, and a stage is not flat. **The wide band is the
honest one and the report must narrow it with a measurement.** Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether ANY delivered formula mentions a stage.

    stage-mentioning : Formula S 2

**Before any obligation, state that type and try to inhabit it from ONE
delivered formula whose satisfaction speaks about `Lset` at a slot.**
Typecheck it alone. **If nothing in the tree inhabits it, the task's answer is
already the inventory and the obligation is a statement without a proof.** That
is a full return and the brief orders it.

ESTIMATE for W3: about 10 lines and under 10 seconds, or a grep and one
sentence if the inventory is empty.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES BOTH FRONTS THEIR MISSING PIECE.** `levelIn` gets a route through
the hull's `wit`, and `cover` gets a description its conclusion can be separated
against.

**A NO-GO IS THE LIKELIER RETURN AND IT IS WORTH AS MUCH.** It would be the
first measured statement of what the constructible level costs to describe in
this tree, and `[LJ-2.5]` cannot rule on the condensation front without it.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-458/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-458-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-458/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-458/Probe458.agda"]
  changed_files_none = ["agents/tasks/LJ-1-458/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-458/review-of-*.md"]

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
