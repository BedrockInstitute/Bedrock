# LJ-1.520: a Levy grade for the level graph, which is what absoluteness is gated on

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-520/Probe520.agda`:

    levelFo-Σ₁ : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ

**a formula of an ABSOLUTE Levy grade that says what `LsetGraphAt` says**, at a
limit `α > ω`. Land nothing in `src/`.

**`[LJ-1.516]` IS A CRITIC-UPHELD NO-GO AND IT NAMED THE REAL OBSTRUCTION.**
Its one sentence for this brief: **"It is not the seam. It is the Levy grade of
`LsetGraphAt`, and that grade is REFUTED and not merely unbuilt. Relabelling
never changes the model; only absoluteness does; and absoluteness is gated on
`Δ₀`, `Σ₁` or `Π₁`, none of which this formula has."**

**THE SEAM I BRIEFED IS NOT THE PROBLEM AND IS ALREADY BUILT.**
`liftFo-correct` and `⊨-map` compose at the first attempt; `seam` is delivered
at `agents/tasks/LJ-1-516/Probe516.agda:72-77`, exit 0 on its first run. And
`transports-Δ₀` and `transports-Σ₁` are delivered too (`:115-122`, `:125-130`).
**The machinery works. The formula does not qualify for it.**

**THE SOURCE SAYS THE GRADE EXISTS AT A LIMIT.**
`dev/literature/devlin-II5.md:218-219`: "Uniform Δ₁ at limit α > ω
(`dev2.txt:674-686`, 2.6-2.7): for γ < α, `v = L_γ` iff `v ∈ L_α` and
`L_α ⊨ ∃z φ(z, v, γ)`". **So the orthodox route does not transport
`LsetGraphAt`. It replaces it with a graded formula at a limit.** Nine
dispatches transported the wrong object.

**AND `dev/literature/devlin-II5.md:217` NAMES WHY THE CURRENT ONE FAILS**:
"Strength: the existential over z is UNBOUNDED at the ambient level." That is
the unbounded quantifier that `src/L/Coding/Sequence.lagda.md:291-292` carries
and that no Levy grade admits.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-520/Probe520.agda::levelFo-Σ₁"]

## SCOPE (write)
- agents/tasks/LJ-1-520/Probe520.agda
- agents/tasks/LJ-1-520/lj-1.520-report.md
- agents/tasks/LJ-1-520/review-of-levelFo-sigma1.md
- agents/tasks/LJ-1-520/runs/

## PREMISES

1. `[LJ-1.516]` is a critic-upheld NO-GO and names the Levy grade as the obstruction. Basis: agents/tasks/LJ-1-516/lj-1.516-report.md:13
2. Every delivered route from `AbsL.⊨ᵐ` is gated on a Levy grade. Basis: agents/tasks/LJ-1-516/lj-1.516-report.md:107
3. The seam itself is delivered and was not the problem. Basis: agents/tasks/LJ-1-516/Probe516.agda:72
4. `transports-Σ₁` is delivered. Basis: agents/tasks/LJ-1-516/Probe516.agda:125
5. The Levy hierarchy has no constructor for an unbounded quantifier. Basis: src/FOL/LevyHierarchy.lagda.md:47
6. `GraphAt` carries that unbounded existential. Basis: src/L/Coding/Sequence.lagda.md:291
7. The source states the uniform Δ₁ grade at a limit. Basis: dev/literature/devlin-II5.md:218
8. It names the unbounded existential as the current strength. Basis: dev/literature/devlin-II5.md:217
9. `[LJ-1.514]` is GO and lifted the formula's carrier. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:103
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE TRANSPORT MACHINERY IS COMPLETE AND UNUSED.** `[LJ-1.514]` lifted the
carrier for the whole family, `[LJ-1.516]` built the seam and both graded
transports. **What is missing is a formula they accept.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read `src/FOL/LevyHierarchy.lagda.md` and say at
`file:line` which constructors `Σ₁` admits. **Then say whether the tree can
express `v = Lset γ` with a bounded existential at a limit.** If the Levy
hierarchy as delivered cannot state the source's formula, say which constructor
is missing and STOP: that is a fact about `src/FOL/`, not about condensation,
and it would be the first time this campaign has priced that chapter.

**W8. READ `dev/literature/devlin-II5.md` AND CHECK IT AGAINST
`dev/literature/devlin-errata.md` BEFORE YOU RELY ON IT.** Chapter II is among
the known errors. Quote what you take at `file:line`. `[LJ-1.519]` is running
the same source for a different statement; do not assume its reading.

**DO NOT TRANSPORT `LsetGraphAt` AGAIN.** `[LJ-1.516]` refuted its grade. Nine
dispatches moved the wrong object and the brief that ordered the tenth was
mine.

**DO NOT WEAKEN THE FORMULA'S MEANING TO BUY A GRADE.** A Σ₁ formula that does
not say `v = Lset γ` pays nothing. **The report must state the equivalence, as
a type, whether or not it is proved.**

**DO NOT ATTEMPT THE TRANSPORT, `GraphSatAtStage`, `cover` OR `levelIn`.**
AD12 gives this brief one obligation.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE GRADE COSTS`.** Name every hypothesis
the graded formula needs that `LsetGraphAt` does not, at `file:line`, and say
which are delivered. **The limit is expected to be one of them; say so if it
is not.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.516]` built the seam and two graded transports in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the bound on the existential, because that single quantifier is what
`[LJ-1.516]` measured no grade admits.

    -- the existential of GraphAt, with its witness bounded by a term

**Write it FIRST, as a type, and typecheck it ALONE.** If the witness cannot be
bounded by anything the object language can name, the graded formula cannot be
written and the task stops at its cheapest point with the reason quoted from
the Levy chapter.

ESTIMATE for W3: about 20 lines and under 35 seconds. **Do not fund it against
`[LJ-1.516]`'s numbers**: that composed two laws and this bounds a quantifier.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE DELIVERED TRANSPORT MACHINERY A FORMULA IT ACCEPTS**, which
is the only thing standing between `[LJ-1.516]`'s work and a usable transport.

**A NO-GO SAYS THE TREE'S LEVY HIERARCHY CANNOT STATE THE ORTHODOX FORMULA**,
which prices `src/FOL/LevyHierarchy.lagda.md` for the first time and is a
finding about the foundations rather than about condensation.

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
  changed_files_none = ["agents/tasks/LJ-1-520/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-520/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-520/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-520/Probe520.agda"]
  changed_files_none = ["agents/tasks/LJ-1-520/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-520/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 210.666)
- CANDIDATE archive/dev/JOURNAL.md  (score 207.458)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 200.492)
- CANDIDATE archive/dev/DD-archived.md  (score 154.109)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 152.466)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 94.289)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.372)
- CANDIDATE dev/literature/digest.md  (score 49.198)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 47.421)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.532)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
