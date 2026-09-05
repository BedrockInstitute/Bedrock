# LJ-1.455: the order this tree describes, carved into a set

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-455/Probe455.agda`:

    order-as-set :
        (a : S) (w : SWO ⟪ fst a ⟫) (bnd : S)
      → ((x y : S) → ⟨ x ∈ˢ fst a ⟩ → ⟨ y ∈ˢ fst a ⟩
                   → ⟨ pr (fst x) (fst y) ∈ fst bnd ⟩)
      → Σ[ R ∈ S ] ((z : S) → ⟨ z ∈ˢ R ⟩
          ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo a)))

where `orderFo a : Formula S 1` is the order comparison of
`src/L/Choice/Internal.lagda.md` with every slot but one fixed at `a`. **The
proof is ONE separation and nothing else.** Land nothing in `src/`.

**READ ONE REPORT BEFORE ANY AGDA.** `agents/tasks/LJ-1-454/lj-1.454-report.md`
is a critic-upheld STOP (`:73`) and it is the reason this task exists. Quote its
inventory at `:155-165`. **It measured that `L.Choice.Internal` delivers the
ORDER and not the RANK**, and it named the corrected target at `:178-182`:
inhabit the formula first, then carve. **This task is the first half of that,
and only the first half. Do not attempt the rank.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-455/Probe455.agda::order-as-set"]

## SCOPE (write)
- agents/tasks/LJ-1-455/Probe455.agda
- agents/tasks/LJ-1-455/lj-1.455-report.md
- agents/tasks/LJ-1-455/review-of-order-as-set.md
- agents/tasks/LJ-1-455/runs/

## PREMISES

1. `[LJ-1.454]` is a critic-upheld STOP: Internal delivers the order and not the rank. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:73
2. Its inventory names what Internal DOES deliver, with slot counts. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:157
3. The order comparison as a formula is `≺At`, eight slot indices. Basis: src/L/Choice/Internal.lagda.md:741
4. Separation in this tree takes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
5. The carve device names its bound BEFORE it builds the set, and spends one separation. Basis: src/L/InjChain.lagda.md:468
6. The chapter exists so that the model's own separation can carve the order out as a set. Basis: src/L/Choice/Internal.lagda.md:5
7. That chapter sits inside the LANDED `L⊨ZFC` import closure. Basis: src/Landmarks.lagda.md:76
8. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
9. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CHAPTER SAYS IN ITS OWN OPENING WHAT IT IS FOR, AND NOBODY HAS SPENT IT.**
`src/L/Choice/Internal.lagda.md:5-10`: the meta-level family of well-orders is
not speakable inside `L`, so the chapter writes the comparison as a formula
"so that the model's own separation can carve the order out as a set and the
choosing can be written down inside". The formulas are delivered (`:731`,
`:741`, `:910`, `:973`) and the chapter is load-bearing for a proved trophy.

**AND THE CARVE IS DELIVERED TOO.** `src/L/InjChain.lagda.md:468-490` separates
one formula over one bound and reads both directions back. `[LJ-1.429]` used it.

## WHAT IS MISSING

The two have never been put in one file. `grep -rn "≺At" src/` outside its own
chapter is what this task must run first and report.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `≺At` takes EIGHT slot indices
(`src/L/Choice/Internal.lagda.md:741-742`) and separation takes ONE
(`src/L/Axioms/Full.lagda.md:144`). **Write out how the other seven are fixed**,
in the shape `inclFo` uses at `src/L/InjChain.lagda.md:475`, and say whether the
reduction is a specialisation or a re-statement. If seven slots cannot be fixed
from `a` alone, name what else the formula needs and STOP: that is the finding.

**THE SHAPE.** Fix the slots, name the bound, separate once, read both
directions back. Do not import a probe. Do not build the rank. Do not build a
well-founded recursion.

**DO NOT POSTULATE AND DO NOT WEAKEN.** If the separation cannot be run at this
formula, the obstruction file is the deliverable.

**REQUIRED REPORT SECTION `## WHAT THE NEXT BRIEF NEEDS`.** State, as a type,
what a rank formula would quantify over once the order is a set. Do not build
it. Say whether the order-as-a-set makes a first-order rank description
possible, and give the evidence.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 30. BASIS: `src/L/InjChain.lagda.md:468-544` is 77 lines for the carve
plus its two readings at the inclusion formula. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the slot reduction, and it is the cheapest place this task can die.

    orderFo : (a : S) → Formula S 1

**Write it FIRST, typecheck it ALONE with the obligation omitted, and report the
result.** If `≺At`'s eight slots cannot be brought to one at a fixed `a`, the
separation has nothing to consume and the task stops there.

ESTIMATE for W3: about 20 lines and under 10 seconds. BASIS: `inclFo` is the
same move at a smaller arity (`src/L/InjChain.lagda.md:475`).

Report the median wall time and peak RSS over three forced rechecks.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE ORDER IN THE MODEL AS A SET**, which is what a first-order rank
description must quantify over, and it does it with the chapter's own formula.

**A NO-GO NAMES WHAT THE FORMULA STILL NEEDS.** `[LJ-1.454]` named the missing
rank formula; this would name what stands before it.

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
  changed_files_any = ["agents/tasks/LJ-1-455/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes review-of-LJ-1-455-<k>.md
  # beside the coder's leftover review-of-*.md. Without this exclusion the
  # escalation re-escalates itself and attempt_max parks the task PERMANENTLY.
  # MEASURED 2026-08-21 on LJ-1.448, 449, 450 and 451.
  changed_files_none = ["agents/tasks/LJ-1-455/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-455/Probe455.agda"]
  changed_files_none = ["agents/tasks/LJ-1-455/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-455/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 151.522)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 133.286)
- CANDIDATE archive/dev/JOURNAL.md  (score 128.489)
- CANDIDATE dev/ARCHIVE.md  (score 118.792)
- CANDIDATE archive/dev/DD-archived.md  (score 118.617)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.122)
- CANDIDATE dev/literature/devlin-II5.md  (score 38.534)
- CANDIDATE dev/literature/digest.md  (score 38.021)
- CANDIDATE dev/literature/terms-2026-08.md  (score 27.951)
- CANDIDATE dev/literature/primary-sources.md  (score 25.124)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
