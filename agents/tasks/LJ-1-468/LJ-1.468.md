# LJ-1.468: the order formula restated, the way its own chapter restates one

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-468/Probe468.agda`:

    orderFo : (R P B C C₀ : S) → Formula S 1

the constructible name-order as a ONE-slot formula, with its five background
sets carried in TERM position, in the shape `appAtC` restates `appAt`
(`src/L/Choice/Before.lagda.md:1302-1303`). Land nothing in `src/`.

**`[LJ-1.455]` REFUTED THE REDUCTION MY EARLIER BRIEF ASKED FOR, AND THE DEFECT
WAS THE BRIEF'S.** Its report is a critic-upheld STOP
(`agents/tasks/LJ-1-455/lj-1.455-report.md`, `## WHAT THE NEXT BRIEF NEEDS`):
fixing seven of `≺At`'s eight slots at a single `a` is FALSE, and the telescope
I wrote mixed two different orders. `≺At` is the constructible NAME-order and
needs `R`, `P` and two names' data; it does not read an arbitrary
`w : SWO ⟪ fst a ⟫`. **This brief carries the five constants that report names
and asks for nothing about `w`.**

**READ THAT REPORT FIRST AND QUOTE ITS D-10.** If its verdict is not a stated
STOP, or the five constants it names are absent, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-468/Probe468.agda::orderFo"]

## SCOPE (write)
- agents/tasks/LJ-1-468/Probe468.agda
- agents/tasks/LJ-1-468/lj-1.468-report.md
- agents/tasks/LJ-1-468/review-of-orderFo.md
- agents/tasks/LJ-1-468/runs/

## PREMISES

1. `[LJ-1.455]` is a critic-upheld STOP and it names this restatement as the next brief's target. Basis: agents/tasks/LJ-1-455/lj-1.455-report.md:255
2. It records that the seven-slot reduction is FALSE and that the mixing was the brief's defect. Basis: agents/tasks/LJ-1-455/lj-1.455-report.md:257
3. `≺At` is at eight `Fin n` indices. Basis: src/L/Choice/Internal.lagda.md:741
4. Separation takes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
5. The carve names its bound before it builds the set. Basis: src/L/InjChain.lagda.md:468
6. `appAtC` is the delivered pattern for carrying a set in Term position. Basis: src/L/Choice/Before.lagda.md:1302
7. The chapter exists so the model's own separation can carve the order out as a set. Basis: src/L/Choice/Internal.lagda.md:5
8. It sits inside the LANDED `L⊨ZFC` import closure. Basis: src/Landmarks.lagda.md:76
9. `[LJ-1.454]` measured that Internal delivers the ORDER and not the RANK, and that stands. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:73
10. A refutation measures the site it names and never how far it extends. Basis: dev/LESSONS.md:3752
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`src/L/Choice/Internal.lagda.md` delivers `LexAt` (`:731`), `≺At` (`:741`),
`LeastNameAt` (`:910`) and `StepAt` (`:973`), all at many slot indices, and it
says in its own opening (`:5-10`) that it was written so separation could carve
the order out as a set. **Nothing outside that chapter reads `≺At`.**

`appAtC` (`src/L/Choice/Before.lagda.md:1302-1303`) shows the tree's own way to
move a set from a slot into Term position: `∃̇∈ (con F) ...`.

## WHAT IS MISSING

The one-slot form. Without it separation has nothing to consume, which is what
`[LJ-1.455]` measured.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND `[LJ-1.455]` ALREADY WROTE HALF OF IT.** Quote its
D-10 and quote `≺At`'s type. **Then say, for each of the eight slots, whether it
becomes a `con` in Term position, stays a bound variable, or has no home.** If a
slot has no home, name it and STOP: this brief does not know that the five
constants are the right five, and a sixth would be the finding.

**THE SHAPE.** Restate `≺At` with `R`, `P`, `B`, `C`, `C₀` as `con` arguments in
the `appAtC` shape, leaving ONE free variable. Do not import a probe. **Do not
touch `w`**: an arbitrary well-order is not this order, and mixing them is the
error this task exists to correct.

**DO NOT CARVE THE SET.** That was `[LJ-1.455]`'s obligation and it is not this
one. AD12 gives this brief one obligation: the formula.

**DO NOT POSTULATE AND DO NOT WEAKEN THE ORDER.** A restatement that drops a
conjunct is a different order.

**REQUIRED REPORT SECTION `## WHAT THE CARVE WOULD NOW COST`.** With the formula
in hand, state as a type what a carve of the order would take, name the bound it
would need, and give a price with its basis. **Do not carve it.** That is the
next brief and it needs this measurement first.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 110 lines in the probe, of which the obligation is
about 30. BASIS: `appAtC` is two lines at a small arity
(`src/L/Choice/Before.lagda.md:1302-1303`) and `≺At` carries eight indices, so
the restatement is that pattern eight times over with five moved to `con`.
`[LJ-1.455]`'s own probe measured 149 total lines reaching its stop. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the five constants are the right five.

    slots : the eight indices of ≺At, each assigned a home

**Before any term, write the eight-row table: index, what it names, and whether
it becomes `con`, stays free, or has no home. Typecheck NOTHING for this; it is
a reading.** Then write `orderFo`'s TYPE alone and typecheck that, with the body
omitted. **If the type will not form at five constants and one free variable,
the count is wrong and the corrected count IS the finding.**

ESTIMATE for W3: the table plus three lines, under 10 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES SEPARATION SOMETHING TO CONSUME**, which is what `[LJ-1.455]` found
absent, and it reopens the route `[LJ-1.454]` named: the order as a set first,
the rank afterwards.

**A NO-GO CORRECTS THE CONSTANT COUNT**, which no report has yet measured, and
that number is what any later carve must be written against.

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
  changed_files_any = ["agents/tasks/LJ-1-468/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-468-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-468/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-468/Probe468.agda"]
  changed_files_none = ["agents/tasks/LJ-1-468/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-468/review-of-*.md"]

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
