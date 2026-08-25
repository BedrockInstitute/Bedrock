# LJ-1.471: carve the order, now that separation has something to eat

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-471/Probe471.agda`:

    order-as-set :
        (R P B C C₀ bnd : S)
      → Σ[ Q ∈ S ] ((z : S) → ⟨ z ∈ˢ Q ⟩
          ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo R P B C C₀)))

the constructible name-order carved into a set by ONE separation, at
`[LJ-1.468]`'s delivered `orderFo`. Land nothing in `src/`.

**`[LJ-1.455]` COULD NOT DO THIS BECAUSE THE FORMULA DID NOT EXIST IN ONE-SLOT
FORM, AND `[LJ-1.468]` BUILT IT.** That GO is committed at `7dec192`: the eight
slots of `≺At` all have a home, the five constants are the right five, and
`orderFo` inhabits `(R P B C C₀ : S) → Formula S 1`
(`agents/tasks/LJ-1-468/Probe468.agda:78-87`). **Separation now has a
`Formula S 1` to consume.**

**READ `[LJ-1.468]`'s REPORT FIRST** (verdict at `:71`). If its verdict is not
`GO`, write nothing and stop. **Take `orderFo` from the probe that typechecked,
never from a brief.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-471/Probe471.agda::order-as-set"]

## SCOPE (write)
- agents/tasks/LJ-1-471/Probe471.agda
- agents/tasks/LJ-1-471/lj-1.471-report.md
- agents/tasks/LJ-1-471/review-of-order-as-set.md
- agents/tasks/LJ-1-471/runs/

## PREMISES

1. `[LJ-1.468]` is GO on `orderFo` at one free slot with five constants in Term position. Basis: agents/tasks/LJ-1-468/lj-1.468-report.md:71
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-468/Probe468.agda:78
3. `[LJ-1.455]` is a critic-upheld STOP whose obstruction was exactly the missing one-slot form. Basis: agents/tasks/LJ-1-455/lj-1.455-report.md:255
4. Separation takes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
5. The carve names its bound BEFORE it builds the set and spends one separation. Basis: src/L/InjChain.lagda.md:468
6. `[LJ-1.429]` used that route and got a code. Basis: agents/tasks/LJ-1-429/lj-1.429-report.md:84
7. The chapter exists so the model's own separation can carve the order out as a set. Basis: src/L/Choice/Internal.lagda.md:5
8. `[LJ-1.454]` measured that Internal delivers the ORDER and not the RANK, and that still stands. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:73
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The formula (`[LJ-1.468]`), the separation (`src/L/Axioms/Full.lagda.md:144`)
and the carve pattern (`src/L/InjChain.lagda.md:468-490`, used by `[LJ-1.429]`).
**Nothing outside its own chapter has ever read `≺At`.**

## WHAT IS MISSING

The bound, and the separation applied.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND THE BOUND IS THE WHOLE QUESTION.** The order is a
set of PAIRS. Separation carves a subset of a set you can NAME FIRST
(`src/L/InjChain.lagda.md:468-472` takes `bnd` as a parameter and `InclGraph`
supplies it from a stage bound at `:575-598`). **Say where the bound for pairs of
names comes from, at `file:line`, before you write a term.** This brief takes
`bnd` as a parameter deliberately: if no delivered term supplies one, that
absence is the finding and the next brief's whole target.

**THE SHAPE.** Rebuild `orderFo` at `[LJ-1.468]`'s delivered type. Apply
`hasSeparationL` once at `bnd`. Read both directions back. Do not import a probe.
Do not build the rank and do not touch `w`.

**DO NOT SUPPLY THE BOUND BY POSTULATE.** It is a parameter here. **Do not
inhabit it from a hypothesis you invent.**

**REQUIRED REPORT SECTION `## WHERE THE BOUND COMES FROM`.** Name every delivered
term in `src/` that could supply `bnd` for pairs of names, at `file:line`, and
say for each whether it fits. **If none fits, that list is worth more than the
obligation.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 30. BASIS: `src/L/InjChain.lagda.md:468-544` is 77 lines for a carve plus
its two readings, and `[LJ-1.468]`'s probe reached its GO in about 90 lines.
Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is whether the separation accepts this formula at all.

    sep-applied : Σ[ Q ∈ S ] _

**Apply `hasSeparationL bnd (orderFo R P B C C₀)` and typecheck THAT ALONE, with
the readings and the obligation omitted.** `orderFo`'s constants sit in Term
position, and separation has never been run against a formula built that way in
this tree. **If the application does not typecheck, the `appAtC` restatement
does not reach separation and that is the finding.**

ESTIMATE for W3: about 8 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE CONSTRUCTIBLE ORDER IN THE MODEL AS A SET**, which is what a
first-order rank description must quantify over, and it does it with the
chapter's own formula and one separation.

**A NO-GO NAMES EITHER THE MISSING BOUND OR THE SEPARATION'S REFUSAL**, and both
are measurements this campaign has never had.

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
  changed_files_none = ["agents/tasks/LJ-1-471/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-471/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-471-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-471/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-471/Probe471.agda"]
  changed_files_none = ["agents/tasks/LJ-1-471/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-471/review-of-*.md"]

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
