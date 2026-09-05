# LJ-1.505: the environment vector nobody has ever written

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-505/Probe505.agda`:

    gammaPrime : S ^ (11 + 9)

**the `γ'` that a `TFacts` value at `KValue`'s frame would be stated over, with
every slot occupied by a named object.** Land nothing in `src/`.

**NO `TFacts` VALUE EXISTS, SO NOTHING HAS EVER CHOSEN THESE SLOTS.**
`[LJ-1.499]` says exactly that (`agents/tasks/LJ-1-499/lj-1.499-report.md:288-292`)
and hands the choice to the mathematician. **This task supplies the evidence for
that choice: it does not make it.** Build the vector, justify each slot by the
field or formula that names it, and report any slot nothing names.

**THE FRAME IS SOUND AND THAT IS MEASURED.** `[LJ-1.502]` is GO: all four rows
of `twelveB` survive `t0 := N0` and `t1 := N1`, because `t0` IS the tag-0 index
and `N0` IS the tag-0 index, so the two demands are the same statement
(`agents/tasks/LJ-1-502/lj-1.502-report.md:19-58`). **Take the identification.
Do not re-open it.**

**WHAT I MEASURED BEFORE WRITING THIS, SO YOU START FROM IT RATHER THAN FROM
NOTHING.** In `record TFacts` (`src/L/Condensation/TwelveAgree.lagda.md:129-332`)
the fields name `lookup (suc zero) γ'` twice and `lookup (suc (suc zero)) γ'`
four times, and `twelveAt (suc (suc zero)) (suc zero) zero` at `:494` names
slots two, one and zero. **Slots zero, one and two are spoken for. The other
three of the six front slots are named by nothing I found.** Confirm that
census yourself; it is a regex result and not a proof.

**THE GATE IS SETTLED.** `[LJ-1.503]` measured that the weakest sufficient gate
is `⟨ ω ∈ sucV gam ⟩` (`src/L/Coding/EnvSupply.lagda.md:111`) and the
mathematician has ruled that a `TFacts` value carries it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-505/Probe505.agda::gammaPrime"]

## SCOPE (write)
- agents/tasks/LJ-1-505/Probe505.agda
- agents/tasks/LJ-1-505/lj-1.505-report.md
- agents/tasks/LJ-1-505/review-of-gammaPrime.md
- agents/tasks/LJ-1-505/runs/

## PREMISES

1. `[LJ-1.499]` reports the free slots unspecified and hands the choice back. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:288
2. `[LJ-1.502]` is GO and the identification is free at the syntax and at the record. Basis: agents/tasks/LJ-1-502/lj-1.502-report.md:5
3. Its cost table shows all four affected rows survive. Basis: agents/tasks/LJ-1-502/lj-1.502-report.md:19
4. `TFacts` is stated over `γ' : S ^ (11 + n)`. Basis: src/L/Condensation/TwelveAgree.lagda.md:131
5. Its consumer names slots two, one and zero. Basis: src/L/Condensation/TwelveAgree.lagda.md:494
6. `Kenv` is the fourteen slot vector at `KValue`. Basis: src/L/Condensation.lagda.md:7389
7. `[LJ-1.495]` instantiated the record's indices at that vector. Basis: agents/tasks/LJ-1-495/Probe495.agda:169
8. `[LJ-1.503]` settled the gate at the weakest sufficient form. Basis: agents/tasks/LJ-1-503/lj-1.503-report.md:5
9. That gate is `SupplyEnv`'s own module hypothesis. Basis: src/L/Coding/EnvSupply.lagda.md:111
10. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIRTY NINE OF THE FIFTY NINE FIELD POSITIONS ARE ACCOUNTED AT THIS FRAME**,
by `[LJ-1.495]`, `[LJ-1.501]` and `[LJ-1.499]`. **Every one of them is stated
over a `γ'` that nobody has written.** This task writes it.

## WHAT IS MISSING

Twenty slots, and a reason for each.

## THE REASONING

**D-10, BEFORE ANY AGDA.** The vector has `11 + 9` slots. Fourteen of them are
`Kenv`'s, reached under the six-fold shift `[LJ-1.495]` built. **Six are in
front of it and they are the question.** Say at `file:line`, for each of the
six, which field or formula names it and what that use requires the slot to
hold. **A slot nothing names is a real answer: report it as UNCONSTRAINED and
put the junk value there**, and say which junk value and why.

**DO NOT INVENT A REQUIREMENT TO FILL A SLOT.** If three of the six are
unconstrained, the report says three, and the mathematician decides whether the
record should have had `11 + n` slots at all. **That is a better outcome than a
vector that looks fully justified because you reasoned backwards from what would
be convenient.**

**DO NOT BUILD A `TFacts` VALUE.** Twenty of the fifty nine fields are still
unaccounted, `[LJ-1.500]` and `[LJ-1.504]` hold two families, and AD12 gives
this brief one obligation. **The vector is the deliverable, not a value over
it.**

**DO NOT RE-OPEN THE IDENTIFICATION OR THE GATE.** `[LJ-1.502]` and
`[LJ-1.503]` settled those and both are GO.

**REQUIRED REPORT SECTION `## THE TWENTY SLOTS`.** One row per slot: its index,
its occupant, and the `file:line` of what requires that occupant, or the word
UNCONSTRAINED. **This table is the deliverable even if the vector does not
typecheck.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 35. BASIS: `[LJ-1.495]` and `[LJ-1.501]` each rebuilt this frame in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the length, because `Kenv` has fourteen slots, `γ'` has `11 + n`, and with
`n = 9` that is twenty, and nobody has written the vector that reconciles them.

    -- the six front slots, appended to Kenv, at the length the record demands

**Write it FIRST, with every front slot at a junk value, and typecheck the
LENGTH alone.** If `11 + 9` and `6 + 14` do not agree definitionally at this
frame, nothing else in this task matters and the arithmetic is the finding.

ESTIMATE for W3: about 12 lines and under 25 seconds. **Do not fund it against
`[LJ-1.495]`'s 2.44 s**: that measured a record shift and this measures a vector
length.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE MATHEMATICIAN THE FRAME DECISION'S EVIDENCE**, and it is the
last thing standing between thirty nine accounted positions and an actual
`TFacts` value.

**A NO-GO AT THE LENGTH SAYS THE RECORD AND THE FRAME DO NOT FIT**, which would
be a statement about the record's design that no dispatch has made, and it would
re-price every field brief on this front at once.

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
  changed_files_none = ["agents/tasks/LJ-1-505/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-505/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-505/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-505/Probe505.agda"]
  changed_files_none = ["agents/tasks/LJ-1-505/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-505/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 191.405)
- CANDIDATE archive/dev/JOURNAL.md  (score 182.935)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 180.609)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 162.725)
- CANDIDATE dev/ARCHIVE.md  (score 160.125)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.677)
- CANDIDATE dev/literature/devlin-II5.md  (score 54.301)
- CANDIDATE dev/literature/digest.md  (score 43.242)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.286)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 38.933)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
