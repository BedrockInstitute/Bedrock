# LJ-1.499: the envK family at KValue, where the carrier is a value

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-499/Probe499.agda`:

    envK-family : (the five envK fields of TFacts, at KValue's frame)

**from `module EnvSet`, supplied with the `arityK` that `[LJ-1.495]`'s shift
delivers.** Land nothing in `src/`.

**`[LJ-1.495]` IS GO AND IT IS THE KEYSTONE THIS TASK STANDS ON.**
`tfacts-shared-from-kfacts` typechecks (`agents/tasks/LJ-1-495/Probe495.agda:166-199`,
median 3.17 s): twenty-six of `TFacts`'s fifty-nine fields are `KFactsCons`
iterated six times, read off at `TFacts`'s own indices.

**`arityK` IS NOT ONE OF THOSE TWENTY-SIX AND THAT IS THE POINT.** `TFacts` does
not carry `arityK`; `KFacts` does (`src/L/Condensation.lagda.md:6114`). So the
six-fold shift delivers a fact the target record cannot state, and **`module
EnvSet` wants exactly that fact** (`src/L/Condensation.lagda.md:2929-2937`),
together with `E∈K`, `ar∈K` and `envInK`.

**BUILD AT `KValue`'s FRAME, NOT AT `PropAgree`'s.** `[LJ-1.496]` is a
critic-upheld NO-GO which measured that the whole `PropAgree` to `AndAgree` to
`LowerAgree` to `AbstractFrame` chain is generic in `Fin` indices and binds no
stage (`agents/tasks/LJ-1-496/lj-1.496-report.md:78-82`), and that
`AbstractFrame` has no application anywhere in `src/`. **The mathematician has
ruled that this front specializes at `KValue`**, which is the one module that
binds `lam` and `gam` (`src/L/Condensation.lagda.md:7380-7383`) and where
`facts : KFacts` already exists.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-499/Probe499.agda::envK-family"]

## SCOPE (write)
- agents/tasks/LJ-1-499/Probe499.agda
- agents/tasks/LJ-1-499/lj-1.499-report.md
- agents/tasks/LJ-1-499/review-of-envK-family.md
- agents/tasks/LJ-1-499/runs/

## PREMISES

1. `[LJ-1.495]` is GO on the six-fold shift. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
2. Its obligation term is in its probe. Basis: agents/tasks/LJ-1-495/Probe495.agda:166
3. `KFacts` carries `arityK`. Basis: src/L/Condensation.lagda.md:6114
4. `TFacts` does not carry it, so the shift supplies what the record cannot state. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
5. `module EnvSet` is the delivered adequacy and names `arityK` in its telescope. Basis: src/L/Condensation.lagda.md:2929
6. It also wants `E∈K`, `ar∈K` and `envInK`. Basis: src/L/Condensation.lagda.md:2935
7. Its comment says the machine-to-story direction needs `envInK` only. Basis: src/L/Condensation.lagda.md:2926
8. The first field of the family is `envK-mem`. Basis: src/L/Condensation/TwelveAgree.lagda.md:186
9. `[LJ-1.496]` measured that the `PropAgree` chain binds no stage. Basis: agents/tasks/LJ-1-496/lj-1.496-report.md:78
10. `KValue` is the one module that binds the carrier. Basis: src/L/Condensation.lagda.md:7380
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**TWELVE DISPATCHES WENT AT ONE FIELD OF FIFTY-NINE AND THE THIRTEENTH LOOKED AT
THE OTHERS.** `[LJ-1.495]` paid twenty-six of them in one move. **This task is
the first to ask what the next family costs**, and it asks it at the only frame
where the carrier is a value rather than a parameter.

## WHAT IS MISSING

The four arguments of `EnvSet`, and the five readings off it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `EnvSet` wants four arguments. Say at `file:line`
where each comes from at `KValue`'s frame: `arityK` from the shift, `E∈K` and
`ar∈K` from somewhere you must name, and `envInK` from somewhere you must name.
**`envInK` IS THE ONE TO CHECK FIRST**, because `TFacts` states four `envInK-*`
fields of its own, so the fact `EnvSet` consumes may be the fact the record is
supposed to supply. **If that is circular, STOP AND SAY SO**: it would mean the
`envK-*` and `envInK-*` families cannot both come from `EnvSet` and the
mathematician must split them.

**BUILD ONE FIELD FIRST, `envK-mem`, AND THEN THE OTHER FOUR.** The five differ
only in their environment prefix and two slot indices. **If the first costs more
than a quarter of your budget, report that and build no more**: a family that
does not repeat is not a family, and saying so is worth more than four
half-finished terms.

**DO NOT BUILD A `TFacts` VALUE AND DO NOT FILL `someEnv`.** `[LJ-1.496]` closed
that question for now and thirty-three fields are out of scope. AD12 gives this
brief one obligation.

**DO NOT THREAD A STAGE THROUGH `LowerAgree` OR `AbstractFrame`.** `[LJ-1.496]`
measured that wall and the mathematician has ruled the other way.

**REQUIRED REPORT SECTION `## WHAT THE FAMILY COST`.** Give the line count of the
first field and of each of the other four, and say whether the pattern repeated.
**Do not price the remaining fields.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 200 lines in the probe, of which the obligation is
about 70. BASIS: `[LJ-1.495]` rebuilt this frame and the shift in a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `envInK` at `KValue`'s frame, because `EnvSet` consumes it and `TFacts`
also states it, and nobody has said which way that dependency runs.

    envInK-at-frame : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
                    → ⟨ fst z ∈ fst (lookup K γ) ⟩

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If it
can only be had by assuming a `TFacts` value, the route is circular, the task
stops at its cheapest point, and the finding reshapes this whole front.

ESTIMATE for W3: about 35 lines and under 45 seconds. **Do not fund it against
`[LJ-1.495]`'s 2.44 s**: that measured a record shift and this measures a
membership under a satisfaction hypothesis.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS FIVE MORE FIELDS AND CONFIRMS THE SPECIALIZATION RULING**, which
would make `KValue` the frame every later brief on this front targets.

**A NO-GO AT W3 SAYS THE ADEQUACY MODULE AND THE RECORD WANT THE SAME FACT FROM
EACH OTHER**, which is a circularity nobody has named, and it would change what
`TFacts` is for.

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
  changed_files_none = ["agents/tasks/LJ-1-499/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-499/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-499/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-499/Probe499.agda"]
  changed_files_none = ["agents/tasks/LJ-1-499/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-499/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 215.100)
- CANDIDATE archive/dev/JOURNAL.md  (score 159.916)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 146.692)
- CANDIDATE dev/ARCHIVE.md  (score 141.485)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 132.141)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.918)
- CANDIDATE dev/literature/digest.md  (score 45.912)
- CANDIDATE dev/literature/devlin-II5.md  (score 42.195)
- CANDIDATE dev/literature/geology.md  (score 34.984)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 33.213)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
