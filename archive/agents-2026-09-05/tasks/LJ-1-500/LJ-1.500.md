# LJ-1.500: the two code readers, which decode rather than close

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-500/Probe500.agda`:

    codesK-family : (TFacts's codesK and codesK-un, at KValue's frame)

**from the code set's membership and the `arityK` that `[LJ-1.495]`'s shift
delivers.** Land nothing in `src/`.

**THESE TWO ARE NOT CLOSURE FACTS AND THAT IS WHY THEY GET THEIR OWN BRIEF.**
`codesK` (`src/L/Condensation/TwelveAgree.lagda.md:162-167`) takes a code in the
code set and an equation that DECOMPOSES it, and returns three memberships plus a
numeral truncation. `codesK-un` is the same at one fewer component. **A decoder
is a different shape from `envK-*`, which reads a satisfaction**, so this task
does not assume `[LJ-1.499]`'s route works and `[LJ-1.499]` does not assume this
one's.

**`[LJ-1.493]` ALREADY MEASURED THAT `codesK` APPLIES AT THIS FRAME.** Its W3
found `c∈` is the `:3505` binder, `shEq` computes from `shD`, and the domain is
not empty because `C` is a parameter
(`agents/tasks/LJ-1-493/lj-1.493-report.md:74-76`). **That measurement is of the
APPLICATION. This task supplies the field.** They are different directions and
you must not confuse them.

**`[LJ-1.483]` STOPPED HERE ONCE AND ITS STOP WAS A PROBE-FRAME ARTIFACT.** It
reported the domain of `codesK` empty at its own frame
(`agents/tasks/LJ-1-483/lj-1.483-report.md:93`), and `[LJ-1.493]` measured that
the real frame is richer. **Rebuild the real frame, as `[LJ-1.493]` did.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-500/Probe500.agda::codesK-family"]

## SCOPE (write)
- agents/tasks/LJ-1-500/Probe500.agda
- agents/tasks/LJ-1-500/lj-1.500-report.md
- agents/tasks/LJ-1-500/review-of-codesK-family.md
- agents/tasks/LJ-1-500/runs/

## PREMISES

1. `[LJ-1.495]` is GO on the six-fold shift. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
2. `KFacts` carries `arityK`, which `TFacts` does not state. Basis: src/L/Condensation.lagda.md:6114
3. `codesK` is the first reader field. Basis: src/L/Condensation/TwelveAgree.lagda.md:162
4. `codesK-un` is the same at one fewer component. Basis: src/L/Condensation/TwelveAgree.lagda.md:168
5. `[LJ-1.493]` measured that `codesK` applies at the real frame. Basis: agents/tasks/LJ-1-493/lj-1.493-report.md:74
6. `[LJ-1.483]`'s empty domain was measured at its own probe frame. Basis: agents/tasks/LJ-1-483/lj-1.483-report.md:93
7. `KValue` is the module that binds the carrier. Basis: src/L/Condensation.lagda.md:7380
8. `[LJ-1.496]` measured that the `PropAgree` chain binds no stage. Basis: agents/tasks/LJ-1-496/lj-1.496-report.md:78
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.495]` paid twenty-six fields. `[LJ-1.493]` proved the frame is rich enough
to apply a reader. **Nobody has supplied one.**

## WHAT IS MISSING

The decoding, and the numeral truncation that rides with it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `codesK` returns FOUR things: three memberships and
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`. **The truncation is not a closure fact and it
is not `arityK`.** Say at `file:line` where a numeral reading of `ar` can come
from at this frame. **If nothing supplies it, STOP AND SAY SO, and report the
three memberships separately**: three of four is a real measurement and a
fabricated fourth is not.

**BUILD `codesK` FIRST AND `codesK-un` SECOND.** The second should be the first
minus one component. **If it is not, say what differs.**

**DO NOT ASSUME `[LJ-1.499]`'s ROUTE.** That task reads a satisfaction through
`EnvSet`; this one decodes an equation. If you find yourself wanting `EnvSet`,
stop and say why, because that would mean the two families are one and the
mathematician split them wrongly.

**DO NOT BUILD A `TFacts` VALUE AND DO NOT FILL `someEnv`.** Thirty-three fields
are out of scope and AD12 gives this brief one obligation.

**REQUIRED REPORT SECTION `## WHERE THE NUMERAL COMES FROM`.** Name the source of
the truncation at `file:line`, or say NONE. **This section is the deliverable
even if the term is not built**, because the same truncation appears in nine
other fields of this record.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 60. BASIS: `[LJ-1.493]` rebuilt this frame and applied `codesK` in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the numeral truncation, because it rides with every reader and no dispatch
has ever named its source.

    ar-is-numeral : (ar : S) → (what this frame gives) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If it
will not form, every reader field is short by the same conjunct, and that is a
finding about ten fields rather than two.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.493]`'s 4.53 s**: that built an environment and this reads an arity.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS TWO MORE FIELDS AND NAMES THE NUMERAL SOURCE FOR TEN**, because the
same truncation conjunct appears across the reader and env families.

**A NO-GO AT W3 SAYS TEN FIELDS SHARE ONE MISSING INPUT**, which would be the
cheapest possible description of what this record still owes, and far better than
finding it out ten times.

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
  changed_files_none = ["agents/tasks/LJ-1-500/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-500/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-500/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-500/Probe500.agda"]
  changed_files_none = ["agents/tasks/LJ-1-500/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-500/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.487)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 188.438)
- CANDIDATE dev/ARCHIVE.md  (score 162.653)
- CANDIDATE archive/dev/JOURNAL.md  (score 155.910)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 137.038)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.041)
- CANDIDATE dev/literature/devlin-II5.md  (score 54.460)
- CANDIDATE dev/literature/digest.md  (score 47.371)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 36.714)
- CANDIDATE dev/literature/terms-2026-08.md  (score 33.419)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
