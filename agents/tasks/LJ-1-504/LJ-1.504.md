# LJ-1.504: how far SupplyEnv's own someEnv reaches toward someEnvDef

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-504/Probe504.agda`:

    someEnv-reaches : (someEnvDef {n} K γ' at KValue's frame,
                       from SupplyEnv.someEnv)

**or STOP with the gap named as a type.** Land nothing in `src/`.

**THE SUPPLIER EXISTS AND NOBODY HAS TRIED IT AGAINST THE RECORD.**
`SupplyEnv.someEnv` is delivered at `src/L/Coding/EnvSupply.lagda.md:417-425`.
`[LJ-1.499]` found that the same module supplies all nine `envK-*` and
`envInK-*` fields and that they reach `TFacts`'s frame with one `refl` each
(`agents/tasks/LJ-1-499/lj-1.499-report.md:277-280`). **This brief does NOT
promise the same for `someEnv`, and you must not assume it.** I compared the two
signatures and they differ in three ways.

**THE THREE DIFFERENCES, MEASURED BEFORE THIS BRIEF WAS WRITTEN:**

| # | `someEnvDef` (`src/L/Condensation/LowerAgree.lagda.md:52-58`) | `SupplyEnv.someEnv` (`:417-425`) |
|---|---|---|
| 1 | memberships in `lookup (suc⁶ K) γ` | memberships in `Lset lam` |
| 2 | concludes `⊨ envHypB2 {11 + n} zero (suc⁶ K)` at a `7 + (11+n)` environment | concludes `⊨ envSetB zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))` at a FOUR element environment |
| 3 | asks no numeral hypothesis | asks `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` |

**DIFFERENCE 1 IS THE FRAME IDENTIFICATION `[LJ-1.499]` ALREADY USED.**
**DIFFERENCE 3 IS THE GAP THAT COST TWELVE DISPATCHES**, and `[LJ-1.488]`
measured that `someEnvDef` does not bind what the truncation needs
(`agents/tasks/LJ-1-488/lj-1.488-report.md:278-279`). **DIFFERENCE 2 IS
UNMEASURED BY ANYBODY** and it is this task's W3.

**THE GATE IS SETTLED, SO USE IT AND DO NOT RE-OPEN IT.** `[LJ-1.503]` is GO and
measured that `envSetNumeral∈` asks `⟨ ω ∈ σ ⟩` at its own argument
(`src/L/Coding/Key.lagda.md:486`), that the call site pins `σ = sucV gam`, and
that `⟨ ω ∈ sucV gam ⟩` is therefore the weakest sufficient gate. **The
mathematician has ruled that a `TFacts` value carries that gate.** Take it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-504/Probe504.agda::someEnv-reaches"]

## SCOPE (write)
- agents/tasks/LJ-1-504/Probe504.agda
- agents/tasks/LJ-1-504/lj-1.504-report.md
- agents/tasks/LJ-1-504/review-of-someEnv-reaches.md
- agents/tasks/LJ-1-504/runs/

## PREMISES

1. `SupplyEnv.someEnv` is delivered. Basis: src/L/Coding/EnvSupply.lagda.md:417
2. `someEnvDef` is the type the record's field states. Basis: src/L/Condensation/LowerAgree.lagda.md:52
3. `TFacts.someEnv` is that type at the record. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
4. `[LJ-1.499]` is GO and reached nine sibling fields from the same module. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:20
5. Its sweep found `EnvSet` is a consumer and never a supplier. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:94
6. `[LJ-1.488]` measured that `someEnvDef` cannot state the numeral truncation. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:278
7. `[LJ-1.503]` is GO and settled the gate at the weakest sufficient form. Basis: agents/tasks/LJ-1-503/lj-1.503-report.md:5
8. `envSetNumeral∈` asks its gate at its own first argument. Basis: src/L/Coding/Key.lagda.md:486
9. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
10. `[LJ-1.496]` measured that the `PropAgree` chain binds no stage, so this is built at `KValue`. Basis: agents/tasks/LJ-1-496/lj-1.496-report.md:78
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIRTY NINE OF FIFTY NINE `TFacts` FIELDS ARE ACCOUNTED AT ONE FRAME**:
twenty six from `[LJ-1.495]`, four from `[LJ-1.501]`, nine from `[LJ-1.499]`.
**`someEnv` is the fortieth and it has cost more than the other thirty nine
together.**

## WHAT IS MISSING

The comparison, and whatever it shows.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND DIFFERENCE 2 IS THE WHOLE RISK.** `envSetB` at a
four element environment and `envHypB2` at a `7 + (11 + n)` element environment
are different formulas at different arities. **Say at `file:line` what each
asserts and whether one is the other under a renaming.** If no renaming carries
one to the other, **STOP AND STATE THE GAP AS A TYPE**: that is the deliverable,
and it would be the first time anybody has said precisely why the delivered
supplier does not fill the record's field.

**A STOP HERE IS A GOOD OUTCOME AND YOU MUST NOT AVOID IT.** Twelve dispatches
went at this field from the consumer's side. **This is the first from the
supplier's side**, and a clean statement of the remaining distance is worth more
than a term built by weakening the record's type.

**DO NOT WEAKEN `someEnvDef` AND DO NOT EDIT IT.** If the field's type is wrong,
that is a finding for the mathematician and not an edit for you.

**DO NOT RE-DERIVE THE NINE ENV FIELDS.** `[LJ-1.499]` delivered them and its
report forbids asking again.

**DO NOT RE-OPEN THE GATE.** `[LJ-1.503]` settled it and the mathematician has
ruled.

**REQUIRED REPORT SECTION `## THE THREE DIFFERENCES, RESOLVED OR NOT`.** One row
per difference in the table above, with what closed it or what remains, at
`file:line`. **State in one sentence whether `TFacts.someEnv` is now reachable
from the delivered supplier.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.499]` rebuilt this frame and reached nine fields in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is difference 2, because differences 1 and 3 both have measurements behind
them and this one has none.

    envSetB-to-envHypB2 : (the four element conclusion, renamed into the
                           record's environment)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
renaming does not exist, the task stops at its cheapest point and the report
carries the exact distance between the delivered supplier and the record's field.

ESTIMATE for W3: about 30 lines and under 45 seconds. **Do not fund it against
`[LJ-1.499]`'s 3.04 s**: that measured a membership and this compares two
formulas at different arities.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE FIELD THAT TWELVE DISPATCHES COULD NOT**, and takes the account
to forty of fifty nine at one frame.

**A NO-GO NAMES THE DISTANCE AS A TYPE**, from the supplier's side for the first
time, which tells the mathematician whether the remaining work is a renaming, a
new lemma, or a wrong field type.

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
  changed_files_none = ["agents/tasks/LJ-1-504/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-504/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-504/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-504/Probe504.agda"]
  changed_files_none = ["agents/tasks/LJ-1-504/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-504/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 215.262)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 174.419)
- CANDIDATE archive/dev/JOURNAL.md  (score 168.040)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 154.240)
- CANDIDATE archive/dev/DD-archived.md  (score 141.145)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 62.921)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 54.533)
- CANDIDATE dev/literature/digest.md  (score 45.518)
- CANDIDATE dev/literature/geology.md  (score 37.757)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.037)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
