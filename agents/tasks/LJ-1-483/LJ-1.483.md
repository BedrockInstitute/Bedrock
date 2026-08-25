# LJ-1.483: someEnv where the truncation is actually in scope

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-483/Probe483.agda`:

    someEnv-at-codesK : someEnvDef {n} K γ

at a frame where `codesK` is a module hypothesis at the type
`src/L/Condensation.lagda.md:2782-2786` delivers, with the body transported from
`SupplyEnv.someEnv` (`src/L/Coding/EnvSupply.lagda.md:417-444`) and the numeral
truncation taken from `codesK`'s own third component. Land nothing in `src/`.

**THE MATHEMATICIAN HAS RULED BETWEEN `[LJ-1.480]`'s TWO READINGS AND THIS BRIEF
CARRIES THE RULING.** `[LJ-1.480]` is GO on the refutation
(`agents/tasks/LJ-1-480/lj-1.480-report.md:66`, committed `a1389de`): a
Kuratowski pair of two copies of `numeralL 0` is a member of the bound slot and
is not a numeral, so `someEnvDef` as stated cannot be inhabited from the
delivered supplier at `[LJ-1.457]`'s frame. It offered two readings and chose
neither, correctly.

**THE RULING IS READING 2.** Do not change `someEnvDef` and do not gate it.
`codesK` already delivers `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` as its third
component at the consuming site (`src/L/Condensation.lagda.md:2806`), so the
truncation is not missing from the argument; it is missing from the FRAME
`[LJ-1.457]` builds. **Inhabit the field where the consumer stands, not where the
frame stands.**

**READ `[LJ-1.480]` AND `[LJ-1.473]` FIRST.** If 480's verdict is not `GO`, write
nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-483/Probe483.agda::someEnv-at-codesK"]

## SCOPE (write)
- agents/tasks/LJ-1-483/Probe483.agda
- agents/tasks/LJ-1-483/lj-1.483-report.md
- agents/tasks/LJ-1-483/review-of-someEnv-at-codesK.md
- agents/tasks/LJ-1-483/runs/

## PREMISES

1. `[LJ-1.480]` is GO on the refutation and states the two readings without choosing. Basis: agents/tasks/LJ-1-480/lj-1.480-report.md:66
2. Its witness is a Kuratowski pair in the bound slot. Basis: agents/tasks/LJ-1-480/Probe480.agda:129
3. `someEnvDef` takes three memberships and no numeral fact. Basis: src/L/Condensation/LowerAgree.lagda.md:52
4. `SupplyEnv.someEnv` takes the numeral truncation as `arNum` and returns the environment with its membership. Basis: src/L/Coding/EnvSupply.lagda.md:417
5. `codesK` is a delivered parameter shape whose third component IS that truncation. Basis: src/L/Condensation.lagda.md:2782
6. The consuming site spends it as `arNum`. Basis: src/L/Condensation.lagda.md:2806
7. `[LJ-1.473]`'s W3 is GO: the carrier sits in slot 0 and the layout and the supplier share it. Basis: agents/tasks/LJ-1-473/lj-1.473-report.md:112
8. `[LJ-1.457]` is GO on the layout at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
9. `someEnv` is a field of `TFacts`, which has no inhabitant. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
10. `[LJ-1.113]` names it as the only construction among the 28. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Six dispatches have settled everything about this field except where to stand:
the layout (`[LJ-1.457]`), slot 0 (`[LJ-1.473]`), the supplier's membership
(`src/L/Coding/EnvSupply.lagda.md:425`), and now the refutation that fixes the
place (`[LJ-1.480]`).

## WHAT IS MISSING

The transport, at a frame that carries `codesK`.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `codesK`'s type and `SupplyEnv.someEnv`'s type
side by side. **Say, at `file:line`, that `codesK`'s third component is exactly
`arNum`'s type**, and say what `codesK` needs that this frame must supply: it
takes a code `c` and a shape equation before it yields anything
(`src/L/Condensation.lagda.md:2782-2806`). **If those inputs have no source at
this frame, name them and STOP.** That would mean the field is inhabitable only
deeper in the chain than anyone has looked, and it is the finding.

**THE SHAPE.** Take `codesK` as a MODULE HYPOTHESIS at its delivered type. Build
the frame with the carrier in slot 0, as `[LJ-1.473]` measured. Transport
`SupplyEnv.someEnv`, feeding `arNum` from `codesK`. Do not import a probe and do
not re-derive `[LJ-1.457]`'s layout arithmetic.

**DO NOT CHANGE `someEnvDef` AND DO NOT GATE IT.** That is Reading 1 and it is
not the ruling. **If the work forces Reading 1, say so plainly and stop**: a
coder's evidence outranks a mathematician's ruling, and that reversal is a full
return.

**DO NOT POSTULATE AND DO NOT BUILD THE OTHER 27.**

**REQUIRED REPORT SECTION `## WHERE THE FIELD LIVES`.** State, at `file:line`,
the site at which `someEnv` is now inhabitable and the site at which it is not,
and say whether `TwelveAgree.AbstractFrame` can reach the first.
**`TwelveAgree` takes `TFacts` as a whole**, so if the field is inhabitable only
under `codesK`, `TFacts` may need splitting. Name that as a type; do not do it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 55. BASIS: `[LJ-1.473]` built the frame with slot 0 in about 170 lines and
reached its hole; this adds `codesK` and the transport. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `codesK` can be applied at this frame at all.

    arNum-from-codesK : ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

**Derive it from `codesK` alone, with the obligation omitted, and typecheck it
ALONE.** `codesK` wants a code `c` in the class carrier and a shape equation
before it yields the triple. **If neither has a source at this frame, the ruling
is wrong and the report must say so**, because then the field is not inhabitable
at the consumer either and both readings fail.

ESTIMATE for W3: about 15 lines and under 20 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST OF `[LJ-1.113]`'s 28 IN THE TREE**, at the site where it is
actually used, and it settles a seven-dispatch question.

**A NO-GO OVERTURNS THE RULING**, which is worth more than the field: it would
say the truncation has no source anywhere in the chain, and `TFacts` itself needs
restating.

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
  changed_files_none = ["agents/tasks/LJ-1-483/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-483/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-483-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-483/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-483/Probe483.agda"]
  changed_files_none = ["agents/tasks/LJ-1-483/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-483/review-of-*.md"]

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
