# LJ-1.467: someEnv from the supplier the tree already has

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-467/Probe467.agda`:

    someEnv-numeral : someEnvDef {9} iK' Kenv'

the `someEnv` field of `TFacts` at `[LJ-1.457]`'s re-laid-out frame, **with its
body taken from `SupplyEnv.someEnv`, which is delivered in `src/`.** Land
nothing in `src/`.

**`[LJ-1.463]` STOPPED ON A MEMBERSHIP AND ITS OWN REPORT NAMES THE SUPPLIER.**
That task built `Generic.envSetGen` as a term of `S` and could not put it in the
bound: `KFacts.numK0` is membership of `numeralL 0` and the bound's delivered
closures do not include `envSetK`
(`agents/tasks/LJ-1-463/lj-1.463-report.md:61`, committed `846f18c`). **Its
`## WHAT THE NEXT BRIEF NEEDS` orders exactly this task**, body from
`SupplyEnv.someEnv`, plus a transport from the four-slot frame onto `envHypB2`,
needing `ω∈γ`, the numeral truncation, and the carrier in slot 0.

**AND THE SUPPLIER CARRIES THE MEMBERSHIP `[LJ-1.463]` COULD NOT DERIVE.**
`SupplyEnv.someEnv` returns `E , (EK , henvB)` where `EK` is
`⟨ fst E ∈ Lset lam ⟩` (`src/L/Coding/EnvSupply.lagda.md:425-432`).

**READ `[LJ-1.463]`'s REPORT FIRST.** If its verdict is not a stated NO-GO, or
`[LJ-1.457]`'s layout is not GO, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-467/Probe467.agda::someEnv-numeral"]

## SCOPE (write)
- agents/tasks/LJ-1-467/Probe467.agda
- agents/tasks/LJ-1-467/lj-1.467-report.md
- agents/tasks/LJ-1-467/review-of-someEnv-numeral.md
- agents/tasks/LJ-1-467/runs/

## PREMISES

1. `[LJ-1.463]` is a critic-upheld NO-GO on the membership, and it names the supplier. Basis: agents/tasks/LJ-1-463/lj-1.463-report.md:61
2. `SupplyEnv.someEnv` is delivered and returns the environment with its membership. Basis: src/L/Coding/EnvSupply.lagda.md:417
3. Its body builds `E` from `Generic.envSetGen` and carries `EK`. Basis: src/L/Coding/EnvSupply.lagda.md:425
4. `[LJ-1.457]` is GO on the frame at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
5. Its delivered layout is at the probe that typechecked. Basis: agents/tasks/LJ-1-457/Probe457.agda:136
6. `someEnv` is a field of `TFacts`, which has no inhabitant. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
7. `someEnvDef` is stated in the lower agreement. Basis: src/L/Condensation/LowerAgree.lagda.md:52
8. `[LJ-1.113]` names `someEnv` as the only construction among the 28 and prices the whole set at about 250 lines. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
9. The bound's delivered closures are numerals, pairs and transitivity, and no environment set. Basis: src/L/Condensation.lagda.md:7415
10. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE MEMBERSHIP `[LJ-1.463]` COULD NOT DERIVE FROM `KFacts` IS DELIVERED
ELSEWHERE.** `src/L/Coding/EnvSupply.lagda.md:417-432` builds the environment
and returns its membership in the level. `[LJ-1.463]` tried to derive it from
the bound's closures instead, and the bound has none for this shape.

`[LJ-1.457]` settled the layout, so the frame this must land at is fixed and
measured.

## WHAT IS MISSING

The transport. `SupplyEnv.someEnv` is stated at a four-slot frame; `someEnvDef`
is stated at the twelve-row frame.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `SupplyEnv.someEnv`'s type
(`src/L/Coding/EnvSupply.lagda.md:417-424`) and `someEnvDef`
(`src/L/Condensation/LowerAgree.lagda.md:52-58`) side by side. **Name every slot
that differs and every hypothesis the supplier takes that the target does not
give**: `[LJ-1.463]` lists `ω∈γ`, the numeral truncation, and the carrier in
slot 0. **If one of those three has no source at this frame, say which and
STOP.**

**THE SHAPE.** Import `L.Coding.EnvSupply` and `L.Condensation.LowerAgree` from
`src/`. Rebuild `[LJ-1.457]`'s frame at its delivered layout; do not re-derive
the arithmetic and do not import a probe. Do W3 first. Then transport.

**DO NOT BUILD THE OTHER 27.** One field.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE THE TRANSPORT.**

**REQUIRED REPORT SECTION `## WHAT THE 27 NOW COST`.** `[LJ-1.113]`'s 250-line
figure is a hypothesis and `[LJ-1.463]` says not to fund the 25 closures against
its measurement. **Give your measured number for this one construction, and say
plainly that it does not price the closures**, which are a different shape.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.457]`'s probe runs about 170 lines for the frame plus 24
transfers, and `[LJ-1.463]` measured 1.90 s reaching the membership wall.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the three hypotheses the supplier takes, because `[LJ-1.463]` named them
and nobody has sourced them at this frame.

    supplies : ⟨ ω ∈ˢ fst γ₀ ⟩

**Take the first of the three, `ω∈γ`, state it at `[LJ-1.457]`'s frame, and
typecheck it ALONE with the obligation omitted.** The frame is built from a
limit bound and a stage below it (`src/L/Condensation.lagda.md:7380-7386`), so
either that gives `ω ∈ γ` or nothing at this frame does. **If it does not, the
supplier cannot be applied here whatever the transport costs, and the task stops
at its cheapest point.**

ESTIMATE for W3: about 8 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST OF `[LJ-1.113]`'s 28 IN THE TREE**, using a supplier that
was in `src/` the whole time, and it settles the one field of the 28 that is a
construction.

**A NO-GO SAYS THE DELIVERED SUPPLIER CANNOT BE APPLIED AT THIS FRAME**, and
names which of the three hypotheses has no source. That would be the honest
price of the condensation frame and `[LJ-1.113]` could not measure it from the
record alone.

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
  changed_files_any = ["agents/tasks/LJ-1-467/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-467-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-467/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-467/Probe467.agda"]
  changed_files_none = ["agents/tasks/LJ-1-467/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-467/review-of-*.md"]

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
