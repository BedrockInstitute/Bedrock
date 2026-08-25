# LJ-1.485: the environment at the clause where its hypothesis is already bound

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-485/Probe485.agda`:

    env-at-clause :
        (ya yc b a ar c : S)
      → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      → ⟨ fst ya ∈ fst K ⟩ → ⟨ fst yc ∈ fst K ⟩ → ⟨ fst ar ∈ fst K ⟩
      → Σ S (λ E → ⟨ fst E ∈ fst K ⟩
          × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero K' ⟩)

`someEnvDef`'s conclusion with the numeral truncation ADDED as a hypothesis, at
`[LJ-1.457]`'s layout. Take the exact slot indices from
`src/L/Condensation/LowerAgree.lagda.md:52-58`. Land nothing in `src/`.

**`[LJ-1.483]` OVERTURNED THE MATHEMATICIAN'S RULING AND FOUND THE PLACE.** Its
W3 is GO twice over: `no-code` refutes every C-membership at the pad, and
`arNum-from-codesK` typechecks, but **the domain of `codesK` at that frame is
empty** (`agents/tasks/LJ-1-483/lj-1.483-report.md:88`, committed `813f4a0`). So
Reading 2 is dead. **The report then located the one site where the hypothesis IS
bound**: `src/L/Condensation.lagda.md:3509` binds `arNum` from binary `codesK`,
and `:3515` calls `someEnv` six lines later WITHOUT it.

**SO THE FIELD IS NOT INHABITABLE AND THE CLAUSE IS.** This task builds the
clause's version. It does not touch `TFacts`, `LFacts` or `someEnvDef`.

**READ `[LJ-1.483]` FIRST AND QUOTE ITS `## WHERE THE FIELD LIVES`.** If its
verdict is not a stated STOP, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-485/Probe485.agda::env-at-clause"]

## SCOPE (write)
- agents/tasks/LJ-1-485/Probe485.agda
- agents/tasks/LJ-1-485/lj-1.485-report.md
- agents/tasks/LJ-1-485/review-of-env-at-clause.md
- agents/tasks/LJ-1-485/runs/

## PREMISES

1. `[LJ-1.483]` is a critic-upheld STOP and it names both the dead route and the live site. Basis: agents/tasks/LJ-1-483/lj-1.483-report.md:88
2. It measured the domain of `codesK` empty at the pad frame. Basis: agents/tasks/LJ-1-483/Probe483.agda:90
3. `arNum` is bound at the clause from binary `codesK`. Basis: src/L/Condensation.lagda.md:3509
4. `someEnv` is called six lines later without it. Basis: src/L/Condensation.lagda.md:3515
5. `someEnvDef` takes three memberships and no numeral fact. Basis: src/L/Condensation/LowerAgree.lagda.md:52
6. `SupplyEnv.someEnv` takes the numeral truncation as `arNum` and returns the environment with its membership. Basis: src/L/Coding/EnvSupply.lagda.md:417
7. `[LJ-1.480]` refuted the numeral fact at the frame, so it cannot come from the memberships. Basis: agents/tasks/LJ-1-480/lj-1.480-report.md:66
8. `[LJ-1.473]`'s W3 is GO: the carrier sits in slot 0 and the layout and the supplier share it. Basis: agents/tasks/LJ-1-473/lj-1.473-report.md:112
9. `[LJ-1.457]` is GO on the layout at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
10. `[LJ-1.113]` names `someEnv` as the only construction among the 28. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Eight dispatches have settled this field's geography: the layout, slot 0, the
supplier's membership, the refutation of the numeral fact at the frame, the
emptiness of `codesK`'s domain there, and now the one call site where the
hypothesis is bound. **What no file has is the term.**

## WHAT IS MISSING

The application, at a telescope that carries `arNum`.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `someEnvDef` (`LowerAgree.lagda.md:52-58`) and
the clause's `let` block (`src/L/Condensation.lagda.md:3505-3515`) side by side.
**Say, at `file:line`, which of the supplier's inputs the clause binds and which
it does not.** `[LJ-1.473]` named three: `ω∈γ`, the numeral truncation, and the
carrier in slot 0. This brief hypothesises ONE of them, the truncation. **If
either of the other two is still unsourced at this telescope, name it and STOP**:
this task must not quietly gate all three.

**THE SHAPE.** Rebuild `[LJ-1.457]`'s layout at its delivered form with the
carrier in slot 0, as `[LJ-1.473]` measured. State the obligation with `arNum` as
a hypothesis. Apply `SupplyEnv.someEnv`. Do not import a probe and do not
re-derive the layout arithmetic.

**DO NOT EDIT OR RESTATE `someEnvDef`, `TFacts` OR `LFacts`.** Whether the field
should exist at all is a mathematical judgement and it is not this task's. **Say
what you find; do not act on it.**

**DO NOT POSTULATE. DO NOT GATE `ω∈γ` OR SLOT 0 SILENTLY.**

**REQUIRED REPORT SECTION `## WHAT THE FIELD SHOULD BECOME`.** With the term in
hand, state as types the two candidates and give evidence for each, without
choosing: the field gains the truncation in its own telescope, or the field is
removed and `SupplyEnv.someEnv` is inlined at
`src/L/Condensation.lagda.md:3515`. **Name what each would cost in edits to
landed chapters.** The choice returns to the mathematician.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.473]` built this layout with slot 0 in about 170 lines
and reached its hole; this adds one hypothesis and the application. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `ω∈γ`, because `[LJ-1.467]` REFUTED it at a legal instance of this frame
and this brief does not gate it.

    omega-source : ⟨ ω ∈ˢ fst gam ⟩

**Source it at the layout FIRST, with the obligation omitted, and typecheck it
ALONE.** `[LJ-1.467]` inhabited its negation at `lam = ω`, `gam = ∅`
(`agents/tasks/LJ-1-467/lj-1.467-report.md:60`). **So either this task's frame
excludes that instance, or the obligation needs `ω∈γ` gated as well and the
report must say so rather than hide it.** That is the likeliest death point and
it costs eight lines.

ESTIMATE for W3: about 8 lines and under 20 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO SETTLES AN EIGHT-DISPATCH QUESTION** and hands the mathematician a choice
between two concrete repairs, each priced in edits to landed chapters.

**A NO-GO NAMES THE SECOND UNSOURCED HYPOTHESIS**, which would mean the clause
site is not sufficient either and the field's whole neighbourhood needs
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
  changed_files_none = ["agents/tasks/LJ-1-485/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-485/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-485-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-485/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-485/Probe485.agda"]
  changed_files_none = ["agents/tasks/LJ-1-485/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-485/review-of-*.md"]

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
