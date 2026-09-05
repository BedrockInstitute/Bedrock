# LJ-1.488: both gates at once, because three refutations say both are needed

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-488/Probe488.agda`:

    someEnv-doubly-gated :
        (ya yc b a ar c : S)
      → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      → ⟨ ω ∈ˢ fst gam ⟩
      → ⟨ fst ya ∈ fst K ⟩ → ⟨ fst yc ∈ fst K ⟩ → ⟨ fst ar ∈ fst K ⟩
      → Σ S (λ E → ⟨ fst E ∈ fst K ⟩
          × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero K' ⟩)

`someEnvDef`'s conclusion with BOTH missing hypotheses added, at `[LJ-1.457]`'s
layout with the carrier in slot 0. Take the slot indices from
`agents/tasks/LJ-1-485/lj-1.485-report.md`'s Candidate 1 and the layout from
`[LJ-1.457]`'s probe. Land nothing in `src/`.

**THREE GREEN REFUTATIONS SAY BOTH GATES ARE NEEDED, AND THE BRIEF CARRIES ALL
THREE.** `[LJ-1.467]` inhabited the negation of `ω∈γ` at `lam = ω`, `gam = ∅`.
`[LJ-1.480]` refuted the numeral fact at the same frame: the bound slot holds a
Kuratowski pair, which is not a numeral. `[LJ-1.485]` measured `⟨ ω ∈ sucV gam ⟩`
EMPTY at that legal instance and reports that both candidates "still lack `ω∈γ`"
(`agents/tasks/LJ-1-485/lj-1.485-report.md:157`, committed `dc6b40b`).

**EVERY EARLIER BRIEF ON THIS FIELD GATED ONE HYPOTHESIS OR NONE, AND EACH DIED
ON THE OTHER.** This one gates both, deliberately, and the report must say what
that costs.

**READ `[LJ-1.485]` FIRST AND QUOTE ITS CANDIDATE 1.** If its verdict is not a
stated STOP, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-488/Probe488.agda::someEnv-doubly-gated"]

## SCOPE (write)
- agents/tasks/LJ-1-488/Probe488.agda
- agents/tasks/LJ-1-488/lj-1.488-report.md
- agents/tasks/LJ-1-488/review-of-someEnv-doubly-gated.md
- agents/tasks/LJ-1-488/runs/

## PREMISES

1. `[LJ-1.485]` is a critic-upheld STOP and reports both candidates still lack `ω∈γ`. Basis: agents/tasks/LJ-1-485/lj-1.485-report.md:157
2. Its W3 measured the type empty at a legal instance of the layout. Basis: agents/tasks/LJ-1-485/Probe485.agda:115
3. It also confirmed the carrier sits in slot 0 at that instance. Basis: agents/tasks/LJ-1-485/Probe485.agda:102
4. `[LJ-1.480]` refuted the numeral fact at the frame. Basis: agents/tasks/LJ-1-480/lj-1.480-report.md:66
5. `[LJ-1.467]` inhabited the negation of `ω∈γ` at the same frame. Basis: agents/tasks/LJ-1-467/lj-1.467-report.md:60
6. `[LJ-1.483]` measured `codesK`'s domain empty at the pad, closing the other route. Basis: agents/tasks/LJ-1-483/lj-1.483-report.md:88
7. `SupplyEnv.someEnv` takes the numeral truncation and returns the environment with its membership. Basis: src/L/Coding/EnvSupply.lagda.md:417
8. `someEnvDef` takes three memberships and neither missing fact. Basis: src/L/Condensation/LowerAgree.lagda.md:52
9. `[LJ-1.457]` is GO on the layout at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
10. `[LJ-1.113]` names `someEnv` as the only construction among the 28. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Nine dispatches have mapped this field completely: the layout, slot 0, the
supplier and its membership, and three separate refutations fixing exactly which
hypotheses are missing and where. **Nothing about its geography is now unknown.**

## WHAT IS MISSING

The term, at a telescope that carries both facts.

## THE REASONING

**D-10, BEFORE ANY AGDA.** List the supplier's inputs and, for each, say whether
this telescope binds it: `arNum` and `ω∈γ` are hypotheses here, the three
memberships come from `someEnvDef`'s shape, and the carrier is in slot 0.
**If a FOURTH input is still unsourced, name it and STOP.** Three dispatches have
each found one more; a fourth would say the supplier cannot be applied at this
frame at all, and that is a bigger result than the term.

**THE SHAPE.** Rebuild `[LJ-1.457]`'s layout with the carrier in slot 0, as
`[LJ-1.485]` measured. State both gates. Apply `SupplyEnv.someEnv`. Do not import
a probe and do not re-derive the layout arithmetic.

**DO NOT EDIT `someEnvDef`, `TFacts` OR `LFacts`.** Whether the field should gain
these hypotheses is a mathematical judgement and it returns to the mathematician
with this report.

**DO NOT POSTULATE, AND DO NOT ADD A THIRD GATE SILENTLY.**

**REQUIRED REPORT SECTION `## WHAT THE DOUBLE GATE COSTS`.** State, at
`file:line` and as a count of edited chapters, what it would take to put both
hypotheses into `someEnvDef` (`LowerAgree.lagda.md:52-58`), and what it would
take instead to leave the field alone and inline `SupplyEnv.someEnv` at
`src/L/Condensation.lagda.md:3515`, where `arNum` is already bound.
**Say which of the two is smaller in edits to LANDED chapters. Do not choose.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 175 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.485]` built this layout with one gate in about 170 lines
and reached its W3; this adds one hypothesis and the application. Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the supplier's application itself, because no task has ever reached it.

    applied : Σ S (λ E → ⟨ fst E ∈ fst K ⟩ × _)

**Apply `SupplyEnv.someEnv` with both gates in scope, with the obligation's
satisfaction half omitted, and typecheck THAT ALONE.** Every earlier task on this
field died before the application. **If it still will not apply, the report must
say which argument it refuses**, because that is the fourth input and it changes
everything downstream.

ESTIMATE for W3: about 12 lines and under 25 seconds. **Do not fund it against
`[LJ-1.473]`'s or `[LJ-1.485]`'s seconds**: neither reached this line.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO SETTLES A NINE-DISPATCH QUESTION** and prices two concrete repairs to
landed chapters, one of which the mathematician then rules on.

**A NO-GO NAMES A FOURTH MISSING INPUT**, which would say the delivered supplier
cannot serve this field at any frame, and `[LJ-1.113]`'s 28 need re-classifying
rather than paying.

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
  changed_files_none = ["agents/tasks/LJ-1-488/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-488/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-488-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-488/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-488/Probe488.agda"]
  changed_files_none = ["agents/tasks/LJ-1-488/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-488/review-of-*.md"]

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
