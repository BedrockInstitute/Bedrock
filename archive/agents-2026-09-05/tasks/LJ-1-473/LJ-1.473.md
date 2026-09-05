# LJ-1.473: the frame with a carrier in slot zero and its side condition stated

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-473/Probe473.agda`:

    someEnv-gated : someEnvDef {9} iK' Kenv'

at a frame that **puts the carrier in slot 0** and carries `⟨ ω ∈ˢ fst gam ⟩`
as a STATED module hypothesis, with the body transported from
`SupplyEnv.someEnv` (`src/L/Coding/EnvSupply.lagda.md:417-444`). Land nothing in
`src/`.

**`[LJ-1.467]` REFUTED THE UNGATED FORM AND ITS REFUTATION IS WHY THIS BRIEF
STATES THE HYPOTHESIS.** That critic-upheld NO-GO inhabited the NEGATION of the
supplier's first hypothesis at a LEGAL instance of `[LJ-1.457]`'s frame:
`KValue` accepts `lam = ω` and `gam = ∅`, and there `⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥`
typechecks (`agents/tasks/LJ-1-467/lj-1.467-report.md:60`, committed `4207425`).
**So no ungated `someEnv` can exist at that frame. The hypothesis is not
decoration and this brief does not hide it.**

**AND `[LJ-1.467]` NAMED THE SECOND DEFECT.** The six fillers of `Kenv'` are
dummy `numeralL 0`, while `envHypB2` reads slot 0 as `B` and the supplier uses
the carrier `LsetS gam`. **A brief that reuses the dummy cannot work.** Put the
carrier in slot 0.

**READ `[LJ-1.467]` AND `[LJ-1.457]` FIRST.** If either verdict is missing, write
nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-473/Probe473.agda::someEnv-gated"]

## SCOPE (write)
- agents/tasks/LJ-1-473/Probe473.agda
- agents/tasks/LJ-1-473/lj-1.473-report.md
- agents/tasks/LJ-1-473/review-of-someEnv-gated.md
- agents/tasks/LJ-1-473/runs/

## PREMISES

1. `[LJ-1.467]` is a critic-upheld NO-GO that inhabited the negation of the first hypothesis at a legal frame instance. Basis: agents/tasks/LJ-1-467/lj-1.467-report.md:60
2. It names the slot-0 defect and forbids reusing the dummy filler. Basis: agents/tasks/LJ-1-467/lj-1.467-report.md:143
3. `[LJ-1.457]` is GO on the layout at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
4. `SupplyEnv.someEnv` is delivered and returns the environment with its membership. Basis: src/L/Coding/EnvSupply.lagda.md:417
5. Its body builds `E` and carries `EK`. Basis: src/L/Coding/EnvSupply.lagda.md:425
6. `someEnvDef` is stated in the lower agreement. Basis: src/L/Condensation/LowerAgree.lagda.md:52
7. `someEnv` is a field of `TFacts`, which has no inhabitant. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
8. `KValue` builds the frame from a limit bound and a stage below it. Basis: src/L/Condensation.lagda.md:7380
9. `[LJ-1.113]` names `someEnv` as the only construction among the 28. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
10. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The layout (`[LJ-1.457]`), the supplier with its membership
(`src/L/Coding/EnvSupply.lagda.md:417-444`), and a measured refutation of the
ungated form (`[LJ-1.467]`). **What no file has is the gated form.**

## WHAT IS MISSING

The transport, at a frame that admits it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote the supplier's type and `someEnvDef` side by
side. **List the three hypotheses `[LJ-1.467]` named, and for each say its source
at this frame**: `ω∈γ` is now a stated module hypothesis, the numeral truncation
and the carrier in slot 0 are not. **If either of the other two has no source,
name it and STOP.** This brief gates ONE of the three deliberately; gating all
three would make the obligation vacuous.

**THE SHAPE.** Rebuild `[LJ-1.457]`'s frame at its delivered layout, **with the
carrier `LsetS gam` in slot 0 instead of the dummy**. State `⟨ ω ∈ˢ fst gam ⟩`
as a module hypothesis. Transport `SupplyEnv.someEnv` onto `someEnvDef`. Do not
import a probe and do not re-derive the layout arithmetic.

**DO NOT GATE THE OTHER TWO HYPOTHESES.** If they need gating too, that is the
finding and the report says so as types.

**DO NOT POSTULATE AND DO NOT BUILD THE OTHER 27.**

**REQUIRED REPORT SECTION `## WHAT THE GATE COSTS`.** A gated `someEnv` is
weaker than the field `TFacts` declares. **State, as a type, the difference
between what you built and `TFacts.someEnv`**, and say whether any consumer can
discharge `⟨ ω ∈ˢ fst gam ⟩` at the site it is spent. **Do not claim the field.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 50. BASIS: `[LJ-1.457]`'s probe runs about 170 lines for the frame plus 24
transfers, and `[LJ-1.467]` reached its refutation in about the same. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is slot 0, because `[LJ-1.467]` measured that the dummy is wrong and nobody
has put the carrier there.

    slot-zero : fst (lookup zero Kenv') ≡ fst (LsetS gam ordγ)

**Rebuild the frame with the carrier in slot 0 and typecheck THAT ALONE, with
the obligation omitted.** `[LJ-1.457]`'s 24-field transfer was measured at the
dummy layout; **moving slot 0 may break it, and if it does, the layout and the
supplier cannot both be satisfied at one frame.** That is the finding and it
outranks the obligation.

ESTIMATE for W3: about 15 lines and under 20 seconds. **Do not fund it against
`[LJ-1.457]`'s 2.20 s: that measurement was at a different layout.**

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST OF `[LJ-1.113]`'s 28 IN THE TREE, GATED**, and names
exactly what the gate costs.

**A NO-GO SAYS THE LAYOUT AND THE SUPPLIER CANNOT BOTH BE SATISFIED AT ONE
FRAME**, which would redirect the whole condensation front and is worth more
than the field.

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
  changed_files_none = ["agents/tasks/LJ-1-473/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-473/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-473-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-473/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-473/Probe473.agda"]
  changed_files_none = ["agents/tasks/LJ-1-473/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-473/review-of-*.md"]

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
