# LJ-1.480: finish the refutation its own W3 set up

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-480/Probe480.agda`:

    ar-numeral-refuted :
        (∥ Σ[ n ∈ ℕ ] (fst (prʟ (numeralL 0) (numeralL 0)) ≡ # n) ∥₁) → Empty.⊥

at `[LJ-1.457]`'s frame with `lam = ω`, the instance `[LJ-1.476]` already
exhibits. Land nothing in `src/`.

**`[LJ-1.476]` FOUND THE WITNESS AND LEFT THE REFUTATION A HOLE.** Its W3 is GO:
`witness` typechecks and it is the L-pair of two copies of `numeralL 0`, a member
of the bound slot at `lam = ω` (`agents/tasks/LJ-1-476/Probe476.agda:72-74`,
committed `f74db13`). Its obligation `ar-numeral` is a hole at `:137`. **The
brief asked for a refutation first and got a witness without one.**

**THIS TASK FINISHES IT AND NOTHING ELSE.** A Kuratowski pair of two numerals is
not a numeral; that is what must be written down.

**READ `[LJ-1.476]`'s REPORT FIRST.** If its W3 is not GO, or the witness is
absent from its probe, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-480/Probe480.agda::ar-numeral-refuted"]

## SCOPE (write)
- agents/tasks/LJ-1-480/Probe480.agda
- agents/tasks/LJ-1-480/lj-1.480-report.md
- agents/tasks/LJ-1-480/review-of-ar-numeral-refuted.md
- agents/tasks/LJ-1-480/runs/

## PREMISES

1. `[LJ-1.476]` is a critic-upheld NO-GO whose W3 is GO and whose obligation is a hole. Basis: agents/tasks/LJ-1-476/lj-1.476-report.md:57
2. Its witness is the L-pair of two copies of `numeralL 0`, in the bound slot. Basis: agents/tasks/LJ-1-476/Probe476.agda:72
3. `someEnvDef` supplies three memberships and no numeral fact. Basis: src/L/Condensation/LowerAgree.lagda.md:52
4. `SupplyEnv.someEnv` takes the numeral truncation as `arNum`. Basis: src/L/Coding/EnvSupply.lagda.md:417
5. `[LJ-1.473]`'s only hole was that truncation, and its W3 was GO. Basis: agents/tasks/LJ-1-473/lj-1.473-report.md:112
6. `numeralL-fst` says the numeral's underlying set is `#`. Basis: src/L/Axioms/Numerals.lagda.md:179
7. `KValue` builds the bound slot from a limit stage. Basis: src/L/Condensation.lagda.md:7387
8. `[LJ-1.467]` inhabited a negation of the same class at this frame, and that is the pattern. Basis: agents/tasks/LJ-1-467/lj-1.467-report.md:60
9. D-10: price the truth of a recorded residue before pricing its proof. Basis: dev/LESSONS.md:1375
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The witness, and the frame it lives at. **Five dispatches have now converged on
one truncation** (`[LJ-1.463]`, `[LJ-1.467]`, `[LJ-1.473]`, `[LJ-1.476]`, and
this one), and every question but this has been settled GO along the way: the
layout, slot 0, and the supplier's membership.

## WHAT IS MISSING

The two lines that say a pair is not a numeral.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `# n` is a von Neumann numeral and
`prʟ (numeralL 0) (numeralL 0)` is a Kuratowski pair. **Name the delivered fact
that separates them, at `file:line`.** Candidates: the numeral's own
characterisation (`src/L/Axioms/Numerals.lagda.md:179`), a membership count, or
an extensionality argument on the pair's members. **If no delivered fact
separates them, say so and STOP**: that absence would be the finding, and it
would mean this tree cannot tell a pair from a numeral, which is a much larger
statement than the obligation.

**THE SHAPE.** Rebuild `[LJ-1.476]`'s frame and its witness at their delivered
shapes. Spend the truncation with `PT.rec` into `Empty.⊥`. Do not import a probe.

**DO NOT REBUILD `[LJ-1.476]`'s OBLIGATION AND DO NOT TRY TO PROVE
`ar-numeral`.** It is refuted at this instance or it is not, and this task
settles only that.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE FIELD MUST BECOME`.** With the refutation
in hand, state as types the two readings `[LJ-1.476]`'s brief named and did not
choose between: the numeral truncation belongs in `someEnvDef`'s own telescope,
or `TFacts.someEnv` is usable only where a consumer supplies it
(`src/L/Condensation.lagda.md:279` is such a site). **State both and choose
neither.** That choice is the mathematician's.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 15. BASIS: `[LJ-1.467]` reached a green refutation of the same class at the
same frame in a comparable file, measured at 2.21 s, and `[LJ-1.476]` has already
built the frame and the witness. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the separating fact, not the refutation.

    not-a-numeral : (n : ℕ) → fst (prʟ (numeralL 0) (numeralL 0)) ≡ # n → Empty.⊥

**Write the UNTRUNCATED form first, at a fixed `n` if that is easier, and
typecheck it ALONE with the obligation omitted.** The truncation is one `PT.rec`
once this holds. **If the untruncated form will not close, the truncated one
cannot, and the task stops at its cheapest point.**

ESTIMATE for W3: about 10 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO SETTLES A FIVE-DISPATCH QUESTION.** It says `TFacts.someEnv` cannot be
inhabited from the delivered supplier as the field is stated, and it redirects
`[LJ-1.113]`'s 28 rather than funding a sixth attempt at one of them.

**A NO-GO IS ALSO A RESULT.** It would say this tree cannot separate a
Kuratowski pair from a numeral at that frame, which is a defect in the coding
layer and far more consequential than the field.

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
  changed_files_none = ["agents/tasks/LJ-1-480/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-480/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-480-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-480/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-480/Probe480.agda"]
  changed_files_none = ["agents/tasks/LJ-1-480/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-480/review-of-*.md"]

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
