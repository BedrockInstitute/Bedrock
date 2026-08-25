# LJ-1.476: is someEnvDef inhabitable at all, or is the field misstated

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-476/Probe476.agda`:

    ar-numeral :
        (ar : S) → ⟨ fst ar ∈ fst K ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

at `[LJ-1.457]`'s frame, where `K` is that frame's bound slot. **This is the one
hypothesis `SupplyEnv.someEnv` needs that `someEnvDef` does not give.** Land
nothing in `src/`.

**`[LJ-1.473]` CLOSED EVERYTHING ELSE AND NAMED THIS.** Its W3 is GO: the carrier
sits in slot 0 by `refl`, and the layout and the supplier share that slot
(`agents/tasks/LJ-1-473/Probe473.agda:69-70`). The obligation is a hole because
**the numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` has no source at
`someEnvDef`** (`agents/tasks/LJ-1-473/lj-1.473-report.md:112`, committed
`398c950`). `someEnvDef` supplies three memberships and nothing else
(`src/L/Condensation/LowerAgree.lagda.md:52-58`).

**THIS IS A D-10 QUESTION AND A NO-GO IS THE LIKELY AND USEFUL RETURN.** Law
D-10 says price the TRUTH of a recorded residue before pricing its proof. **If
this term is false at the frame, then `TFacts.someEnv` as stated cannot be
inhabited from the delivered supplier at all**, and the field's own statement is
what needs changing, not the transport.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-476/Probe476.agda::ar-numeral"]

## SCOPE (write)
- agents/tasks/LJ-1-476/Probe476.agda
- agents/tasks/LJ-1-476/lj-1.476-report.md
- agents/tasks/LJ-1-476/review-of-ar-numeral.md
- agents/tasks/LJ-1-476/runs/

## PREMISES

1. `[LJ-1.473]` is a critic-upheld NO-GO whose only gap is this truncation. Basis: agents/tasks/LJ-1-473/lj-1.473-report.md:112
2. Its W3 is GO and the slot-0 question is settled by `refl`. Basis: agents/tasks/LJ-1-473/Probe473.agda:69
3. `someEnvDef` supplies three memberships and no numeral fact. Basis: src/L/Condensation/LowerAgree.lagda.md:52
4. `SupplyEnv.someEnv` takes the numeral truncation as `arNum`. Basis: src/L/Coding/EnvSupply.lagda.md:417
5. Its `envSetK` spends `arNum` directly. Basis: src/L/Coding/EnvSupply.lagda.md:143
6. The SAME truncation appears as a delivered parameter shape elsewhere in the condensation chapter, which is where a consumer gets it. Basis: src/L/Condensation.lagda.md:279
7. `[LJ-1.457]` is GO on the frame at `n = 9`. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
8. `KValue` builds the bound slot from a limit stage. Basis: src/L/Condensation.lagda.md:7387
9. `[LJ-1.113]` names `someEnv` as the only construction among the 28. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
10. D-10: price the truth of a recorded residue before pricing its proof. Basis: dev/LESSONS.md:1375
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Everything the transport needs except this one fact. `[LJ-1.457]` settled the
layout, `[LJ-1.473]` settled slot 0, and `SupplyEnv.someEnv` carries the
membership `[LJ-1.463]` could not derive. **Four dispatches have converged on one
truncation.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND THE ANSWER MAY BE NO.** `K` at `[LJ-1.457]`'s frame
is a constructible LEVEL (`src/L/Condensation.lagda.md:7387-7390`). **Its members
are not all numerals.** So `ar-numeral` as stated is very likely FALSE, and the
cheap move is to try to REFUTE it before trying to prove it.

**RUN THE REFUTATION FIRST.** Exhibit one member of `K` at a legal frame instance
that is not a numeral, and inhabit
`(∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁) → Empty.⊥` at it. `[LJ-1.467]` did exactly this
shape at `lam = ω`, `gam = ∅` and it is the pattern to follow. **A green
refutation is a full return and it is worth more than the obligation.**

**IF THE REFUTATION LANDS, THE REPORT MUST SAY WHAT FOLLOWS**, in a required
section `## WHAT THE FIELD MUST BECOME`: the numeral truncation belongs in
`someEnvDef`'s own telescope, or `TFacts.someEnv` is only usable where a
consumer supplies it (`src/L/Condensation.lagda.md:279` is such a site). **State
both readings as types and do not choose between them**: that choice is a
mathematical judgement and it comes back to the mathematician.

**DO NOT TRANSPORT `SupplyEnv.someEnv` AND DO NOT BUILD `someEnv-gated`.** One
obligation, and it is this fact or its refutation.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO MAKE IT TRUE.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation or
its refutation is about 20. BASIS: `[LJ-1.467]` reached a green refutation of the
same class at this frame in about the same file size, measured at 2.21 s.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is a single non-numeral member of `K`.

    witness : Σ[ ar ∈ S ] ⟨ fst ar ∈ fst K ⟩

**Exhibit one, at a legal instance of the frame, with the obligation omitted, and
typecheck it ALONE.** If every member of `K` at every legal instance is a
numeral, the obligation may be TRUE and the task turns into a proof. **The
witness decides which task this is, and it costs two lines.**

ESTIMATE for W3: about 8 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO WOULD MEAN THE TRANSPORT CAN RUN**, and `[LJ-1.473]`'s hole closes with
one more dispatch.

**A REFUTATION IS THE MORE LIKELY AND THE MORE USEFUL RETURN.** It would say
`TFacts.someEnv` cannot be inhabited from the delivered supplier as the field is
stated, which redirects `[LJ-1.113]`'s 28 rather than funding a fifth attempt at
one of them.

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
  changed_files_none = ["agents/tasks/LJ-1-476/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-476/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-476-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-476/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-476/Probe476.agda"]
  changed_files_none = ["agents/tasks/LJ-1-476/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-476/review-of-*.md"]

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
