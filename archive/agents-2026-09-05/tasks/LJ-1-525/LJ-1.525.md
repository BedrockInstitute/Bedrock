# LJ-1.525: the leaf conversion, which consumes what 522 paid

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-525/Probe525.agda`:

    leaf-unbounds : ⟨ γ ⊨ leafB ⟩ → ⟨ γ ⊨ (the leaf at extAt, unbounded) ⟩

**by applying the delivered `extAtB→extAt` with its `inK` hypothesis supplied
from `[LJ-1.522]`'s `defPow-closed-noCode`.** Land nothing in `src/`.

**`[LJ-1.522]` IS GO AND IT NAMED THIS TASK.** Its own words: "the transport
that would consume the certificate needs the leaf conversion, the leaf
conversion needs this row, and **this row is now paid at a level carrier**. So
the certificate's consumer is one step nearer, and it is still not written"
(`agents/tasks/LJ-1-522/lj-1.522-report.md:236-240`).

**THE CONVERSION IS DELIVERED AND ITS THIRD HYPOTHESIS IS EXACTLY 522's TERM.**
`extAtB→extAt` (`src/L/Condensation.lagda.md:2514-2521`) takes:

    → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)

and `defPow-closed-noCode` (`agents/tasks/LJ-1-522/Probe522.agda:356-364`)
concludes `⟨ fst z ∈ fst (lookup K γ) ⟩` from `⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩`.
**Match them at `file:line` before you build.**

**`leafB` IS THE SITE.** `src/L/Condensation.lagda.md:2398-2402`, built from
`extAtB` at the `K` slot with two bounded existentials inside.

**TAKE 522's `noCode` FORM, NOT THE BRIEFED ONE.** `[LJ-1.522]` measured that
the code-membership hypothesis my brief wrote **is never consumed**, and
delivered the same type without it (`Probe522.agda:430-435` is the briefed
form, and it only forgets an argument). **Use the weaker-hypothesis term.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-525/Probe525.agda::leaf-unbounds"]

## SCOPE (write)
- agents/tasks/LJ-1-525/Probe525.agda
- agents/tasks/LJ-1-525/lj-1.525-report.md
- agents/tasks/LJ-1-525/review-of-leaf-unbounds.md
- agents/tasks/LJ-1-525/runs/

## PREMISES

1. `[LJ-1.522]` is GO and names the leaf conversion as the next step. Basis: agents/tasks/LJ-1-522/lj-1.522-report.md:236
2. Its `noCode` term drops a hypothesis that is never consumed. Basis: agents/tasks/LJ-1-522/Probe522.agda:356
3. The briefed form only forgets an argument. Basis: agents/tasks/LJ-1-522/Probe522.agda:430
4. `extAtB→extAt` is delivered. Basis: src/L/Condensation.lagda.md:2514
5. Its third hypothesis is a membership in `K`. Basis: src/L/Condensation.lagda.md:2517
6. `extAt-in-both` is what it calls. Basis: src/L/Condensation.lagda.md:2520
7. `leafB` is the bounded leaf. Basis: src/L/Condensation.lagda.md:2398
8. `DefBody` is the delivered code-set description. Basis: src/L/Coding/Powerset.lagda.md:437
9. Two `Σ₁` certificates are delivered and unconsumed. Basis: src/L/BoundedSubset.lagda.md:145
10. `[LJ-1.520]` measured the circularity that a frame hypothesis avoids. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:262
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CONDENSATION LEG'S MACHINERY IS NOW ALMOST ALL BUILT AND ALMOST NONE OF
IT IS CONNECTED.** `[LJ-1.514]` lifted the carrier, `[LJ-1.516]` built the seam
and two graded transports, `[LJ-1.520]` built the graded formula, `[LJ-1.522]`
paid its ninth hypothesis. **Two `Σ₁` certificates have sat unconsumed in
`src/` since `[LJ-1.228]`. This task is the first link of the chain that would
consume them.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `extAtB→extAt` wants `inK` at `φ`, the UNBOUNDED
leaf. `defPow-closed-noCode` concludes from `DefBody w`. **Say at `file:line`
whether the unbounded leaf's `φ` is `DefBody w` or something that reduces to
it.** If it is neither, name the gap and STOP: an adapter written silently
between two delivered terms is how a two-step chain becomes a three-step one
nobody priced.

**SUPPLY `α` AND THE LIMIT HONESTLY.** `defPow-closed-noCode` takes
`(α : V ℓ) → IsLimit α` and `fst (lookup K γ) ≡ Lset α`. **Those ride into
your conclusion as hypotheses.** Do not discharge them and do not hide them:
`[LJ-1.519]` measured that the limit is Part A of Devlin's proof and it is
bought, but it is still a hypothesis here.

**DO NOT CONSUME THE `Σ₁` CERTIFICATES.** That is the next task. This one makes
their consumer reachable and does not reach it.

**DO NOT REBUILD THE GRADED FORMULA, THE SEAM OR `defPow-closed`.**
`[LJ-1.520]`, `[LJ-1.516]` and `[LJ-1.522]` delivered them.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT NOW CONSUMES THE CERTIFICATE`.** After this
term, say what stands between it and `Σ₁-levelHood`
(`src/L/BoundedSubset.lagda.md:145-146`), as types, with `file:line` for each
piece that is delivered. **`[LJ-1.522]` re-measured that nothing in `src/`
consumes either certificate; say whether that is still true after this task.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 35 and the rest is the rebuilt frame. BASIS: `[LJ-1.522]` rebuilt this
frame and its closure in a comparable file. Comparables are of SHAPE and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the match between the two `φ`, because both terms are delivered and the
only question is whether they meet.

    -- extAtB→extAt's `inK` argument, at the leaf's own φ

**Write it FIRST, as a type, and typecheck it ALONE.** If `defPow-closed-noCode`
does not have that shape at this frame, the two delivered terms do not compose
and the task stops at its cheapest point with the difference as a type.

ESTIMATE for W3: about 20 lines and under 35 seconds. **Do not fund it against
`[LJ-1.522]`'s numbers**: that proved a closure and this matches two signatures.

## WHAT GO AND NO-GO EACH EARN

**A GO MAKES THE UNCONSUMED CERTIFICATES REACHABLE FOR THE FIRST TIME SINCE
`[LJ-1.228]`**, and is the first link of the chain that would use them.

**A NO-GO SAYS TWO DELIVERED TERMS DO NOT COMPOSE AT THIS FRAME**, which is a
fact about `src/L/Condensation.lagda.md`'s own transfer and worth more than a
term built across an unrecorded adapter.

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
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-525/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-525/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-525/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-525/Probe525.agda"]
  changed_files_none = ["agents/tasks/LJ-1-525/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-525/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 163.963)
- CANDIDATE archive/dev/JOURNAL.md  (score 151.804)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 147.964)
- CANDIDATE dev/ARCHIVE.md  (score 131.716)
- CANDIDATE archive/dev/DD-archived.md  (score 122.384)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 67.108)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 45.567)
- CANDIDATE dev/literature/digest.md  (score 38.161)
- CANDIDATE dev/literature/geology.md  (score 38.041)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 35.642)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
