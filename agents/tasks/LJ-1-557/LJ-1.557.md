# LJ-1.557: an internal code for one member of the successor

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-557/Probe557.agda`:

    member-code-into-kappa :
      (δ κ : S) → SuccCardL δ κ → (a : S) → ⟨ fst a ∈ fst δ ⟩
      → ∥ Σ[ F ∈ S ] InjCode F a κ ∥₁

an INTERNAL injection code from one member of δ into κ. Land nothing in `src/`.

**`[LJ-1.552]` IS A NO-GO, UPHELD, AND THIS IS STEP 1 OF THE ONLY PRICED ROUTE
IT FOUND.** Its `## WHAT WOULD REOPEN THIS` names `Codes δ κ`
(`agents/tasks/LJ-1-552/Probe552.agda:295-300`) and decomposes it into two
steps, of which the first is **"an INTERNAL injection code `a ↪ κ` for each
member `a` of δ"**, with its own half giving the ambient one.

**IT ALSO NAMED THE MACHINERY, AND IT DID NOT CLAIM THE MACHINERY WORKS.** Its
own words: **"I DID NOT BUILD THIS AND I DO NOT CLAIM IT WORKS."** The three
terms it names are `InternalLeastCard` (`src/L/Cardinal.lagda.md:235`) for the
shape, `L.InjChain.InclGraph` (`src/L/InjChain.lagda.md:575`) for
non-emptiness, and `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314`) to compose
down to κ. **All three are modules and all three resolve today.**

**AND IT NAMED THE TWO THINGS TO CHECK FIRST**: that the carved code lands in
the stage `InternalLeastCard` selects over, and that the leastness of δ refutes
the bad branch INTERNALLY the way `member-into-kappa` refutes it ambiently.
**Those two checks are your D-10.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-557/Probe557.agda::member-code-into-kappa"]

## SCOPE (write)
- agents/tasks/LJ-1-557/Probe557.agda
- agents/tasks/LJ-1-557/lj-1.557-report.md
- agents/tasks/LJ-1-557/review-of-member-code.md
- agents/tasks/LJ-1-557/runs/

## PREMISES

1. `[LJ-1.552]` is a NO-GO and names `Codes δ κ` as the reopener. Basis: agents/tasks/LJ-1-552/Probe552.agda:295
2. Its first decomposition step is an internal code per member. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:171
3. It disclaims having built or checked it. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:171
4. `InternalLeastCard` is a module over an ordinal κ. Basis: src/L/Cardinal.lagda.md:235
5. `InjChain.InclGraph` is a module. Basis: src/L/InjChain.lagda.md:575
6. `InjChain.Comp` is a module. Basis: src/L/InjChain.lagda.md:314
7. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
8. `SuccCardL`'s fourth component is a leastness clause. Basis: src/L/GCH.lagda.md:47
9. `[LJ-1.526]` overturned the archive on `IsCardinal` inhabitation. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
10. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three modules that a predecessor judged to be the right shape, and no term that
uses them for this. **The judgement is unverified and it is yours to test.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TWO CHECKS `[LJ-1.552]` NAMED.** Answer
both at `file:line` before you build:

1. **Does the carved code land in the stage `InternalLeastCard` selects over?**
2. **Does the leastness of δ refute the bad branch INTERNALLY**, the way
   `member-into-kappa` refutes it ambiently?

**If either is NO, that is the result and you stop there.** `[LJ-1.552]` cost
one task by naming these; do not spend five finding out.

**THE OBLIGATION IS FOR ONE MEMBER, NOT FOR ALL OF THEM AT ONCE.** The
quantifier over `a` is inside the Π and outside the truncation, so **you are not
asked for a uniform choice.** That is deliberate: the uniform version is the
assignment, `[LJ-1.552]` refuted the split, and this brief takes the pointwise
half only.

**DO NOT BUILD THE SQUARE LAW.** `[LJ-1.556]` has step 2. AD12 gives this brief
one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE TWO CHECKS`.** Both answers at `file:line`,
before any account of what you built.

**REQUIRED REPORT SECTION `## POINTWISE AGAINST UNIFORM`.** Three sentences.
`[LJ-1.552]` proved the assignment and its `Link` are NOT independent, because
a set enters L only through a generator and both generators take a `Formula`.
**Say whether your pointwise code makes the uniform assignment closer, or
whether the gap between pointwise and uniform is exactly the `Formula` that
`[LJ-1.554]` could not build.** Do not build either.

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.528]` built a comparable internal cardinal fact. Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `InternalLeastCard`'s stage.

    -- the stage InternalLeastCard selects over, at this frame, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** It is check 1 of the two, and if the
stage will not resolve here the rest of the estimate is void. ESTIMATE: about 15
lines, under 90 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE OTHER HALF OF `[LJ-1.552]`'S ROUTE**, and with `[LJ-1.556]` the
two steps would meet at `Codes δ κ`.

**A NO-GO ON EITHER CHECK CLOSES THE ROUTE CHEAPLY**, which is what a named
decomposition is for.

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
  changed_files_none = ["agents/tasks/LJ-1-557/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-557/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-557/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-557/Probe557.agda"]
  changed_files_none = ["agents/tasks/LJ-1-557/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-557/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park_and_split"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 176.317)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 152.977)
- CANDIDATE archive/dev/JOURNAL.md  (score 148.709)
- CANDIDATE dev/ARCHIVE.md  (score 132.553)
- CANDIDATE archive/dev/DD-archived.md  (score 116.093)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 52.003)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 45.644)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.536)
- CANDIDATE dev/literature/digest.md  (score 37.316)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 31.923)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
