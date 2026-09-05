# LJ-1.544: B8, the last join row that wants no code

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-544/Probe544.agda`:

    LimitAbove :
        (α x : SV.S) → IsOrd α → ⟨ isL x ⟩
      → ∥ Σ[ lam ∈ SV.S ]
           ( IsOrd lam
           × ⟨ α ∈ˢ lam ⟩
           × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
           × ⟨ x ∈ˢ Lset lam ⟩ ) ∥₁

Land nothing in `src/`.

**THIS IS THE LAST UNGATED ROW OF THE JOIN, AND THE ARITHMETIC SAYS SO.**
`[LJ-1.523]` listed ten inputs. `[LJ-1.528]` paid B4, `[LJ-1.540]` paid B7,
`[LJ-1.543]` paid B6 for 9 lines. **Four remain: B5, B8, B9 and B10.** Of those,
B9 and B10 name `InjL` or want a formula, and BOTH routes to a generic code are
closed by measurement (`[LJ-1.533]`, `[LJ-1.535]`). B5 wants ambient out of
internal, the direction that does not pay. **B8 is the only one left that a
build can reach today.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-544/Probe544.agda::LimitAbove"]

## SCOPE (write)
- agents/tasks/LJ-1-544/Probe544.agda
- agents/tasks/LJ-1-544/lj-1.544-report.md
- agents/tasks/LJ-1-544/review-of-LimitAbove.md
- agents/tasks/LJ-1-544/runs/

## PREMISES

1. B8's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:244
2. `[LJ-1.540]` counted zero code tokens in it, so it is ambient. Basis: agents/tasks/LJ-1-540/lj-1.540-report.md:1
3. `[LJ-1.543]` is GO and paid B6 in 9 lines. Basis: agents/tasks/LJ-1-543/Probe543.agda:169
4. `[LJ-1.543]` named `Ladder` as the closest machinery and did NOT typecheck the fit. Basis: agents/tasks/LJ-1-543/lj-1.543-report.md:1
5. `Ladder` takes an ω-chain of ordinals that climbs. Basis: src/L/Reflect.lagda.md:256
6. Its `top` is a set union. Basis: src/L/Reflect.lagda.md:268
7. Its `top-ord` gives that union ordinality. Basis: src/L/Reflect.lagda.md:271
8. Its `G∈top` puts every rung inside the union. Basis: src/L/Reflect.lagda.md:274
9. `[LJ-1.533]` closed the generic coded route. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
10. `[LJ-1.535]` closed the counting-site route. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

**THE JOIN HAD SEVEN UNPAID INPUTS THIS MORNING AND HAS FOUR.** Three were paid
today: B4, B7, B6.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE CHAIN.** `Ladder` wants `G : ℕ → V ℓ`
with `G-ord` and `G-up` (`src/L/Reflect.lagda.md:256-257`). **Say at `file:line`
what chain you feed it**, and say it before you build. The four conjuncts fall
into two groups and you should say which group each is in:

- `IsOrd lam` and `⟨ α ∈ˢ lam ⟩` look like `top-ord` and `G∈top` with a rung
  chosen above `α`. **I have NOT typechecked that and I do not report it as
  measured.**
- The successor-closure conjunct and `⟨ x ∈ˢ Lset lam ⟩` are NOT in `Ladder`
  (`[LJ-1.543]` says so at its own report). They are yours to find or to refute.

**W3 IS THE STAGE, AND IT DECIDES THE FOURTH CONJUNCT.** `⟨ isL x ⟩` is the only
thing the type gives you about `x`. If it yields an ordinal β with
`⟨ x ∈ˢ Lset β ⟩`, the chain can be started above both `α` and β and the fourth
conjunct is a cumulativity step. **If it does not yield such a β, say so and
stop**: the row is then not reachable this way and that is worth more than a
partial build.

**THE CONCLUSION IS PROPOSITIONALLY TRUNCATED** (`∥ … ∥₁`, `:249`). You may use
that. It does not have to be a choice-free explicit ordinal if a truncated
existence is available more cheaply, but **say which you delivered.**

**DO NOT BUILD B5, B9 OR B10.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FOUR CONJUNCTS, ONE LINE EACH`.** For each of
the four, name the term that paid it at `file:line`, or say it is unpaid.

**REQUIRED REPORT SECTION `## WHAT THE JOIN NOW STANDS AT`.** After this task,
say how many of `[LJ-1.523]`'s ten inputs are paid and name the unpaid ones.
**Count, do not estimate.**

ESTIMATE: about 120 lines in the probe, of which the obligation is about 30.
BASIS: `[LJ-1.543]` built the sibling ambient row at 70 lines for an obligation
of 9, and this row has four conjuncts against that row's one. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the stage of `x`, because the fourth conjunct has no other source.

    -- from ⟨ isL x ⟩, an ordinal β with ⟨ x ∈ˢ Lset β ⟩, or the reason there is none

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 10 lines, under 30
seconds. Do not fund it against `[LJ-1.543]`'s numbers: that read a membership
and this opens a truncation.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE JOIN TO THREE UNPAID INPUTS, and every one that remains then
wants a code or the direction that does not pay.** That is the state the
mathematician needs in order to rule on whether the bridge waits for a formula.

**A NO-GO THAT NAMES THE FAILING CONJUNCT IS WORTH NEARLY AS MUCH.** It says the
ambient rows are exhausted, which is the same ruling reached the other way.

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
  changed_files_none = ["agents/tasks/LJ-1-544/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-544/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-544/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-544/Probe544.agda"]
  changed_files_none = ["agents/tasks/LJ-1-544/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-544/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 146.664)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 119.711)
- CANDIDATE dev/ARCHIVE.md  (score 117.213)
- CANDIDATE archive/dev/JOURNAL.md  (score 110.869)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 105.921)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 36.521)
- CANDIDATE dev/literature/devlin-II5.md  (score 34.392)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 31.530)
- CANDIDATE dev/literature/terms-2026-08.md  (score 26.849)
- CANDIDATE dev/literature/geology.md  (score 20.556)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
