# LJ-1.530: dK, the one fact rows three and four still want

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-530/Probe530.agda`:

    dK : (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
       → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩

**the definable powerset of `w` is a member of `K`.** Land nothing in `src/`.

**`[LJ-1.527]` IS GO AND IT OVERTURNED A STALE TABLE ROW.** `[LJ-1.525]`'s
chain called rows three to six undelivered and cited `[LJ-1.250]`'s refutation
for row four. **`[LJ-1.527]` found `[LJ-1.304]`'s build, 54 dispatches later,
which overturned it**: rows three, four and five are already BUILT as terms in
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda`, at the ambient carrier. Its warning:
**"A brief for rows three to five that starts from `[LJ-1.525]`'s table alone
will re-buy work that exists."**

**AND IT REDUCED FIVE MEMBERSHIPS TO TWO, THEN TO ONE.** The three that rows
three and four want are `wK`, `dK` and `zK`
(`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176-182`).

- **`wK` IS DELIVERED.** `entryK` (`src/L/Condensation.lagda.md:6615-6616`)
  returns both components of a pair in `K`, so `wK` is its second projection.
  **I checked this at source.**
- **`zK` REDUCES TO `dK`** plus the transitivity of a level, which `src/`
  delivers as `layer-trans (Lset-layer α)`
  (`src/L/Constructible.lagda.md:183`, `:246`).
- **`dK` IS WHAT REMAINS.**

**`[LJ-1.522]` PROVED THE NEAR NEIGHBOUR AND IT IS NOT THIS.** Its
`defPow-closed-noCode` (`agents/tasks/LJ-1-522/Probe522.agda:356-364`) says
every definable SUBSET of a member of `K` is a member of `K`, discharged from
`K` being a limit level. **`dK` wants the definable POWERSET ITSELF, the set of
those subsets, to be a member.** Those are different statements and the
difference is this task's whole risk.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-530/Probe530.agda::dK"]

## SCOPE (write)
- agents/tasks/LJ-1-530/Probe530.agda
- agents/tasks/LJ-1-530/lj-1.530-report.md
- agents/tasks/LJ-1-530/review-of-dK.md
- agents/tasks/LJ-1-530/runs/

## PREMISES

1. `[LJ-1.527]` is GO and found rows three to five already built. Basis: agents/tasks/LJ-1-527/lj-1.527-report.md:1
2. The three memberships are named there as types. Basis: agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176
3. `dK` is the second of the three. Basis: agents/tasks/LJ-1-304/ProbeLJ1304A.agda:178
4. `zK` is the third and it consumes `dK`. Basis: agents/tasks/LJ-1-304/ProbeLJ1304A.agda:180
5. `entryK` delivers `wK`. Basis: src/L/Condensation.lagda.md:6615
6. Level transitivity is delivered. Basis: src/L/Constructible.lagda.md:183
7. `[LJ-1.522]` proved the subset closure at a limit. Basis: agents/tasks/LJ-1-522/Probe522.agda:356
8. `[LJ-1.525]` built row one of the chain. Basis: agents/tasks/LJ-1-525/lj-1.525-report.md:180
9. `[LJ-1.527]` built row two. Basis: agents/tasks/LJ-1-527/lj-1.527-report.md:1
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CONDENSATION CHAIN HAD SIX ROWS THIS MORNING AND NOW HAS ONE FACT.**
`[LJ-1.525]` paid row one, `[LJ-1.527]` paid row two and found rows three to
five already built elsewhere, `wK` is delivered and `zK` reduces. **`dK` is
what is left.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE DIFFERENCE.** `[LJ-1.522]` closed `K`
under definable subsets. `dK` wants the powerset object itself in `K`. **Say at
`file:line` what `𝒟ₒ` is and whether a level holds it.** If `K` is `Lset α` at
a limit, ask whether `𝒟ₒ w` appears at some level below `α` when `w` does;
`src/L/Constructible.lagda.md` is where that would be said. **If nothing says
it, say so and STOP**: that would mean `dK` needs a new fact about the
hierarchy, not a re-use of `[LJ-1.522]`.

**READ `[LJ-1.304]`'s PROBE BEFORE YOU BUILD.** `[LJ-1.527]` warns that a brief
starting from `[LJ-1.525]`'s table alone re-buys work that exists. **Check
whether `[LJ-1.304]` already discharges `dK` at the ambient carrier**, and if it
does, say what stands between that and this obligation.

**DO NOT REBUILD ROWS THREE TO FIVE.** `[LJ-1.527]` found them built. Cite
them; do not re-derive them.

**DO NOT WEAKEN `dK` TO THE SUBSET FORM.** That form is delivered and it is not
what rows three and four consume.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE CHAIN OWES AFTER THIS`.** Re-walk
`[LJ-1.525]`'s six rows with `[LJ-1.527]`'s correction and this task's result,
and say which rows are now delivered, at `file:line`. **Include row six, which
no dispatch has yet examined.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.522]` proved the neighbouring closure in a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether a level holds its own definable powerset, because that is the one
step between `[LJ-1.522]`'s result and this one.

    dpow-in-level : (α : V ℓ) → IsLimit α → (w : V ℓ) → ⟨ w ∈ Lset α ⟩
                  → ⟨ 𝒟ₒ w ∈ Lset α ⟩

**Write it FIRST, and typecheck it ALONE.** If a limit level does not hold the
definable powerset of its members, `dK` is out of reach at this frame and the
task stops at its cheapest point with the chain's last fact named as unpayable.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.522]`'s numbers**: that closed under subsets and this asks for an
object.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES ROWS THREE AND FOUR AND LEAVES ROW SIX AS THE ONLY UNEXAMINED
ROW**, which would put the condensation leg within sight of spending the two
`Σ₁` certificates that have been unconsumed since `[LJ-1.228]`.

**A NO-GO SAYS THE CHAIN'S LAST FACT NEEDS A NEW THEOREM ABOUT THE
HIERARCHY**, which is a named, checkable statement and not a wall.

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
  changed_files_none = ["agents/tasks/LJ-1-530/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-530/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-530/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-530/Probe530.agda"]
  changed_files_none = ["agents/tasks/LJ-1-530/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-530/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 213.338)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 188.524)
- CANDIDATE archive/dev/JOURNAL.md  (score 185.589)
- CANDIDATE archive/dev/DD-archived.md  (score 148.649)
- CANDIDATE dev/ARCHIVE.md  (score 145.378)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 63.187)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.956)
- CANDIDATE dev/literature/digest.md  (score 48.372)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.780)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 34.754)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
