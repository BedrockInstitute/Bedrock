# LJ-1.487: the Sigma-one transfer, the failing step of cover

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-487/Probe487.agda`:

    CoverWitnessesInHull :
        (y : S) → ⟨ y ∈ˢ M ⟩
      → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

where `M` is the definable hull, exactly as `src/L/BoundedSubset.lagda.md:903-914`
builds it. Land nothing in `src/`.

**`[LJ-1.484]` DECOMPOSED `cover` FOR THE FIRST TIME AND THIS IS ITS ONE FAILING
STEP.** That critic-upheld NO-GO
(`agents/tasks/LJ-1-484/lj-1.484-report.md:114`) reports step 1 GO, step 2 the
wrong shape, **step 3 GO but not paying `cover` because the index lands in `lam`
and not in `M`**, and step 4 unbuilt. It states step 4 at
`agents/tasks/LJ-1-484/Probe484.agda:123-126` and names it Devlin's Σ₁ transfer
of the covering witnesses into the hull.

**AND IT NAMES WHY THE AMBIENT COVERING DOES NOT DO IT: THE HULL IS NOT
TRANSITIVE** (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). An ambient
covering gives `γ` with `y ∈ Lset γ`; it does not give `γ ∈ M`.

**READ `[LJ-1.484]` FIRST AND QUOTE ITS `## THE DECOMPOSITION`.** Take step 4's
type from its probe, never from this brief.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-487/Probe487.agda::CoverWitnessesInHull"]

## SCOPE (write)
- agents/tasks/LJ-1-487/Probe487.agda
- agents/tasks/LJ-1-487/lj-1.487-report.md
- agents/tasks/LJ-1-487/review-of-CoverWitnessesInHull.md
- agents/tasks/LJ-1-487/runs/

## PREMISES

1. `[LJ-1.484]` is a critic-upheld NO-GO whose one failing step is this. Basis: agents/tasks/LJ-1-484/lj-1.484-report.md:114
2. Its statement of step 4 is at the probe that typechecked its neighbours. Basis: agents/tasks/LJ-1-484/Probe484.agda:123
3. Its step 3 is GO and lands the index in `lam`, not in `M`. Basis: agents/tasks/LJ-1-484/Probe484.agda:88
4. The hull is NOT transitive, measured. Basis: agents/tasks/LJ-1-160/lj-1.160-report.md:248
5. The hull is closed under definable existence at the stage. Basis: src/L/Hull.lagda.md:120
6. Its membership is a truncated code by construction. Basis: src/L/Hull.lagda.md:330
7. `[LJ-1.472]` is GO on the numerals being hull members, by `wit` at a formula. Basis: agents/tasks/LJ-1-472/lj-1.472-report.md:151
8. `[LJ-1.474]` is GO on codes for the level formula's constants. Basis: agents/tasks/LJ-1-474/lj-1.474-report.md:70
9. The level formula is delivered with its adequacy. Basis: src/L/Coding/Sequence.lagda.md:349
10. `cover` is spent twice at an arbitrary hull member. Basis: src/L/BoundedSubset.lagda.md:967
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.484]` built steps 1 and 3 and named their suppliers at `file:line`. The
hull's closure under definable existence is delivered, and `[LJ-1.472]` and
`[LJ-1.474]` have both used `wit` successfully to put things in the hull.

## WHAT IS MISSING

The index in `M`. Everything else about `cover` is now built or named.

## THE REASONING

**W8 BINDS AND THE LITERATURE IS DIGESTED.** This is Devlin's Σ₁ transfer
(`dev/literature/devlin-II5.md:107-108`). **Read the injected block and say what
the orthodox argument uses**, at `file:line`. If it needs elementarity this tree
does not have, **STOP: a literature NO-GO is a full return.**

**D-10, BEFORE ANY AGDA.** The obstruction is `γ ∈ M`, not `y ∈ Lset γ`. Two
routes and the report must weigh both before a term:

1. **By `wit`.** The hull is closed under definable existence
   (`src/L/Hull.lagda.md:120-123`), and "the least ordinal `γ` with `y ∈ Lset γ`"
   is definable once the level formula is available. `[LJ-1.472]` and
   `[LJ-1.474]` are the two delivered precedents for getting something into the
   hull this way. **Say whether the level formula lets `wit` name that ordinal.**
2. **By elementarity.** The orthodox route, which needs `M ≺_{Σ₁} L_lam`.
   **Say whether this tree has that, at `file:line`, or has nothing.**

**Name which route you took and why. If neither closes, say which is nearer and
what it lacks.**

**THE SHAPE.** Rebuild the telescope down to the hull, copying
`src/L/BoundedSubset.lagda.md:903-914`. Do W3 first. Do not import a probe.
**Do not take `levelIn` or `cover` as a hypothesis.**

**DO NOT POSTULATE AND DO NOT WEAKEN `γ ∈ M` TO A TRUNCATION OUTSIDE THE
EXISTING ONE.** The conclusion is already truncated once; a second truncation
inside changes the statement.

**REQUIRED REPORT SECTION `## WHAT COVER STILL OWES`.** Restate `[LJ-1.484]`'s
four steps with this one marked BUILT or UNBUILT, and say whether step 2's wrong
shape now matters. **Do not claim `cover`.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.484]`'s probe decomposed the whole statement and built
two steps in about 130 lines; this builds one harder step on the same telescope.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `wit` can name an ordinal at all.

    ord-by-wit : ⟨ some ordinal ∈ˢ M ⟩

**Put ONE ordinal in the hull by `wit` at a formula, with the obligation omitted,
and typecheck it ALONE.** `[LJ-1.472]` did this for numerals, which are ordinals
of a special shape. **If a general ordinal cannot be named the same way, route 1
is closed and the task turns on elementarity alone.** That is the cheapest
possible split between the two routes.

ESTIMATE for W3: about 12 lines and under 20 seconds. **Do not fund it against
`[LJ-1.472]`'s numeral measurement**: a numeral is not a general ordinal and C-42
rules the transfer.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE ONE FAILING STEP OF `cover`**, and with steps 1 and 3 already
built the hypothesis becomes a join.

**A NO-GO NAMES WHICH ROUTE IS NEARER AND WHAT IT LACKS**, and if it names
elementarity as absent, that is the first measurement of what the condensation
front owes beyond definability.

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
  changed_files_none = ["agents/tasks/LJ-1-487/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-487/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-487-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-487/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-487/Probe487.agda"]
  changed_files_none = ["agents/tasks/LJ-1-487/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-487/review-of-*.md"]

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
