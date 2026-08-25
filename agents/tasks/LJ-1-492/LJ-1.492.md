# LJ-1.492: the hull's own closure, which three tasks wanted and none opened

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-492/Probe492.agda`:

    CoverWitnessesInHull :
        (y : S) → ⟨ y ∈ˢ M ⟩
      → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

**from `H.T.closed`**, the hull's own closure operator, and NOT from `wit`. `M`
is the definable hull, exactly as `src/L/BoundedSubset.lagda.md:903-914` builds
it. Land nothing in `src/`.

**`[LJ-1.487]` FAILED AT THIS AND ITS PROBE SHOWS WHY.** It opened
`Code; val; wit; Sat; val-wit; inHull; _⊨₀_` from the hull
(`agents/tasks/LJ-1-487/Probe487.agda:73`) and **did not open `closed`**. It then
used `wit 0 φord []` (`:97`), a closed formula with no parameters, which names
SOME ordinal and not one covering `y`. That is why its W3 was GO and its
obligation was not (`agents/tasks/LJ-1-487/lj-1.487-report.md:170`, committed
`6c6c6e3`).

**`closed` IS THE TARSKI AND VAUGHT CRITERION AND IT IS DELIVERED**
(`src/L/Hull.lagda.md:120-122`):

    closed : (φ : Formula Code 1)
           → ∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
           → ∥ Σ[ a ∈ S𝒮 ] (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ []) ⊨c φ ⟩) ∥₁

**It takes an AMBIENT witness and returns a HULL witness.** That is precisely the
step from `[LJ-1.484]`'s `ambient-level`, which is BUILT
(`agents/tasks/LJ-1-484/Probe484.agda:88-90`), to this obligation.

**READ `[LJ-1.487]` AND `[LJ-1.484]` FIRST.** Take `ambient-level` from 484's
probe at its delivered type.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-492/Probe492.agda::CoverWitnessesInHull"]

## SCOPE (write)
- agents/tasks/LJ-1-492/Probe492.agda
- agents/tasks/LJ-1-492/lj-1.492-report.md
- agents/tasks/LJ-1-492/review-of-CoverWitnessesInHull.md
- agents/tasks/LJ-1-492/runs/

## PREMISES

1. `[LJ-1.487]` is a critic-upheld NO-GO on this obligation. Basis: agents/tasks/LJ-1-487/lj-1.487-report.md:170
2. Its probe opened `wit` and not `closed`. Basis: agents/tasks/LJ-1-487/Probe487.agda:73
3. It used a parameter-free formula, which names some ordinal and not a covering one. Basis: agents/tasks/LJ-1-487/Probe487.agda:97
4. `closed` takes an ambient witness to a hull witness. Basis: src/L/Hull.lagda.md:120
5. `[LJ-1.484]` built `ambient-level`, the ambient witness this needs. Basis: agents/tasks/LJ-1-484/Probe484.agda:88
6. It also built step 1, the code of a hull member. Basis: agents/tasks/LJ-1-484/Probe484.agda:68
7. `[LJ-1.458]` found the level formula delivered. Basis: agents/tasks/LJ-1-458/lj-1.458-report.md:71
8. `[LJ-1.474]` is GO on codes for that formula's constants. Basis: agents/tasks/LJ-1-474/lj-1.474-report.md:70
9. The hull is NOT transitive, so the index does not come for free. Basis: agents/tasks/LJ-1-160/lj-1.160-report.md:248
10. `cover` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:918
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE HULL WAS BUILT WITH THIS EXACT CLOSURE AND THREE TASKS HAVE WANTED IT
WITHOUT NAMING IT.** `[LJ-1.481]` stopped because `IsOrd` has no source at a hull
member. `[LJ-1.489]` stopped because two sides cannot agree without elementarity.
`[LJ-1.487]` stopped one application short of it. **`closed` is the tree's
elementarity, and none of the three opened it.**

## WHAT IS MISSING

The formula to feed it, and the application.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `closed` takes a
`Formula Code 1`: ONE free variable, with its constants as `Code`s. The formula
this needs says of `γ`: **`γ` is an ordinal and `y ∈ Lset γ`**, with `y` as a
parameter. **Say, at `file:line`, where each piece comes from**: the ordinal
predicate (`[LJ-1.487]`'s `φord` is the shape, `Probe487.agda:97`), the level
formula (`src/L/Coding/Sequence.lagda.md:349`), and `y`'s code
(`[LJ-1.484]`'s step 1). **If the conjunction cannot be formed at arity one, name
what blocks it and STOP.**

**THE SHAPE.** Rebuild the telescope down to the hull. Open `closed` from `H.T`.
Build the formula. Feed `[LJ-1.484]`'s `ambient-level` as the hypothesis. Apply.
Do not import a probe.

**DO NOT USE `wit`.** `[LJ-1.487]` measured where that leads. `wit` names a
witness of a satisfiable formula; `closed` names one INSIDE THE HULL, and only
the second is what `γ ∈ M` asks for.

**DO NOT POSTULATE AND DO NOT ADD AN ELEMENTARITY HYPOTHESIS.** If `closed` is
not enough, that is the finding, and it would say the hull's construction does
not give the transfer its own consumer needs.

**REQUIRED REPORT SECTION `## WHAT COVER STILL OWES`.** Restate `[LJ-1.484]`'s
four steps with this one marked, and say whether `cover` is now a join. **Do not
claim `cover`.**

**AND A SECOND REQUIRED SECTION, `## DOES THIS REACH levelIn`.** `[LJ-1.481]` and
`[LJ-1.489]` both stopped for want of elementarity at the same hull. **Say, in
two sentences and as types, whether `closed` bears on either**, and do not
attempt them. That answer decides whether `levelIn` needs a new decomposition or
just this application.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.487]` built this telescope, the ordinal formula and its
W3 in a comparable file and stopped at the application. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the formula at arity one, because `closed` accepts nothing else.

    coverFo : (yc : Code) → Formula Code 1

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** It must
conjoin an ordinal predicate with a level membership, at one free variable, with
`y` entering as a constant `Code`. **`[LJ-1.487]`'s `φord` had no parameters at
all**, so this is a different formula and its arity is the thing to measure. If
it will not form, `closed` cannot be fed and the task stops at its cheapest
point.

ESTIMATE for W3: about 20 lines and under 25 seconds. **Do not fund it against
`[LJ-1.487]`'s W3**: a parameter-free formula is not this one.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE ONE FAILING STEP OF `cover` AND MAY UNBLOCK `levelIn` TOO**,
because both stalled on the same missing transfer.

**A NO-GO SAYS THE HULL'S OWN CLOSURE DOES NOT REACH ITS OWN CONSUMER**, which is
the sharpest possible statement of what the condensation front lacks, and it
would be the first time this campaign could name that gap precisely.

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
  changed_files_none = ["agents/tasks/LJ-1-492/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-492/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-492-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-492/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-492/Probe492.agda"]
  changed_files_none = ["agents/tasks/LJ-1-492/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-492/review-of-*.md"]

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
