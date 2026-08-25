# LJ-1.457: the frame re-layout the condensation stack needs

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-457/Probe457.agda`:

    tfacts-prefix :
        (lam : V ℓ) (ordλ : IsOrd lam)
        (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
        (∅∈λ : ⟨ ∅ ∈ lam ⟩)
        (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
      → TFactsPrefix Kenv'

the twelve `tagEq` and twelve `numK` fields of `TFacts`, stated as a Sigma at a
RE-LAID-OUT environment `Kenv'`, and inhabited from `KValue.facts`. Land nothing
in `src/`.

**THE RE-LAYOUT IS THE OBLIGATION AND THE BRIEF NAMES ITS ARITHMETIC.** `TFacts`
reads its frame at `lookup (suc (suc (suc (suc (suc (suc X)))))) γ'` over
`γ' : S ^ (11 + n)` with `X : Fin (5 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:129-133`). `KValue` builds
`Kenv : S ^ 14` addressed at bare `Fin 14` indices
(`src/L/Condensation.lagda.md:7387-7409`). **At `n = 3` those give `Fin 8` over
`S ^ 14` against `Fin 14` over `S ^ 14`, and that is the `14 != 8` an earlier
run met.** Take `n = 9`: `X : Fin 14` over `γ' : S ^ 20`, read at `6 + X`, so
`KValue`'s fourteen slots sit at positions 6 to 19 and the first six are filler.
**Check that arithmetic before you write a term, and report it. If it is wrong,
the corrected arithmetic IS the deliverable.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-457/Probe457.agda::tfacts-prefix"]

## SCOPE (write)
- agents/tasks/LJ-1-457/Probe457.agda
- agents/tasks/LJ-1-457/lj-1.457-report.md
- agents/tasks/LJ-1-457/review-of-tfacts-prefix.md
- agents/tasks/LJ-1-457/runs/

## PREMISES

1. `TFacts` has 55 fields and its frame is read at a six-fold successor offset. Basis: src/L/Condensation/TwelveAgree.lagda.md:133
2. It has NO inhabitant in this tree. Basis: src/L/Condensation/TwelveAgree.lagda.md:342
3. `KValue` inhabits the smaller `KFacts` at a REAL bound, every field a term and no hole. Basis: src/L/Condensation.lagda.md:7410
4. Its environment is fourteen slots addressed at bare indices. Basis: src/L/Condensation.lagda.md:7396
5. The twelve `numK` fields come from the bound's own closure, one line each. Basis: src/L/Condensation.lagda.md:7415
6. The twelve `tagEq` fields are `refl` at that layout. Basis: src/L/Condensation.lagda.md:7413
7. The twelve-row agreement says in the tree what it still needs: the frame instantiated at a real `K`. Basis: src/L/Condensation/TwelveAgree.lagda.md:524
8. Its consumer is live and its two parameters are unsupplied. Basis: src/L/Condensation.lagda.md:6971
9. `[LJ-1.113]` classified the gap at 28 facts and priced it at about 250 lines. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:135
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE AGREEMENT STACK IS COMPLETE AS AN ABSTRACT FRAME AND NO FILE IMPORTS IT.**
`src/L/Condensation/TwelveAgree.lagda.md` is 538 lines and delivers `twelve-out`
(`:527`) and `twelve-back` (`:533`), the two parameters `SatGraphAgree` leaves
unsupplied (`src/L/Condensation.lagda.md:6971`). Its own comment says what is
missing (`:520-526`).

**AND THE REAL `K` IS BUILT.** `KValue` (`src/L/Condensation.lagda.md:7380-7434`)
inhabits `KFacts` with terms, from a limit bound and a stage below it.

## WHAT IS MISSING

An inhabitant of `TFacts`. This task builds the 24 fields `KFacts` already has,
at a layout the two conventions share. **It does not build the other 31.**

## THE REASONING

**WHY THE PREFIX AND NOT A FIELD OF THE 28.** The 24 `tagEq` and `numK` fields
are the ones `KFacts` ALREADY supplies. If they do not transfer, the break is the
LAYOUT and not the mathematics, and every plan for the condensation lemma rests
on that transfer. An earlier run met `[UnequalTerms] 14 != 8` at exactly this
point. **This task fixes the arithmetic or proves it cannot be fixed.**

**D-10, BEFORE ANY AGDA.** Write the two index conventions side by side and give
the `n` that reconciles them, with the arithmetic. If no `n` does, say so and
STOP: that is a defect between two live chapters and it outranks the obligation.

**THE SHAPE.** Import `L.Condensation` and `L.Condensation.TwelveAgree` from
`src/`. Build `Kenv'` by padding `KValue`'s fourteen slots. State
`TFactsPrefix` as a Sigma of the 24 field types, copied from
`TwelveAgree.lagda.md:133-156`. Inhabit it from `KValue.facts`. Do not import a
probe. Do not build a `TFacts` record and do not touch the other 31 fields.

**DO NOT POSTULATE AND DO NOT WEAKEN A FIELD.**

**REQUIRED REPORT SECTION `## WHAT THE 31 NOW COST`.** You will have measured the
transfer. Say whether `[LJ-1.113]`'s 250-line figure still stands for the rest,
and do NOT re-price the 25 closure lemmas from this one transfer: they are a
different shape and C-42 forbids it (`dev/LESSONS.md:3752`).

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 50. BASIS: `KValue` is 55 lines including its fourteen index names, and the
24 field types are copied. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is one field, not twenty-four.

    one-tag : fst (lookup (suc (suc (suc (suc (suc (suc i0')))))) Kenv')
            ≡ fst (numeralL 0)

**Write ONE `tagEq` field at the re-laid-out environment, typecheck it ALONE with
the obligation omitted, and report the result.** If one does not transfer,
twenty-four will not, and the arithmetic is wrong. **This is a two-line
measurement and it must run before anything else.**

ESTIMATE for W3: two lines and under 10 seconds. BASIS: the field is `refl` at
`KValue`'s own layout (`src/L/Condensation.lagda.md:7413`).

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS THE CONDENSATION FRONT FOR THE FIRST TIME.** It puts the first
`TFacts` content in the tree at a real `K` and turns `[LJ-1.113]`'s classified
28 into work a brief can order.

**A NO-GO IS WORTH MORE.** It says two live chapters were built to two
conventions that cannot be reconciled, and that has stood since `[LJ-1.113]`.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-457/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-457-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-457/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-457/Probe457.agda"]
  changed_files_none = ["agents/tasks/LJ-1-457/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-457/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 171.561)
- CANDIDATE archive/dev/JOURNAL.md  (score 151.204)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 138.871)
- CANDIDATE dev/ARCHIVE.md  (score 137.680)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 113.644)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 35.354)
- CANDIDATE dev/literature/devlin-II5.md  (score 35.279)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 31.921)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.272)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 25.050)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
