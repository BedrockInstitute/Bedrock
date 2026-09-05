# LJ-1.411: a code as DATA, and no placement anywhere

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-411/Probe411.agda`.

    code-as-data :
        (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁ → Σ[ F ∈ S ] InjCode F a b

`S` is `L.Cardinal`'s `S`, the L-carrier (`src/L/Cardinal.lagda.md:41`).

**THIS TERM TAKES NO PLACEMENT HYPOTHESIS. IT NAMES NO `SiteBound.β`. IT TAKES
NO ORDINAL AT ALL.** The stage at which the code lives is SELECTED, not
supplied. That is the whole point of the task.

**TAKE `[LJ-1.401]`'s `isPropInjCode` AS A MODULE HYPOTHESIS**, at that task's
own type, `(F a b : S) → isProp (InjCode F a b)`
(`agents/tasks/LJ-1-401/Probe401.agda:48`). Do not import `Probe401` and do not
rebuild it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-411/Probe411.agda::code-as-data"]

## SCOPE (write)
- agents/tasks/LJ-1-411/Probe411.agda
- agents/tasks/LJ-1-411/lj-1.411-report.md
- agents/tasks/LJ-1-411/review-of-code-as-data.md

## PREMISES
- `leastOrd` returns the LEAST ordinal with a given hProp property, as DATA, from a truncated witness, and it quantifies over ALL ordinals. Basis: src/L/Stage.lagda.md:149
- `LeastOrd` carries the property's own payload as a field, so the payload comes back with the ordinal. Basis: src/L/Stage.lagda.md:91
- The descent that proves it is `∈-induction` plus `lem`, and it is delivered and sealed. Basis: src/L/Stage.lagda.md:132
- `stage` gives EVERY L-element an ordinal, as data. Basis: src/L/Stage.lagda.md:180
- `stage-mem` is the membership of that element at that stage. Basis: src/L/Stage.lagda.md:188
- `stage-ord` is the ordinal certificate of that stage. Basis: src/L/Stage.lagda.md:185
- `orderAt` is a strict well-order at EVERY ordinal, not only at `SiteBound.β`. Basis: src/L/Choice/Step.lagda.md:730
- `leastOf` returns DATA from a truncated non-emptiness whenever the predicate is an hProp. Basis: src/L/WellOrder/Base.lagda.md:158
- The crossing from a member of `Lset β` to an L-element reads `β` and `oβ` and nothing else, so it is generic in the ordinal. Basis: src/L/Cardinal.lagda.md:171
- `InjCode` is the four-conjunct code, and it names no stage. Basis: src/L/Cardinal.lagda.md:223
- `[LJ-1.401]` measured that `InjCode` is a proposition. Basis: agents/tasks/LJ-1-401/Probe401.agda:48
- `[LJ-1.403]` states the placement of `F` as gap 2, and asks a caller for it. Basis: agents/tasks/LJ-1-403/lj-1.403-report.md:154
- `[LJ-1.410]` repeats the same gap 2 after retiring gap 3. Basis: agents/tasks/LJ-1-410/lj-1.410-report.md:164
- `[LJ-1.409]` measured that NO finite successor count of `SiteBound.β` places a code. Basis: agents/tasks/LJ-1-409/lj-1.409-report.md:26
- `[LJ-1.397]`'s `code-lands` reduced to one placement obligation and nothing delivered pays it. Basis: agents/tasks/LJ-1-397/lj-1.397-report.md:26
- `L.Stage` reads `S` from the AMBIENT structure and `L.Cardinal` reads `S` from the L structure, so the two names differ in a file that imports both. Basis: src/L/Stage.lagda.md:60

## WHAT IS DELIVERED ALREADY

**THE CLASS-LEVEL SELECTOR.** `leastOrd` (`src/L/Stage.lagda.md:149`) takes a
truncated「some ordinal has this hProp property」and returns the least such
ordinal AS DATA, together with the property's payload
(`src/L/Stage.lagda.md:91-92`). It is not bounded by any stage. It is the
device `stage` itself is built from (`src/L/Stage.lagda.md:176-180`), and
`L.Reflect` already consumes it to pick a witness for an existential
(`src/L/Reflect.lagda.md:175-176`).

**THE STAGE OF ANY CODE.** `stage`, `stage-ord` and `stage-mem`
(`src/L/Stage.lagda.md:180-188`) put every L-element inside `Lset` of an
ordinal, as data.

**THE SET-LEVEL SELECTOR AT ANY ORDINAL.** `orderAt γ oγ`
(`src/L/Choice/Step.lagda.md:730`) is a strict well-order on `Mem (Lset γ)` for
EVERY ordinal γ. Every delivered use runs it at `SiteBound.β`
(`src/L/Cardinal.lagda.md:195` and `:247`), and nothing in its type asks for
that ordinal.

**THE PREDICATE IS ALREADY A PROPOSITION.** `[LJ-1.401]` built `isPropInjCode`
green (`agents/tasks/LJ-1-401/Probe401.agda:48-53`).

## WHAT IS MISSING

**NOBODY HAS RUN THE TWO SELECTORS IN SERIES.** Four tasks have asked for a
code at ONE FIXED STAGE and none has asked WHICH stage.
`[LJ-1.397]`, `[LJ-1.403]`, `[LJ-1.409]` and `[LJ-1.410]` all state the same
obligation: put an arbitrary code inside `Lset (SiteBound.β a)`. `[LJ-1.409]`
measured that no finite successor count of that ordinal does it
(`agents/tasks/LJ-1-409/lj-1.409-report.md:26-33`). **That is a true
measurement of a false target.** A code does not have to live at `SiteBound.β`.
It has to live SOMEWHERE, and `leastOrd` finds the least somewhere.

## THE REASONING

**FOUR STEPS. EACH ONE IS A DELIVERED DEVICE.**

1. **The property.** Write `CodeAt` as a property of an ordinal, and write it
   so that it needs NO ordinal certificate to state:

       CodeAt : Sᵥ → Ω
       CodeAt σ = ∥ Σ[ F ∈ S ] (⟨ fst F ∈ˢ Lset σ ⟩ × InjCode F a b) ∥₁

   It is an hProp because it is a truncation. Do NOT use the crossing `up`
   inside it: a crossing needs `IsOrd σ`, and `leastOrd`'s predicate takes the
   bare ordinal.

2. **The stage exists.** This is W3. See below.

3. **The least stage, as data.** `leastOrd CodeAt` applied to step 2 gives
   `σ₀`, `IsOrd σ₀` and `⟨ CodeAt σ₀ ⟩` (`src/L/Stage.lagda.md:91-92`).
   Minimality is free and this task does not spend it.

4. **The code, as data.** Cross into `Mem (Lset σ₀)` and run
   `leastOf (orderAt σ₀ oσ₀) lem Good`, with

       Good m = InjCode (upAt σ₀ oσ₀ m) a b , isPropInjCode (upAt σ₀ oσ₀ m) a b

   and `upAt σ oσ (x , mem) = x , Lset→isL σ oσ x mem`, which is
   `SiteBound.up` written generic in the ordinal
   (`src/L/Cardinal.lagda.md:171-172`). `[LJ-1.401]`'s `sel-code` is this same
   `leastOf` at the fixed stage (`agents/tasks/LJ-1-401/Probe401.agda:66-71`).
   Return the crossed code and its `InjCode`.

**THE ONE BOOKKEEPING COST, AND IT IS NAMED SO YOU DO NOT DISCOVER IT.**
`L.Stage` opens `S` from the ambient structure (`src/L/Stage.lagda.md:60`) and
`L.Cardinal` opens `S` from the L structure (`src/L/Cardinal.lagda.md:41`). A
file that imports both holds two carriers. Rename one at import. Say in your
report which you renamed and what it cost in lines.

**W2 (DD4).** `code-as-data` is generic in `a` and `b`. Name no cardinal, no
site, no numeral and no stage. The whole value of the term is that it names no
stage.

**W3, THE WIDEST UNMEASURED TERM.** It is STEP 2, and nothing in the tree has
taken it: turning a truncated CODE into a truncated ORDINAL statement.

    code-has-stage :
        (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
      → ∥ Σ[ σ ∈ Sᵥ ] (IsOrd σ × ⟨ CodeAt σ ⟩) ∥₁

**State it ALONE, run it, and report its code lines before you write step 4.**
It is one `PT.rec` into a truncation, with `σ := stage (fst F) (snd F)`,
`stage-ord` for the certificate and `stage-mem` for the membership. ESTIMATE:
about 12 code lines. BASIS: `[LJ-1.410]`'s W3 probe `nofin-at-selected` was
measured at 13 non-blank code lines with two rebuilt helpers
(`agents/tasks/LJ-1-410/lj-1.410-report.md:41`). ESTIMATE for the whole
obligation: about 45 code lines. BASIS: `[LJ-1.401]`'s `sel-code`, the same
`leastOf` at a fixed stage, is 15 lines
(`agents/tasks/LJ-1-401/Probe401.agda:57-71`), plus step 2, plus the crossing
and the two carriers. **These are comparables of SHAPE, not of size, and
nothing may be funded against them.**

**D-10 APPLIES AND THE BRIEF ANSWERS IT.** The target is true if `leastOrd`
does what its type says. It carries no cardinality claim: the code exists by
hypothesis, and both selections are searches, not constructions. **If a step
fails, it fails on a level or on the two carriers, not on the mathematics.
Report which.**

## WHAT GO AND NO-GO EACH EARN

**A GO RETIRES THE PLACEMENT BILL OF THE WHOLE CODED ROUTE.** It retires
`[LJ-1.403]`'s gap 2, `[LJ-1.410]`'s gap 2, `[LJ-1.397]`'s `Placement` and
`[LJ-1.409]`'s residue, and it does it without touching `src/`. `[LJ-1.412]` is
written from it.

**A NO-GO EARNS THE LEVEL OR THE CARRIER THAT BLOCKS IT, AT `file:line`.** If
`CodeAt` cannot be stated at `Ω`, or if `leastOrd`'s predicate cannot hold a
Sigma over the L-carrier, say which and give the level arithmetic. **A stated
NO-GO is a full return**, and it tells `[LJ-1.412]` to keep a placement
hypothesis.

**RUN THE C-42 SWEEP EITHER WAY.** Count the sites in `src/` and in
`agents/tasks/` that select a code at a FIXED stage. Report the COUNT before
any opinion about how many of them this term retires.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-411/Probe411.agda"]
  changed_files_none = ["agents/tasks/LJ-1-411/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-411/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

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

## LAWS (program-generated, do not edit)

MANDATORY for kind `probe` (measures one thing and keeps the file as the report's other half. Gating, heap discipline, the transplant law, which is what a probe most often gets wrong, and the extent law, because a probe that refutes has measured ONE site.):

- **D-1. The probe doctrine**
  **Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest decisive probe with its abort criterion fixed in advance; a red verdict costs the attempt and nothing else.
  Full entry: dev/LESSONS.md:1064
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-i. The conversion-explosion playbook (imported from the source project)**
  **Rule:** When cubical Agda hangs or exhausts memory on this codebase family, the cause is one of three heavy-thing classes forced into normalization, and the cure is selected by the decision tree below, not by trial. Imported whole from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md` §5, twenty measured cases); read that section before any surgery on a hang.
  Full entry: dev/LESSONS.md:229
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/Choice
- CANDIDATE archive/dev/JOURNAL-archived.md
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE dev/ARCHIVE.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/terms-2026-08.md
- CANDIDATE dev/literature/BIBLIOGRAPHY.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
