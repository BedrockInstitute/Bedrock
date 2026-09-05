# LJ-1.412: the coded descent, from the case hypothesis the recursion holds

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-412/Probe412.agda`.

    coded-descent :
        (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
      → (IsCardinalL κ → Empty.⊥)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ˢ fst κ ⟩
                   × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

**THIS IS `[LJ-1.410]`'s `sel-descent-nofin` WITH `Ne°` REPLACED BY THE ONE
HYPOTHESIS THE BAND RECURSION ACTUALLY HOLDS**, the negation of `IsCardinalL`
(`agents/tasks/LJ-1-410/lj-1.410-report.md:145`). There is NO `Ne°`, NO
`Good°`, NO `SiteBound.β` and NO placement.

**TAKE `[LJ-1.411]`'s `code-as-data` AS A MODULE HYPOTHESIS**, at that task's
own type:

    code-as-data : (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
                 → Σ[ F ∈ S ] InjCode F a b

Do not import `Probe411` and do not rebuild it. **If `[LJ-1.411]` returned
NO-GO, the hypothesis is still the right telescope**: build this term against
it and say so.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-412/Probe412.agda::coded-descent"]

## SCOPE (write)
- agents/tasks/LJ-1-412/Probe412.agda
- agents/tasks/LJ-1-412/lj-1.412-report.md
- agents/tasks/LJ-1-412/review-of-coded-descent.md

## PREMISES
- `IsCardinalL` is a Pi over `δ : S` with a truncated code and `Empty.⊥` at the end, so its negation is a truncated existence under `lem`. Basis: src/L/Cardinal.lagda.md:230
- The code quantifier inside it is over ALL of the L-carrier, not over a stage. Basis: src/L/Cardinal.lagda.md:233
- `leastOrd` selects the least ordinal with an hProp property, as DATA, over ALL ordinals. Basis: src/L/Stage.lagda.md:149
- `mem-ord` gives the ordinal certificate of a member of an ordinal. Basis: src/L/Ordinal.lagda.md:221
- `isL-trans` gives constructibility of a member of an L-element, and `isL` is an hProp. Basis: src/L/Constructible.lagda.md:379
- The readback from a code to an ambient injection is `Small`, delivered in `src/`. Basis: src/L/Coding/Injection.lagda.md:123
- `[LJ-1.402]` measured that readback as TWO projections. Basis: agents/tasks/LJ-1-402/Probe402.agda:81
- `[LJ-1.410]` built the same descent under `Ne°` at 31 non-blank code lines. Basis: agents/tasks/LJ-1-410/lj-1.410-report.md:64
- `[LJ-1.410]`'s `nofin-at-selected` recovers infiniteness FROM the arrow at 13 non-blank code lines. Basis: agents/tasks/LJ-1-410/lj-1.410-report.md:41
- `[LJ-1.410]` states the caller obligation `CallerNe°` that this task discharges. Basis: agents/tasks/LJ-1-410/lj-1.410-report.md:145
- `[LJ-1.403]` states gap 1, the placement of `δ`, which this task does not pay and does not need. Basis: agents/tasks/LJ-1-403/lj-1.403-report.md:144
- `no-fin-descent` is the eight-line device the recovery runs on. Basis: agents/tasks/LJ-1-398/Probe398.agda:213
- `finite-excl-ω` is the delivered refutation under it. Basis: src/L/InjChain.lagda.md:153
- `L.Stage` reads `S` from the ambient structure and `L.Cardinal` reads `S` from the L structure. Basis: src/L/Stage.lagda.md:60

## WHAT IS DELIVERED ALREADY

**THE ASSEMBLY, UNDER THE WRONG HYPOTHESIS.** `[LJ-1.410]` built
`sel-descent-nofin` green, with every field of the conclusion as data
(`agents/tasks/LJ-1-410/lj-1.410-report.md:64-84`). It takes `Ne°`, a truncated
existence over `Mem (Lset (SiteBound.β κ))`
(`agents/tasks/LJ-1-410/lj-1.410-report.md:136-138`).

**THE HYPOTHESIS THE RECURSION HOLDS IS NOT THAT.** It is
`IsCardinalL κ → Empty.⊥` together with `⟨ ω ∈ˢ fst κ ⟩`
(`agents/tasks/LJ-1-410/lj-1.410-report.md:145-150`). Two gaps sit between the
two, and both are placements.

**THE RECOVERY.** `nofin-at-selected` turns an arrow out of an infinite ordinal
into the consumer's own spelling of infiniteness, at 13 code lines
(`agents/tasks/LJ-1-410/lj-1.410-report.md:41`).

## WHAT IS MISSING

**NOBODY HAS DERIVED THE SELECTION FROM THE NEGATION.** Three tasks took
`Ne⁺` or `Ne°` as a hypothesis and each one handed the caller a placement bill
(`agents/tasks/LJ-1-403/lj-1.403-report.md:144` and `:154`,
`agents/tasks/LJ-1-410/lj-1.410-report.md:154` and `:164`). The bill exists
only because the selection was written over `Mem (Lset (SiteBound.β κ))`.
**Neither the `δ` nor the `F` has to be selected there.**

## THE REASONING

**SEVEN STEPS, AND EVERY ONE IS A DELIVERED DEVICE.**

1. **W3, and it is first.** See below. From `IsCardinalL κ → Empty.⊥` and
   `lem`, get

       ∥ Σ[ δ ∈ S ] (⟨ fst δ ∈ˢ fst κ ⟩ × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁

2. **The ordinal form.** `leastOrd` selects an ordinal, so restate step 1 over
   the AMBIENT carrier:

       Good : Sᵥ → Ω
       Good d = ∥ Σ[ δ ∈ S ] ((fst δ ≡ d)
                             × ⟨ fst δ ∈ˢ fst κ ⟩
                             × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁

   and lift step 1 to `∥ Σ[ d ∈ Sᵥ ] (IsOrd d × ⟨ Good d ⟩) ∥₁` with `mem-ord`
   (`src/L/Ordinal.lagda.md:221`) for the certificate.

3. **The ordinal, as data.** `leastOrd Good` applied to step 2
   (`src/L/Stage.lagda.md:149`). Minimality is free and this task does not
   spend it.

4. **The L-element, as data.** `δ₀ = (d₀ , isL-trans ...)`, with
   constructibility from the membership and `isL (fst κ)`
   (`src/L/Constructible.lagda.md:379`). `isL` is an hProp, so `δ₀` is the same
   L-element as the one inside the truncation, by `Σ≡Prop`. **Both remaining
   fields of `Good d₀` are hProps**, so `PT.rec` takes them out: the membership,
   and the truncated code at `δ₀`.

5. **The code, as data.** `code-as-data κ δ₀` on step 4's truncated code.

6. **The arrow.** Open `Small` at the three sets and take the two projections,
   exactly as `[LJ-1.402]` measured (`agents/tasks/LJ-1-402/Probe402.agda:81`).
   **BUILD IT. Do not take it as a hypothesis.** `[LJ-1.403]` and `[LJ-1.410]`
   both hypothesized a generic readback; `module Small` is delivered in `src/`
   at `src/L/Coding/Injection.lagda.md:123` and the generic type is what it
   gives.

7. **The infiniteness.** `nofin-at-selected` on the arrow and `⟨ ω ∈ˢ fst κ ⟩`.
   Rebuild the 13 lines; do not import `Probe410`.

**DO NOT PUT THE BAND MEMBERSHIP IN.** The band is the recursion's context and
not this term's, exactly as `[LJ-1.398]` and `[LJ-1.410]` left it out
(`agents/tasks/LJ-1-398/Probe398.agda:206`).

**W2 (DD4).** Every statement is generic in `κ`. Name no cardinal and no
numeral except `ω`.

**W3, THE WIDEST UNMEASURED TERM.** It is STEP 1, because no task in this
campaign has ever consumed the negative case as a hypothesis:

    not-card-gives :
        (κ : S) → (IsCardinalL κ → Empty.⊥)
      → ∥ Σ[ δ ∈ S ] (⟨ fst δ ∈ˢ fst κ ⟩
                     × ∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁) ∥₁

**State it ALONE, run it, and report its code lines before you write step 2.**
It is one `lem` at the truncation: if the truncation is refuted, then every `δ`
with the membership refutes its own code existence, which is `IsCardinalL κ` by
definition (`src/L/Cardinal.lagda.md:230-233`). ESTIMATE: about 14 code lines.
BASIS: `[LJ-1.394]`'s `amb-gives-merely` is the same shape at the ambient
predicate and it is green (`agents/tasks/LJ-1-394/lj-1.394-report.md:87`).
ESTIMATE for the whole obligation: about 55 code lines. BASIS: `[LJ-1.410]`'s
`sel-descent-nofin` at 31 (`agents/tasks/LJ-1-410/lj-1.410-report.md:64`) plus
the recovery at 13 (`:41`) plus steps 1 and 2. **Comparables of SHAPE, not of
size, and nothing may be funded against them.**

**D-10, AND THE BRIEF ANSWERS IT.** Step 1 is a De Morgan move under `lem` and
it carries no cardinality claim. Step 4 is where a false step would hide: if
`isL` were not an hProp the rebuilt `δ₀` would not be the selected one. It is
an hProp (`src/L/Constructible.lagda.md:379-380` reads it through `PT.rec` into
`snd (isL y)`). **If step 4 fails, report it as a truth question and stop.**

## WHAT GO AND NO-GO EACH EARN

**A GO DISCHARGES `CallerNe°` AND ENDS THE PLACEMENT BILL OF THE CODED ROUTE.**
The descent then runs from the band recursion's own case hypothesis, with no
caller obligation left. `[LJ-1.413]` is written from it.

**A NO-GO EARNS THE STEP AND THE `file:line` THAT BLOCKS IT.** Name which of
the seven steps failed and what its type would have to be. **A stated NO-GO is
a full return.**

**STATE THE REMAINING CALLER OBLIGATION AS A TYPE IN YOUR REPORT**, whatever
the outcome, the way `[LJ-1.403]` and `[LJ-1.410]` stated theirs. The next brief
is written from it.

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
  changed_files_any = ["agents/tasks/LJ-1-412/Probe412.agda"]
  changed_files_none = ["agents/tasks/LJ-1-412/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-412/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Coding
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
