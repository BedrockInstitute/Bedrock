# LJ-1.568 report: the weakest hypothesis is the conclusion, and no site supplies it

## HEAD
head_slot: coder
machine: shared
task: LJ-1.568
obligation: agents/tasks/LJ-1-568/Probe568.agda::W-restricted
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-568/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, and there is no
hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it. Nothing lands in
`src/`. I did not attempt the assignment and I did not attempt `StageHigh`.

**NO HEAP EVENT.** The largest maximum resident set size of any run is
784,793,600 bytes, about 748 MiB, against the 8 GB cap
(`agents/tasks/LJ-1-568/runs/final-1.out`). No run gave exit 251. No run
printed a heap message.

## VERDICT

**GO. `W-restricted` IS BUILT** at `agents/tasks/LJ-1-568/Probe568.agda:542-561`.
The program meter agrees: `witness: 0 UNRESOLVED of 1, 5.64 s,
probe_red=False` (`runs/witness-1.out`). The twenty-nine other terms this
report names also all resolve, `0 UNRESOLVED of 29` (`runs/witness-2.out`).

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`runs/final-1.out` to
`final-3.out`, 3.13 s, 3.13 s, 3.20 s). The interface cache was warm, so this
report bounds no cold figure.

**THE ANSWER IN THREE LINES.**

1. **The weakest sufficient hypothesis on `g` is not a matter of search.** It
   is `[LJ-1.554]`'s `LinkAt` moved to `g`: some formula of the object
   language describes `g` on the members of `a`. I call it `Def`
   (`Probe568.agda:189-190`). `weakest` (`:377-381`) proves that EVERY
   sufficient hypothesis implies it.
2. **Under `Def` the statement stops being a residue.** `def-restricted`
   (`:252-253`) PROVES the restricted `W`. Nothing is left for a later task to
   pay at the general pair.
3. **None of the three sites supplies `Def`, and that is a theorem and not a
   failed search.** `no-free-lunch-at-link` (`:409-424`) and
   `no-free-lunch-at-B9` (`:454-463`) are stated at a QUANTIFIED hypothesis
   `H`. They say: a site that can supply ANY sufficient hypothesis has thereby
   closed its own obligation.

**SO THE BRIEF'S REQUEST HAS NO SOLUTION OF THE SHAPE IT EXPECTED, AND THE
PROOF OF THAT IS THE DELIVERABLE.** A hypothesis strictly weaker than the
conclusion is not sufficient. A hypothesis a site can discharge is a hypothesis
that site did not need.

## W AS STATED

**NOT REFUTED, AND NOT FOR WANT OF BUDGET.** The reason is one typechecked row.

`refuting-W-refutes-V=L : (P561.W → Empty.⊥) → ((x : V ℓ) → ⟨ isL x ⟩) → Empty.⊥`
(`Probe568.agda:120-121`). It is `[LJ-1.561]`'s `vl→w`
(`agents/tasks/LJ-1-561/Probe561.agda:195-196`) contraposed and nothing else.
**A refutation of `W` is a refutation of `V = L` in this ambient theory.** The
tree carries no non-constructible set and no chapter of `src/` refutes `V = L`;
the campaign studies what holds INSIDE L. So the D-10 attempt cannot succeed
here, and I stopped it rather than spend the budget on it.

`V=L→W` (`:127-128`) is the same row forwards, so `W` is not `Empty` either.
`W` sits between the two: not provable in this tree, not refutable in it.

**WHAT I DO NOT BELIEVE ABOUT `W` IS NOW A MEASUREMENT AND NOT AN OPINION.**
`def∥↔conclusion` (`:387-393`) proves that `W`'s conclusion at a triple
`(a , b , g)` is EQUIVALENT to `Def` at that triple, for every injective `g`.
So `W` says: every ambient injection between the members of two L-sets is
DEFINABLE over L. An arbitrary ambient function carries no formula. That is the
statement I disbelieve, and it is now written in a form the next brief can
quote.

## THE RESTRICTION

**THE HYPOTHESIS, IN FULL.** `Def a b g` is `[LJ-1.554]`'s `LinkAt`
(`agents/tasks/LJ-1-554/Probe554.agda:80-89`) at the assignment `k ↦ g k`:

    val a b g k = up b (g k)                            Probe568.agda:176-177

    Def a b g = P554.LinkAt a (val a b g)               Probe568.agda:189-190

      = Σ[ Link ∈ Formula S 3 ]
          ( ((x y z : S) (m : ⟨ fst x ∈ fst a ⟩)
             → fst y ≡ fst (val a b g (ixOf a x m))
             → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
          × ((x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
             → (m : ⟨ fst x ∈ fst a ⟩)
             → fst y ≡ fst (val a b g (ixOf a x m))) )

In words: SOME formula of the object language describes `g` on the members of
`a`, in both directions. `Def∥ a b g` is that type truncated
(`Probe568.agda:258-259`), and the truncated form is what the obligation uses,
because the conclusion is truncated already.

**FOUR THINGS THE HYPOTHESIS DOES NOT ASK FOR.** No Levy grade. No stage. No
size bound. No choice principle. The constants of `Formula S 3` are the L-sets
themselves, so arbitrary L-parameters are free
(`agents/tasks/LJ-1-554/Probe554.agda:131-146`). **The absence of the grade is
`[LJ-1.560]`'s gift and not my economy**: the carve runs through
`hasSeparationL`, which takes an ARBITRARY formula
(`src/L/Axioms/Full.lagda.md:144`, re-ascribed at `Probe568.agda:518-521`).

**IT IS SUFFICIENT, AND THAT IS PROVED HERE.** `def-restricted`
(`Probe568.agda:252-253`) inhabits `Restrict Def`. The construction is
`module Build` (`:207-249`) and it adds no mathematics: it instantiates
`[LJ-1.549]`'s `module Table` (`agents/tasks/LJ-1-549/Probe549.agda:268-438`)
and converts the result to `[LJ-1.561]`'s `IsGraph`. `Table` wants a `κ` with
every value a SUBSET of κ; that costs nothing and is not a second hypothesis,
because `⋃ b` inside L serves for every `b` (`hasUnionL`,
`src/L/Axioms/Basic.lagda.md:731`, spent at `Probe568.agda:216-221`).

**IT IS NECESSARY, AND THAT IS PROVED HERE TOO.** `graph→def`
(`:368-371`) turns the conclusion back into `Def`, through
`[LJ-1.554]`'s `graph→link` (`Probe554.agda:232-235`) and one converter,
`isGraph→isGraphOf` (`Probe568.agda:343-365`).

**SO IT IS THE WEAKEST.** `weakest` (`:377-381`) reads: for every `H`, if
`Restrict H` holds then `H a b g` implies `Def∥ a b g` at every injective `g`.
Any hypothesis strictly weaker than `Def∥` is therefore not sufficient. **I did
not choose the hypothesis. The two halves fix it.**

### One row per site

| site | does it supply `Def`? | evidence |
|---|---|---|
| **B9**, `[LJ-1.533]` | **NO** | `no-free-lunch-at-B9`, `Probe568.agda:454-463`. A supply at this site hands over `InjL (LsetS δ oδ) (ordS δ oδ)`, which IS the site's obligation. The site's own `g` is `SC.Upper.stage-card-upper δ oδ δ∈suc infδ` (`runs/W3.agda:98-102`, re-ascribed at `Probe568.agda:144-147`), and that term is built from the module parameter `sq`, an ARBITRARY ambient pairing injection (`src/L/StageCardinal.lagda.md:15-19`). Nothing in the tree gives `sq` a formula. |
| **B7**, `[LJ-1.535]` | **NO** | The same row. `restrict→B7` is defined as `restrict→B9` (`Probe568.agda:296-301`), so the restriction does not separate the two sites either. `[LJ-1.561]` measured that identity first (`Probe561.agda:388-391`). |
| **`Link`**, `[LJ-1.549]` and `[LJ-1.554]` | **NO, AND SHARPER THAN THAT** | `no-free-lunch-at-link`, `Probe568.agda:409-424`: a supply hands over `[LJ-1.549]`'s whole `Residue`. And at this site the hypothesis IS the residue, both directions: `def-at-link→residue` (`:434-440`) and `residue→def-at-link` (`:442-448`), through `link-val` (`:427-432`), which uses `[LJ-1.561]`'s `Link.g-val` (`Probe561.agda:314-315`). |

**THE ROW THE NEXT BRIEF SHOULD READ FIRST IS NOT IN THAT TABLE.** `B9-any-g`
(`Probe568.agda:490-495`) measures that site B9 is FREE TO CHANGE ITS `g`. B9's
obligation names no function: it asks for SOME code at the pair
`(LsetS δ oδ , ordS δ oδ)`. So the hypothesis does not have to hold of
`stage-card-upper`'s `g`. It is enough that it holds of ONE injection there.
**AND THE TWO SIDE CONDITIONS DISAPPEAR WHEN IT DOES.** `δ ∈ˢ sucV α₀` and
`δ ∉ˢ ω` are `stage-card-upper`'s hypotheses
(`src/L/StageCardinal.lagda.md:564-565`), and their only work at this site was
to produce the ambient injection. In `B9-any-g` they are absorbed into the Σ.
**THIS DOES NOT ROUTE PAST `[LJ-1.533]` AND IT CLAIMS NOTHING THAT REVIEW
REFUSED TO CLAIM.** That review says in its own words that it "did not prove
`⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ"
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55`). What it
measured is that the brief's unrestricted type is not reachable from the
delivered chapter, and that the chapter's author excluded the finite case by
hypothesis (`:42-52`). `B9-any-g` CONSUMES an injection and never produces one,
so at a δ where the Σ has no inhabitant the row says nothing.

Site `Link` has no such freedom. Its `g` is fixed by the `s` the residue
quantifies over (`agents/tasks/LJ-1-549/Probe549.agda:668-669`).

### Does `[LJ-1.560]` supply it

**NO, AND THE TYPE SAYS WHY.** `search-bounds` TAKES a formula and RETURNS a
stage (`agents/tasks/LJ-1-560/Probe560.agda:165-176`), re-ascribed TYPE ONLY at
`Probe568.agda:504-510`. A site with no formula gets no formula from it. The
brief named it as the most likely source; it is not the source.

**WHAT IT DOES BUY IS REAL.** `[LJ-1.560]` section 5c is `hasSeparationL`,
separation in L at an ARBITRARY formula (`Probe560.agda:223-225`). That is why
`Def` carries no Δ₀ side condition, and section 2 of my probe pays nothing for
its absence. **`[LJ-1.560]` makes the hypothesis WEAKER; it does not make it
SUPPLIABLE.**

## THE SWEEP (C-42)

A refutation measures one site. I refuted nothing, but the finding has a shape,
so I counted the shape. **The shape is `⟨ isL (<an ambient set already built>) ⟩`.**

| site | where | is it this task's shape? |
|---|---|---|
| `grV δ s`, the assignment's graph | `agents/tasks/LJ-1-554/Probe554.agda:281`, `:284`, `:308`, `:344` | YES. `Def` is equivalent to it (`Probe554.agda:308`) |
| the same graph inside `W` | `agents/tasks/LJ-1-561/Probe561.agda:173` | YES |
| `StageIsL`, R4 | `agents/tasks/LJ-1-550/Probe550.agda:318` | SAME SHAPE, DIFFERENT SUBJECT |
| `StageIsL`, R4 | `agents/tasks/LJ-1-558/Probe558.agda:213` | SAME SHAPE, DIFFERENT SUBJECT |
| `StageIsL`, R4 | `agents/tasks/LJ-1-564/Probe564.agda:114` | SAME SHAPE, DIFFERENT SUBJECT |

**THE COUNT IS FIVE SITES AND TWO SUBJECTS.** Two ask `isL` of a GRAPH and
three ask `isL` of a STAGE, `Lset (fst δ)`. **I MEASURED ONLY THE GRAPH
SUBJECT.** This report claims nothing about `StageIsL`: a stage is not a graph,
and a measured cure does not transfer by analogy. **The count is the reason to
ask.** If the three `StageIsL` rows are also "definable over L, and nothing
else", then one definability statement stands behind five rows and not two.

## W3, WRITTEN FIRST AND ALONE

`agents/tasks/LJ-1-568/runs/W3.agda`, 130 lines, of which 55 are Agda. Three
runs, exit 0, `runs/w3-1.out` to `w3-3.out`, 1.46 s, 1.46 s, 1.47 s,
412,336,128 bytes maximum resident set size. **The brief estimated about 12
lines and under 60 seconds. The file is longer and it is well inside the time.**
It was green on the first attempt.

It writes the type of the `g` at `w→B9`'s call site
(`runs/W3.agda:84-102`), the two L-sets that site hands over (`:63-67`), and
the site's whole list of side conditions (`:110-113`).

**ITS FINDING IS THE PARAMETER.** `stage-card-upper` is a term of
`L.StageCardinal`, and that module takes `sq` as a parameter
(`src/L/StageCardinal.lagda.md:15-19`). So the B9 site's `g` is not one
function. It is a function OF an arbitrary ambient pairing injection. **Writing
the type first was the right order**: it is what made me state the restriction
at a quantified `H` instead of trying to invent a property `stage-card-upper`
might have.

## WHAT THE OBLIGATION COST

**The probe is 561 lines: 228 comment, 68 blank, 265 Agda.** The brief estimated
about 190 lines with about 50 for the obligation. `W-restricted` itself is 20
lines (`Probe568.agda:542-561`) and it is only the pairing. The weight sits in
three places:

- `module Build` (`:207-249`, 43 lines). The proof of the restricted `W`.
- `isGraph→isGraphOf` (`:343-365`, 23 lines). The converter that makes `Def`
  necessary.
- the five `restrict→*` rows (`:277-325`, 49 lines), which are `[LJ-1.561]`'s
  four implications restated at a quantified `H`.

**THE FILE IS LARGER THAN THE ESTIMATE BECAUSE IT PROVES TWO THINGS THE BRIEF
DID NOT ASK FOR, AND BOTH ARE WHY THE ANSWER IS DECISIVE.** The brief asked for
a restricted `W` and three implications out of it. It did not ask for the
restricted `W` to be a THEOREM, and it did not ask for the hypothesis to be
proved WEAKEST. Without the first, the restriction would move the debt and not
pay it. Without the second, the answer would be my choice and not a
measurement.

**NOTHING IN `module Build` IS NEW MATHEMATICS, AND THAT IS THE POINT.** The
carve is `[LJ-1.549]`'s `Table`, instantiated. The bound is the union axiom of
L. The only new lines are the two index dances between `⟪ fst a ⟫` and the
members of `a` (`Probe568.agda:227-246`), and `[LJ-1.561]`'s `Link.convert`
does the same dance in the other direction (`Probe561.agda:321-342`).

**ONE CHOICE OF METHOD IS WORTH RECORDING.** I carved the graph by SEPARATION
and not by REPLACEMENT, although `hasReplacementL` takes a `Formula S 2` and
would collect the pairs directly (`src/L/Axioms/Full.lagda.md:277-281`, the
brief's premise 9). Two reasons. First, separation reuses `[LJ-1.549]`'s
`Table` whole and replacement would need the functionality proof written from
nothing. Second, the archive measured the same choice at a price:
`archive/dev/LJ-dispatch-index.md:230` records `[LJ-1.154]`, carving a graph by
separation rather than replacement, at 1.73 s against 254.22 s.

## WHAT THE SHAPE RESISTED. Two red runs, both kept.

1. `runs/red-1.out`, exit 42, `NotInScope: P560.Below`. `[LJ-1.560]`'s probe
   opens `L.Reflect` WITHOUT `public`, so `Below` and `Wit` are not re-exported
   from it. Cure: import them from `L.Reflect` directly
   (`Probe568.agda:63`). The same applied to `∃̇_` and `Δ₀`.
   **The general law is worth keeping: a predecessor probe re-exports only what
   it declares, never what it imports.**
2. `runs/red-2.out`, exit 42, `UnsolvedConstraints` and `UnsolvedMetaVariables`
   at the ascription of B9's target. I had written the bare pair
   `(δ , P561.isL-ord δ oδ)` under `⟪ fst _ ⟫`, where nothing gives the pair an
   expected type. `[LJ-1.561]` writes the same pair, but always as an argument
   of `InjL`, which supplies the type. Cure: name it once, `ordS`
   (`Probe568.agda:102-103`).

Every other run was green on the first attempt, including `B9-any-g`, which was
added after the first green run.

## WHAT I DID NOT MEASURE

- **I DID NOT REFUTE `W`, AND I DID NOT PROVE IT UNREFUTABLE.** What is proved
  is that a refutation of `W` is a refutation of `V = L`
  (`Probe568.agda:120-121`). That is a reason to stop, not a proof of
  independence, and this report does not claim independence.
- **I DID NOT PROVE THAT NO SITE CAN EVER SUPPLY `Def`.** A non-supply is not a
  type this tree can state. What is proved is that a supply CLOSES the site
  (`:409-424`, `:454-463`). The three sites are open today, so no supply exists
  today. That is an argument about the campaign's state and not a theorem.
- **I DID NOT MEASURE `StageIsL`.** See the sweep. The count is reported and
  the cure is not transferred.
- **I DID NOT ATTEMPT THE ASSIGNMENT OR `StageHigh`**, as the brief forbids.
- **I DID NOT BUILD A DEFINABLE WELL-ORDER**, and no row of this file assumes
  one exists in the tree.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **DO NOT FUND A SEARCH FOR A WEAKER HYPOTHESIS ON `g`.** `weakest`
   (`Probe568.agda:377-381`) closes that search. Every sufficient hypothesis
   implies `Def∥`, and `Def∥` is equivalent to the conclusion
   (`:387-393`). A task that asks for a weaker one is asking for something the
   tree proves does not exist.
2. **THE ONE LIVE DIRECTION IS TO CHANGE THE `g` AT SITE B9, NOT THE
   HYPOTHESIS.** `B9-any-g` (`:490-495`) shows the site accepts ANY injection
   at that pair, and drops the two side conditions when it gets one. **The
   literature names the injection to use, and it is not an ambient one.**
   Devlin's Step D takes the `<ʟ`-least-witness map of a DEFINABLE well-order
   of `L_α` (`dev/literature/devlin-II5.md:259-270`). A definable map has a
   formula by construction, so it supplies `Def` and it supplies it without
   circularity. **The missing object is therefore a definable well-order of a
   stage, not a graph statement.** D-26 says what such a key costs
   (`dev/LESSONS.md:1735`): generation data or syntax.
3. **SITE `Link` IS NOT ON THAT ROW AND MUST NOT BE ADDED TO IT.** Its `g` is
   fixed by the `s` its residue quantifies over, so it cannot change its `g`.
   At that site `Def` and the residue are the same type, both directions
   (`Probe568.agda:434-448`). **`W` is not a way to pay site `Link`. It is site
   `Link`, written at a different pair.**
4. **B9 AND B7 STAY ONE ROW UNDER THE RESTRICTION.** `restrict→B7` is
   `restrict→B9` (`:296-301`). Funding them apart still funds one statement
   twice.
5. **THE FRAME COST IS UNCHANGED AND SMALL.** This file takes
   `L.StageCardinal`'s three parameters, the way `[LJ-1.561]`'s does. The whole
   probe typechecks in 3.13 s warm.
6. **ONE COUNT IS OPEN AND IT IS CHEAP TO SETTLE.** Three probes state
   `StageIsL` (`Probe550.agda:318`, `Probe558.agda:213`, `Probe564.agda:114`).
   If `isL` of a stage is also "definable over L and nothing else", then one
   statement stands behind five campaign rows. **That question is a D-10 for a
   next brief and it is not answered here.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ**, and it carries the measured
  price of the method I chose. At `:230`:
  > | LJ-1.154 | Carve the identity graph by separation, not by replacement | GO: 1.73 s AGAINST 254.22 s | The device BUILDS, not only composes. Devlin's base theory has no replacement at all |

  and at `:228`:
  > | LJ-1.152 | Can two L-graphs compose without a second hasReplacementL | GO: 2.50 s, NO REPLACEMENT | Separation carries it, 2,500 to 1. The seal was NOT the cure and A5 is unpriced again |

  **The finding is positive and it changed my method.** Both rows say
  separation carries graph work that replacement makes expensive, and
  `module Build` runs through `hasSeparationL` for that reason.
- `dev/ARCHIVE.md`. **READ.** I opened it to check whether any retired module
  ever held machinery for turning an ambient graph into a set of L. The nearest
  row is `L.Godel.Tuples`, at `:282`:
  > | `L.Godel.Tuples` | `src/L/Godel/Tuples.lagda.md` | Assignments as graph sets, and their algebra against the operations: extension, shift, entrywise injectivity, and the family of all assignments over a carrier. D18 retires the satisfaction-internalization cone with the route change, and no surviving chapter imports `L.Godel`; verified at archival by `rg` over `src/` to have no importer outside the `Everything` index. Retired under D18 and D20, 2026-08-06. | `7bf2913` | 153 code lines, 22 obligations | Measured 0.009 s per obligation, 0.12x the 0.074 benchmark. Not yet assessed as a module-specific practice, same reason: 153 lines and 22 obligations; the abstract-carrier pattern is visible at `src/L/Godel/Tuples.lagda.md:112`. | If the assignments-as-graph-sets algebra is needed again; it is the substrate of the tuple operations. |

  **It is assignments as graph sets and not the `isL` step**, so it is not a
  revival of this task's question. The finding is negative and it is real: no
  retired module ever did what `Def` asks.
- `archive/dev/JOURNAL-archived.md`. **DECLINED, NOT READ.** A journal is
  history. This task's evidence is four live predecessor probes with
  `file:line`.
- `archive/dev/JOURNAL.md`. **DECLINED, NOT READ.** Same reason.
- `archive/dev/ORCHESTRATION.md`. **DECLINED, NOT READ.** It is the archived
  loop document. It bears on how a task is dispatched, not on whether an
  ambient injection has a formula.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ**, and it names the injection the B9
  site should use. At `:259`:
  > Requirement: a definable well-order of L_α, used to pick the <_L-least

  **The classical route does not use an arbitrary ambient injection at this
  site.** It uses a definable map, and a definable map supplies `Def` by
  construction. This is finding 2 of `## WHAT THE NEXT BRIEF NEEDS`.
- `dev/literature/truncation-and-selection.md`. **READ**, and it settles why
  the truncated hypothesis costs nothing. At `:143`:
  > the reason: "a proposition-valued goal absorbs the truncation"

  `def∥-restricted` (`Probe568.agda:261-262`) is one `PT.rec` into
  `∥ Σ G … ∥₁`, which is a proposition, so stating the hypothesis truncated is
  free and it makes the hypothesis weaker.
- `dev/literature/digest.md`. **READ**, and it corroborates finding 2 from the
  other tower. At `:334-335`:
  > 6. **AC without satisfaction; the well-order as a purely algebraic

  The J-tower's canonical well-order is built from a finite basis with no
  syntax, so its graph carries generation data rather than a formula. **Both
  towers therefore carry a definable ordering; neither carries an arbitrary
  ambient injection.** The digest marks the surrounding claim as its own
  analysis and not sourced, and I do not quote it as sourced.
- `dev/literature/terms-2026-08.md`. **DECLINED, NOT READ.** It is a
  terminology dossier and this task proposes no term. Clause W5 puts a naming
  question in a different pipeline.
- `dev/literature/glossary-review-2026-08.md`. **DECLINED, NOT READ.** Same
  reason: no glossary entry is proposed or needed here.
