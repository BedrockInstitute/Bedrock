# [LJ-1.584] report: the formula for the stage-cardinality bound

## HEAD
head_slot: coder
machine: shared
task: LJ-1.584
obligation: agents/tasks/LJ-1-584/Probe584.agda::stage-bound-definable
verdict: NO-GO

The report was written as a skeleton before any proof Agda and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-584/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **NO HEAP EVENT**: the largest maximum resident set size of any run of
mine is 1,620,688,896 bytes, about 1.51 GiB, against the 8 GB cap
(`agents/tasks/LJ-1-584/runs/floor-cold-1.out`). No run of mine gave exit 251
and no run printed a heap message. Nothing is postulated, the probe carries
`--safe`, and there is no hole. Nothing lands in `src/`. The probe is a raw
`.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

**THE MACHINE WAS SHARED AND I MEASURED THE CONTENTION.** At 04:24Z a second
Agda process appeared on this host, pid 5251, checking
`agents/tasks/LJ-1-582/runs/S6.agda`, at 8,410,912 KB resident. It is not mine
and I did not touch it. Every number below was taken with my own process at
about 1.1 to 1.6 GiB; the floor pair at 04:17 to 04:18 predates pid 5251.

## VERDICT

**NO-GO on `stage-bound-definable`**, and
`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md` states it.

**THE PROBE IS GREEN, EXIT 0, FOUR RUNS** (`runs/final-1.out` to
`runs/final-3.out`, and `runs/final-4.out`. All four postdate the last edit to
`Probe584.agda`, so the tree is exactly as described). Green and not holed is
deliberate: every reduction in the file is then a measurement and not a claim.

**THE ANSWER IN FOUR LINES.**

1. **THE STATEMENT IS NOT FALSE AND I DID NOT REFUTE IT.** `V = L` gives it
   outright and UNTRUNCATED: `vl→obligation` (`Probe584.agda:108`). So a
   refutation of the obligation is a refutation of `V = L`
   (`refuting-obligation-refutes-V=L`, `:126`).
2. **AND `L.StageCardinal` CANNOT BUILD IT, FOR A REASON THAT IS A THEOREM.**
   `value-is-a-sq-value` (`Probe584.agda:200`): **every value of the injection
   is a value of `fst (sq α α∈suc infα)`**, and `sq` is a module parameter
   carrying injectivity and nothing else (`src/L/StageCardinal.lagda.md:17-19`).
   By `[LJ-1.568]`'s `def∥↔conclusion` the obligation is EQUIVALENT to putting
   that function's graph into L, which is `[LJ-1.533]`'s wall
   (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`).
3. **THE BRIEF ASKED FOR MORE THAN `[LJ-1.580]`'s REOPENER SPENDS.**
   `Obligation` (`:95`) must name `stage-card-upper`, so it carries `sq`.
   `Reopener` (`:250`) is `InjL (Lset α) α`, a TRUNCATION over all codes
   (`src/L/GCH.lagda.md:38`); it names no injection. This is the finding the
   next brief needs and section `## THE FORMULA` gives it in full.
4. **AND THE SAME AMBIENT SHAPE KILLED THE OTHER ROUTE.** The C-42 sweep counts
   SEVEN parameter lines, THREE objects, THREE chapters. `absorbs` is
   `[LJ-1.580]`'s block and `sq` is mine, in the same two chapters.

**I DID NOT ATTEMPT ROW 1 OR ROW 4. I DID NOT POSTULATE. NOTHING LANDS IN
`src/`.**

## THE FLOOR

**MEASURED FIRST, BEFORE ANY OTHER AGDA, AS D-10 ORDERS.**
`agents/tasks/LJ-1-584/runs/Floor.agda` is the obligation's type with a hole in
the smallest import set that holds it: the module parameters, `LsetS`,
`L.StageCardinal`, and `[LJ-1.568]`'s `Def` imported. Exit 42 with exactly one
`UnsolvedInteractionMetas` at `Floor.agda:44`, so the STATEMENT is well formed
and only the hole is open.

| run | wall | peak RSS | exit |
|---|---|---|---|
| `runs/floor-cold-1.out` | 14.66 s | 1,620,688,896 B (1.51 GiB) | 42, the hole |
| `runs/floor-warm-1.out` | 2.67 s | 814,432,256 B (0.76 GiB) | 42, the hole |

**THE FINISHED TERM'S FLOOR**, the whole probe, no hole:

| run | wall | peak RSS | exit |
|---|---|---|---|
| `runs/final-1.out` | 26.32 s | 1,578,254,336 B (1.47 GiB) | 0 |
| `runs/final-2.out` | 3.13 s | 790,052,864 B (0.74 GiB) | 0 |
| `runs/final-3.out` | 3.07 s | 790,069,248 B (0.74 GiB) | 0 |
| `runs/final-4.out` | 3.36 s | 790,118,400 B (0.74 GiB) | 0 |

**SO THE FRAME IS NOT A CAUSE OF A TIMEOUT AT THIS SITE.** `[LJ-1.559]` used a
trimmed frame's 1.39 s warm and 4.12 s cold the same way
(`agents/tasks/LJ-1-559/lj-1.559-report.md:58-59`, and its own conclusion at `:84`); this frame is 2.67 s warm and
14.66 s cold and it holds the whole obligation. **A measured cure does not
transfer by analogy and neither does a measured cause: I re-measured here.**

**AND I FOUND A CAUSE THAT IS NOT THE FRAME.** See the next section.

## W3: `step`, RE-ASCRIBED ALONE

The brief: "Write it FIRST and typecheck it ALONE ... you will know in the first
hour." I did, and it produced the most surprising number of the task.

**W3 IS GREEN AND CHEAP.** `agents/tasks/LJ-1-584/runs/W3a.agda`, exit 0,
**1.22 s**, 313,917,440 B (0.29 GiB), `runs/w3a-1.out`. Two rows: `step`
re-ascribed alone at its delivered type (`W3a.agda:36`), and `pair-is-sq`
(`:41-46`), which is `refl`.

**BUT ONE ROW I ALSO WROTE DOES NOT TERMINATE, AND THAT IS A MEASUREMENT.**
`runs/W3b.agda` is the same file plus ONE row: `step α IH oα α∈suc infα`
against `limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)` by `refl`,
which is `src/L/StageCardinal.lagda.md:562` read back.

- First attempt, `runs/w3-1.out`: killed by me at about 5 min 05 s wall, 98.8%
  CPU, resident set PINNED at 1,154,848 KB across samples at 03:58 and 04:56
  elapsed. **A conversion loop and NOT a heap event**, so the heap-wall protocol
  does not apply and I did not simply rerun it.
- Isolation, `runs/w3b-1.out`: a 180 s bound the run did not reach the end of.

**`runs/W3b.agda` IS KEPT AS THE EVIDENCE AND MUST NEVER BE ADDED TO A TYPECHECK
SWEEP.** It is not reachable from `src/Everything.lagda.md` and `make typecheck`
does not see it; `check-probes` is clean with it in place (exit 0).

**BISECTED: the same file WITHOUT that row is green in 1.22 s.** So the cost is
one row and not the frame. **NO ROW OF `Probe584.agda` PUTS `step` INTO A
CONVERSION PROBLEM**; section 2 measures `limit-step` instead, which is the same
value at every stage the induction visits, and costs 25 s cold.

**WHAT `step` DOES**, which the brief ordered said at `file:line`.
`step α IH oα α∈suc infα = limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)`
(`src/L/StageCardinal.lagda.md:562`). `limit-step` (`:396-403`) is
`LimitStep.h` and `LimitStep.h-inj` at `D := DefOf.defSet (Lset δ)` and
`inv := 𝒟ₒ-inv`. And `LimitStep.h` (`:350-351`) is

    h x = fst (leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x))

the LEAST `y ∈ α` under the ordinal order satisfying `class-pred x y`
(`:319-324`):

    ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪α⟫↪ m) ⟫ 1 ]
        ( D (⟪α⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x ) × ( B.pair m (cnt m φ) ≡ y ) ∥₁

**THREE INGREDIENTS, AND TWO OF THEM ARE ALREADY INTERNAL.** `D` is `defSet`,
which is `𝒟ₒ` (`:400-401`). `leastOf` is the ordinal order (`:258-259`).
**THE THIRD IS `B.pair`, AND IT IS `sq` APPLIED** (`:283`, and `pair-is-sq` is
`refl`). `cnt` (`:288`) is `B.formula-bound`, which is built from the same
`B`, so it is `sq` too.

**THE PAIRING IS THE ONLY UNDESCRIBED INGREDIENT.** That is the whole finding.

## THE FORMULA

**THERE IS NO FORMULA IN THIS PROBE, AND THIS SECTION SAYS WHAT WAS ASKED, WHAT
THE TWO DIRECTIONS WOULD HAVE BEEN, AND WHERE EACH BREAKS.**

**THE ARITY IS THREE.** `Def a b g` is `[LJ-1.554]`'s `LinkAt a (val a b g)`
(`agents/tasks/LJ-1-568/Probe568.agda:189-190`), and `LinkAt`
(`agents/tasks/LJ-1-554/Probe554.agda:80-89`) is

    Σ[ Link ∈ Formula S 3 ] ( into × out )

`Formula S 3`: three free variables, assigned `(y ∷ x ∷ z ∷ [])`, with `z` a
spectator. **The constants are the L-sets themselves**, so parameters in L are
free and I did not spend a line trying to eliminate them, as the brief ordered.

**DIRECTION ONE, `into`.** For every `x` in `Lset α` and `y` equal to `g x` as
an L-set, `Link` must hold at `(y ∷ x ∷ z ∷ [])`. To write it I must name `h x`
inside the object language. By `value-is-a-sq-value` (`Probe584.agda:200`),
`h x` is `fst (sq α α∈suc infα) (m , cnt m φ)` for the witnessing pair. **`sq`
is a module parameter of type `⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` with injectivity and nothing
else** (`src/L/StageCardinal.lagda.md:17-19`). No formula names it, and no
hypothesis in scope says one exists.

**DIRECTION TWO, `out`.** If `Link` holds at `(y ∷ x ∷ z ∷ [])` and `x ∈ Lset α`,
then `y` must BE `g x`. This is the harder half and it fails for the same
reason: to exclude every wrong `y`, the formula must pin `fst (sq α α∈suc infα)`
on the whole set `{ (m , cnt m φ) }`, which is exactly a code for an arbitrary
ambient function.

**AND THE TWO DIRECTIONS TOGETHER ARE NOT WEAKER THAN THE GRAPH.**
`[LJ-1.568]`'s `def∥↔conclusion` (`Probe568.agda:387-393`) proves `Def∥` is
EQUIVALENT to the graph of `g` being an L-set, so there is no cheaper reading of
the demand.

**I FOUND NOTHING THAT NEEDED A LEVY GRADE, A STAGE OR A SIZE BOUND**, so the
brief's warning did not fire and no measurement is contradicted.

**WHAT THE NEXT BRIEF SHOULD ASK FOR INSTEAD.** `Reopener`
(`Probe584.agda:250`) is `InjL (LsetS α oα) (ordS α oα)`, and
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:38`). Read the
two signatures against each other: `Obligation` takes `α∈suc` and `α∉ω` because
it must name `stage-card-upper`; `Reopener` takes neither. **A target that
quantifies over all codes cannot demand one named function**, so the obligation
is sufficient (`obligation→graph`, `:230`) and strictly stronger than needed.

## WHAT THE NEXT BRIEF NEEDS

1. **AIM AT `Reopener`, NOT AT `Obligation`.** It is `sq`-free and truncated, so
   a next probe may assume `SqFam α` freely under `PT.rec` and build ANY coded
   injection.
2. **OR RE-PARAMETERISE `L.StageCardinal` WITH A DESCRIBABLE PAIRING.** Section
   2's theorem would then carry a formula through to `h`, because the other two
   ingredients are internal already. **Priced against nothing measured; named as
   a route, not funded.**
3. **OR MEASURE THE WEAKLY CONSTANT ENDOMAP ON `sq δ`, WHICH THE ARCHIVE ALREADY
   NAMED AS THE WIDEST UNMEASURED TERM** (`archive/dev/JOURNAL.md:1366-1367`).
4. **DO NOT WRITE A `refl` AGAINST `step`.** See `## W3` above. This is the one
   operational law this task discovered and it cost 7 minutes to find.

**AND ONE BRIEF PREMISE DOES NOT CHECK.** Premise 10's basis is
`agents/tasks/LJ-1-572/LJ-1.572.md:1`, and `agents/tasks/LJ-1-572/` DOES NOT
EXIST at this tree. Its rows are in `dev/pod/table.toml:19146-19160`, admitted
2026-08-23. I relied on none of the premise; I report the basis because a report
that cannot be checked can only be believed.

## THE C-42 SWEEP

C-42 orders the count before the cure, and the law is mandatory in this brief's
bundle. The shape is **a bare ambient injection handed to a chapter of `src/` as
a module parameter, carrying injectivity and no `Formula`**. Grepped at today's
tree: **SEVEN parameter lines, THREE distinct objects, THREE chapters.** The
table is in the review file. `sq` has a producer, truncated
(`src/L/SquareLawClosed.lagda.md:325-328`); `absorbs` has none.

## W2 AND W4

**W2.** The brief states no generic-carrier obligation and the probe adds no
mathematics to `src/`, so W2 has nothing to bind here. `Def` is already stated
at a generic pair `(a , b , g)` by `[LJ-1.568]` and I instantiated it rather
than restating it, which is the rule read forwards.

**W4.** No module was retired and none should be. Nothing moved to `archive/`.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ, AND IT CORROBORATES THE BLOCK.**
  `archive/dev/JOURNAL.md:940` reads "`src/L/StageCardinal.lagda.md:15-19` both
  demand an injective". The same entry at `:1367` reads "the next probe is named
  for it.", closing the sentence that names the weakly constant endomap on
  `sq δ` as the widest unmeasured term. That is route 3 of the review.
- `archive/dev/LJ-dispatch-index.md`. **READ.** `archive/dev/LJ-dispatch-index.md:82`
  reads "| LJ-1.24 | PROBE: is StageCardinal's limit half curable | ARM 1 WINS | 29.1 s to 2.3 s, 12.8x, for about 6 lines. R-38's class, NOT P-n's floor: the transport over a TRANSPARENT sett index costs".
  Read for a prior cost measurement on this chapter's limit half; it is a timing
  result and it does not bear on definability, so nothing above rests on it.
- `archive/dev/JOURNAL-archived.md`. **NOT USED.** Grepped for this chapter and
  for the square law; the hits (`:1338`, `:1394`, `:1437`, `:1449`) are campaign
  pricing for the square law's own build, not its definability. Declined.
- `dev/ARCHIVE.md`. **NOT USED.** Grepped for `StageCardinal`, `InjCode` and
  the square law: no hit. No module was retired by this task either, so the
  file takes no row from me. Declined.
- `archive/dev/ORCHESTRATION.md`. **NOT USED.** It is the archived process
  document; this task is a mathematical measurement and takes no rule from it.
  Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ, AND IT IS LOAD-BEARING
  TWICE.** `dev/literature/truncation-and-selection.md:146` reads "**The
  constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`".
  That is why `h`'s payload cannot come out as data. And
  `dev/literature/truncation-and-selection.md:158` reads "- **Theorem 16: \"A
  type X has a constant endomap if and only if it has split", which is the
  criterion route 3 of the review is named for.
- `dev/literature/devlin-II5.md`. **READ.** `dev/literature/devlin-II5.md:156`
  reads "|L_α| = |α| and |L_γ| = |γ|, so |γ| = |M| = |α| < κ, hence γ < κ and".
  This is the size equation the obligation is the internal form of, and it is
  where `[LJ-1.580]` pointed. **The source states it as a CARDINAL EQUATION, not
  as a named injection**, which is the same asymmetry section `## THE FORMULA`
  measures in Agda.
- `dev/literature/digest.md`. **NOT USED.** It pins the orthodox rud route;
  this task is on the definable-power route's stage bound and takes nothing from
  it. Declined.
- `dev/literature/geology.md`. **NOT USED.** Set-theoretic geology: mantles,
  grounds, Usuba. No bearing on a stage-cardinality formula. Declined.
- `dev/literature/terms-2026-08.md`. **NOT USED.** A terminology dossier for a
  naming ruling; this task adds no term and writes no glossary entry. Declined.
