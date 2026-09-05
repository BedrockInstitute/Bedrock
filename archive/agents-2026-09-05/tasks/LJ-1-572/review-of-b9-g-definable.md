# review of `b9-g-is-definable`: the obligation is not delivered, and the brief's premise is inverted

## RE-VERIFIED AT TODAY'S TREE, 2026-08-23

This file is the stop the original brief was rewritten to close on, and the
rewrite ordered the two load-bearing facts re-verified at today's tree
before restating it. **Both hold. The stop is restated, unchanged in every
word of substance, and the row closes on `stop-stated`.**

1. **`sq` is still a bare parameter with no formula. HOLDS.**
   `src/L/StageCardinal.lagda.md:17-19`: the module header quantifies
   `sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ →
   (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥) →
   Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
   ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)`. Injectivity, and nothing
   else: no `Formula`, no `isL`, no stage, no grade. Read at the site in this
   dispatch, 2026-08-23.
2. **`step` still reaches it by the chain the predecessor checked by `refl`.
   HOLDS.** `stage-card-upper = ∈-induction step`
   (`src/L/StageCardinal.lagda.md:566`); `step α IH oα α∈suc infα =
   limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)` (`:562`);
   `LimitStep`'s counting bound is `module B = Bound α oα infα
   (sq α α∈suc infα)` (`:283`), consumed by `cnt` (`:288`) and `cnt-inj`
   (`:291`). The same chain re-checked today by re-running the salvaged
   `agents/tasks/LJ-1-572/runs/W3.agda` (`unfold-1`, `unfold-2`, `sq-bare`:
   each hop a `refl` or a bare ascription of the parameter): exit 0, 1.70 s
   warm, one Agda process, pane caliber `-A64m -I0 -M2g`
   (`agents/tasks/LJ-1-572/runs/w3-4.out`).

Neither fact changed. Nothing in `src/` moved between the original stop and
this dispatch. **The stop is therefore restated, not repaired: NO-GO,
for the three reasons below, and the limit is kept in its own words: this is
evidence and not a refutation; a definable `sq` would make it true.**

## VERDICT

**NO-GO. `agents/tasks/LJ-1-572/Probe572.agda` binds no term named
`b9-g-is-definable`, and it binds no postulate and no hole.** The obligation is
not delivered. This file is the stop, and my clause makes a stop a deliverable
(`AGENTS.md:43-44`).

**THE BRIEF ORDERED THE ARITY READ FIRST AND CALLED IT "the whole risk in this
task". THE ARITY IS FREE.** `svAt`, `domAt` and `injAt` are arity-polymorphic:

| formula | signature | home |
|---|---|---|
| `svAt` | `∀ {n} → Fin n → Formula S n` | `src/L/Coding/Model.lagda.md:210` |
| `domAt` | `∀ {n} → Fin n → Fin n → Formula S n` | `src/L/Coding/Model.lagda.md:278` |
| `injAt` | `∀ {n} → Fin n → Formula S n` | `src/L/Coding/Injection.lagda.md:44` |

`Def` wants `Formula S 3` (`agents/tasks/LJ-1-568/Probe568.agda:190` is
`P554.LinkAt a (val a b g)`, and `LinkAt`'s Σ is over `Formula S 3`,
`agents/tasks/LJ-1-554/Probe554.agda:81-82`). All three come to 3 at no cost.
`Probe572.agda` section 1 typechecks each one at `Formula S 3`. **So the risk
the brief priced is not a risk, and the risk that stopped the task is one the
brief did not name.**

## THE THREE REASONS, IN THE ORDER THEY BITE

### 1. `InjCode` NAMES NO FUNCTION, SO IT CANNOT STATE EITHER DIRECTION

`InjCode : S → S → S → Type (ℓ-suc ℓ)` (`src/L/Cardinal.lagda.md:223`). It
takes three SETS. Both halves of `Def` mention `g`
(`agents/tasks/LJ-1-554/Probe554.agda:83-86`: one half sends a value to
satisfaction, the other reads a value back out). **No instance of a type that
never mentions `g` can supply either half.** `Probe572.agda` section 2 checks
that arity.

The brief asked which of the two readings the assembled code already supplies.
**NEITHER.** `svAt`, `domAt` and `injAt` are evaluated at the environment
`(F ∷ a ∷ [])` (`src/L/Cardinal.lagda.md:225-227`), with the CODE `F` in the
environment. They are statements ABOUT a code. `Def`'s formula is evaluated at
`(y ∷ x ∷ z ∷ [])` with no code in the environment at all. The two are not the
same shape of thing.

### 2. THE FRAME MISSES ON BOTH COMPONENTS

`[LJ-1.566]` delivered
`injcode-assembled : (a : S) (oa : IsOrd (fst a)) → InjCode (Carve.G a oa) a (Carve.C a oa)`
(`agents/tasks/LJ-1-566/Probe566.agda:492-500`).

| slot | `[LJ-1.566]` | B9 | evidence |
|---|---|---|---|
| `a` | ANY `a` with `IsOrd (fst a)` | `LsetS δ oδ`, and `fst` of it is `Lset δ` | `agents/tasks/LJ-1-561/Probe561.agda:379-381` |
| `b` | `Carve.C a oa`, PRODUCED by the carve out of the rank well-order | `ordS δ oδ`, that is `δ`, GIVEN | `agents/tasks/LJ-1-566/Probe566.agda:132-141`, `:323-324` |

**MISS ONE.** `Lset δ` is a stage of L. It is not an ordinal, and nothing in
the tree gives `IsOrd (Lset δ)`. `Probe572.agda` `p566-frame` ascribes the
delivered signature, so the demand `IsOrd (fst a)` is checked, and
`B9-a-carrier` checks by `refl` that B9's `fst a` is `Lset δ`.

**MISS TWO, AND IT SURVIVES ANY REPAIR OF MISS ONE.** `[LJ-1.566]`'s `b` is the
carve's bounding ordinal. The ascribed signature carries this: **the `b` is an
OUTPUT of the term and never an input to it**, so no instance of it can be
steered to B9's `b`.

**AND THE MISMATCH CANNOT BE PUT TO THE ELABORATOR AT ALL. MEASURED.**
`runs/Frame.agda` takes `IsOrd (fst (LsetS δ oδ))` as a PREMISE and then APPLIES
`injcode-assembled` at B9's `a`. `runs/Frame2.agda` is the same file with those
two applications removed.

| file | interfaces | result |
|---|---|---|
| `runs/Frame.agda` | cold | 1360.52 s, killed, exit 143 (`runs/frame-1.out`) |
| `runs/Frame2.agda` | warm | **1.83 s, exit 0** (`runs/frame2-1.out`) |
| `runs/Frame.agda` | warm | **past 300 s, killed** (`runs/frame-2.out`) |

**THE WARM PAIR IS A CLEAN ATTRIBUTION.** Same interfaces, same file, and only
the two applications differ. **IT WAS NOT A HEAP WALL**: on the cold run RSS was
static at 2,314,080 KB against a `-M8g` cap and CPU time equalled elapsed time,
so the process held one core and allocated nothing. **IT WAS NOT CONTENTION**
either, and the same equality rules that out (`runs/contention-1.out` records
the three other Agda processes on this shared pane).

**SO THE PREMISE IS NOT THE PROBLEM.** `Carve` runs on the ordinal well-order of
the carrier (`agents/tasks/LJ-1-566/Probe566.agda:129-130`), and at a carrier
that is not an ordinal it has nothing to reduce against. **Do not fund a task to
supply `IsOrd (Lset δ)`.**

The brief says: "IF `[LJ-1.566]`'s FRAME IS NOT B9's FRAME, SAY SO AND STOP."
It is not. This is that stop.

### 3. AND THE DEPENDENCY RUNS THE OTHER WAY

This is the reason that would stand even if both premises above were paid.

`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`), and
B9's obligation is `InjL (LsetS δ oδ) (ordS δ oδ)`
(`agents/tasks/LJ-1-561/Probe561.agda:376-378`). `Probe572.agda`
`B9-obligation-unfolds` checks that by `refl`.

**SO AN `InjCode` AT B9's PAIR IS B9's OBLIGATION.** It is not raw material for
`Def`. It is what `Def` buys. The one bridge in the tree between the two runs
FROM a graph L-set TO `Def` (`graph→def`,
`agents/tasks/LJ-1-568/Probe568.agda:368-371`), and the graph L-set is `W`'s
conclusion.

**AND THE OBLIGATION IS ROW 4 ITSELF.** `Probe572.agda` `obligation-pays-B9`
takes the obligation as a hypothesis and returns
`InjL (LsetS δ oδ) (ordS δ oδ)`, through `[LJ-1.568]`'s
`restrict→B9 Def∥ def∥-restricted` (`Probe568.agda:285-291`). `[LJ-1.568]`
stated that at a QUANTIFIED `H` (`no-free-lunch-at-B9`, `Probe568.agda:454-463`).
This row puts it at THIS brief's own hypothesis and at B9's own `g`.

**The brief estimated the obligation at about 40 lines. The obligation is
worth exactly row 4 of the bill, and row 4 is open.**

**CLOSURE NOTE, 2026-08-23.** The rewritten brief of this dispatch orders this
stop re-verified and the row closed on `stop-stated`. Re-verification is in
the section at the top of this file: both load-bearing facts hold at
`src/L/StageCardinal.lagda.md:17-19` and `:566, :562, :283` (used `:288, :291`),
and the salvaged `runs/W3.agda` re-ran green at 1.70 s
(`runs/w3-4.out`). Nothing in `src/` was touched, nothing was committed, and
nothing was pushed. The obligation `b9-g-is-definable` stands open in
`Probe572.agda` exactly as measured: this file, not a term, is what the task
delivers.

## WHAT THE MAP ACTUALLY IS

W3 unfolded B9's `g` and checked every hop by `refl`
(`agents/tasks/LJ-1-572/runs/W3.agda`, exit 0, `runs/w3-2.out`):

- `stage-card-upper` IS `∈-induction step` (`unfold-1`).
- `step`'s body is `limit-step` at the branch family (`unfold-2`).
- `limit-step` counts every earlier stage's formulas into `α` through
  `Bound α oα infα (sq α α∈suc infα)` (`src/L/StageCardinal.lagda.md:283`,
  used at `:287-292`).
- `sq` is a BARE module parameter (`src/L/StageCardinal.lagda.md:17-19`). It
  carries injectivity and nothing else: no formula, no `isL`, no stage, no
  grade (`sq-bare`).

**SO THE OBLIGATION'S TRUTH IS A FUNCTION OF `sq`, AND `sq` IS UNIVERSALLY
QUANTIFIED AT THE MODULE HEADER.** I state the limit of that exactly: **this is
evidence and not a refutation.** I did not prove `Def` false at this `g` in
Agda, and I could not, because a definable `sq` would make it true. What is
measured is that the tree gives `sq` no formula, so the obligation is not
provable from the module's own parameters.

`[LJ-1.568]` had already recorded the same sentence
(`agents/tasks/LJ-1-568/lj-1.568-report.md:132`). My clause takes a
predecessor's hypothesis as the type that predecessor DELIVERED, and that row's
verdict at B9 is **NO**. This task's W3 checks the two hops between
`stage-card-upper` and `sq` that the row asserted.

## WHAT WOULD MAKE THE OBLIGATION TRUE

**NOT A REPAIR OF THIS `g`. A DIFFERENT `g`.** `[LJ-1.568]` left the address
(`Probe568.agda:485-489`), and `B9-any-g` (`Probe568.agda:490-495`) is the row
that consumes it: **B9's obligation names no function**, so any injection at
that pair will do, and the classical route uses the `<ʟ`-least-witness map of a
DEFINABLE well-order, whose graph carries a formula by construction
(`dev/literature/devlin-II5.md:259-270`).

**I DID NOT BUILD IT.** AD12 gives this brief one obligation, and that is a
different one.

## WHAT I DID NOT DO

- I did not attempt rows 1, 2, 3 or 5 of `[LJ-1.564]`'s bill.
- I did not postulate. `Probe572.agda`, `runs/W3.agda`, `runs/Frame.agda` and
  `runs/Frame2.agda` carry no postulate and no hole. `runs/Frame.agda` does not
  typecheck in bounded time and that is its finding, recorded above; the
  obligation's own file, `Probe572.agda`, is GREEN at exit 0
  (`runs/probe-1.out`, `runs/probe-2.out`).
- Nothing landed in `src/`.
- I did not commit and I did not push.
