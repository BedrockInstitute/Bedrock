# LJ-1.337 report: the successor-or-limit dichotomy, and `sq-below`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## THE ANSWER: DELIVERED, and it reached one step further than the brief asked

**The dichotomy BUILDS: 77 code lines, 1.324 seconds, exit 0.**
`ord-split` at `agents/tasks/LJ-1-337/ProbeLJ1337A.agda:137-180`.

**`sq-below` BUILDS: 90 code lines, 1.711 seconds, exit 0.**
`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:206-210`.

**AND THE CONSUMER TAKES IT, END TO END.** `stage-card-from-band` at
`agents/tasks/LJ-1-337/ProbeLJ1337D.agda:41-46` instantiates the delivered
`L.StageCardinal` with `sq-below α oα lb` and reads `stage-card-upper` out of
it. **One band in, the delivered conclusion out, 1.720 seconds, exit 0.** That
is `[LJ-1.335]` section 4.1's promise, MEASURED.

**BUT THE BRIEF WARNED ABOUT ITS OWN PREMISE, AND THE PREMISE IS FALSE.** The
semantic search found three things `[LJ-1.335]`'s literal searches missed, and
one of them is LIVE IN `src/`. Section 1.

## 1. THE SEMANTIC SEARCH (D-10), AND WHAT IT OVERTURNED

**`[LJ-1.335]:279-286` recorded three literal `grep` filters and called the
piece absent. It also predicted its own failure:「the filter is literal and it
would miss a differently spelled statement」. It did.**

| what `[LJ-1.335]` called absent | what the semantic search found | verdict |
|---|---|---|
| `sucV` injectivity | **`ord-suc-inj : (δ δ' : S) → IsOrd δ → sucV δ ≡ sucV δ' → δ ≡ δ'` at `src/L/Choice/Stage.lagda.md:239`. Top level, exported, not `opaque`, consumed at `src/L/Choice/Faithful.lagda.md:53`** | **FOUND IN `src/`. The negative was FALSE, and I MACHINE-CHECKED the refutation** |
| the propositionality it buys | `isPropPredOf` at `src/L/Choice/Stage.lagda.md:249-252`, the same `Σ≡Prop` and `isProp×` body I wrote | **FOUND IN `src/`** |
| a successor-or-limit dichotomy | `agents/tasks/LJ-1-301/Descent.agda:249-258`, PROVED inline, TRUNCATED, in a `--safe` file on the library path | **FOUND, in a live probe** |
| the same | `ord-case` at `archive/src/2026-08-09-rud-route/L/Rud/OrdArith.lagda.md:240-241`, proved, with `isSucc`, `isLimit` and `sucV-inj-ord` beside it | **FOUND, archived** |
| the same | `Split` at `agents/tasks/LJ-1-332/ProbeLJ1332A.agda:234-236` | **type only.** Its author says at `:211-213` it is a HYPOTHESIS |
| `isProp (Init δ)` | nothing of that type in `src/`, `archive/` or `agents/tasks/` | **VERIFIED ABSENT, MEASURED** |

**WHY THE LITERAL SEARCH MISSED IT.** `[LJ-1.335]:298` ran
`grep -rn "isPropInit\|sucV-inj\|sucV-injective" src/`. **The delivered name is
`ord-suc-inj`. The token order is reversed, so no substring of that pattern can
match it.**

**AND THE PROJECT SPELLS DECIDABILITY AS `A ⊎ (A → ⊥)`, never `Dec`.** So a
`Dec`-shaped search returns nothing here by construction. MEASURED, from
`src/L/Ordinal/Linear.lagda.md:101` and `:167-168`.

**THE MACHINE CHECK OF THE REFUTATION.** `agents/tasks/LJ-1-337/ProbeLJ1337C.agda`
names the two types probe A proves for itself and closes both with the delivered
terms:

```agda
reuse-sucV-inj : (a b : S) → IsOrd a → sucV a ≡ sucV b → a ≡ b
reuse-sucV-inj = ord-suc-inj

reuse-isPropIsSuc : (σ : S) → isProp (Σ[ δ ∈ S ] (IsOrd δ × (sucV δ ≡ σ)))
reuse-isPropIsSuc = isPropPredOf
```

**Exit 0, 0.904 seconds, 0 agda slots before the run.** So probe A's PART 1 and
its propositionality are re-derivations of `src/`.

## 2. WHAT IS STILL MISSING, AND WHY IT IS NOT THE SAME THING

**The three finds are TRUNCATED or ARCHIVED. The consumer needs UNTRUNCATED.**

- **`Descent.agda`'s dichotomy never leaves a truncation.** Its successor
  branch reads `Succ∥ = ∥ Σ[ γ ] (⟨ γ ∈ˢ α ⟩ × (⟨ sucV γ ∈ˢ α ⟩ → ⊥)) ∥₁`
  (`agents/tasks/LJ-1-301/Descent.agda:198-199`) and spends it under `PT.rec`
  into a truncated goal (`:207`). **So it never reads the predecessor as data,
  and that is exactly why it never needed the delivered `ord-suc-inj`.**
  MEASURED, from the types: `sq-descent` returns `∥ sq α ∥₁` (`:261-262`).
- **`[LJ-1.333]` measured that a truncated family does not close the consumer**
  (`agents/tasks/LJ-1-333/lj-1.333-report.md` section 2.3). So `Descent.agda`
  cannot be lifted as it stands.
- **`archive/` is frozen and nothing imports across the boundary.** `ord-case`
  is a shape to copy, never a term to use.

**SO THE TASK WAS REAL, AND IT WAS SMALLER THAN THE BRIEF PRICED.** The new
work is the untruncation, and the untruncation is `isPropIsSuc`, which rests on
injectivity, which is delivered. **CONTROL 2 puts that whole sentence into one
Agda error message.**

## 3. THE DICHOTOMY, BUILT AND PRICED

**`agents/tasks/LJ-1-337/ProbeLJ1337A.agda`, exit 0.**

```agda
Closed : S → Type (ℓ-suc ℓ)
Closed α = (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩

IsSuc : S → Type (ℓ-suc ℓ)
IsSuc α = Σ[ γ ∈ S ] (IsOrd γ × (⟨ γ ∈ˢ α ⟩ × (α ≡ sucV γ)))

Split : S → Type (ℓ-suc ℓ)
Split α = Closed α ⊎ IsSuc α

ord-split : (α : S) → IsOrd α → Split α
```

**`Closed α` IS the third row of the chapter's own `Init`**
(`src/L/Ordinal/SquareLaw.lagda.md:695`) **and the fourth argument of
`[LJ-1.335]`'s `LimitBand`. No adapter is needed at either end.** MEASURED:
`isPropInit` uses `isPropClosed` for that row with no coercion
(`ProbeLJ1337A.agda:195`), and `LimitBand` names `Closed δ` directly
(`ProbeLJ1337B.agda:127`).

**Zero needs no branch: zero is closed under successors vacuously.** So this
dichotomy has TWO branches where the archived `ord-case` has three. **The third
branch buys the consumer nothing, so I did not write it** (C-45).

**`IsSuc` carries the membership row `⟨ γ ∈ˢ α ⟩` on purpose.** A descent
applies its induction hypothesis at members only, so a predecessor without that
row is useless. **CONTROL 3 measures that `[LJ-1.332]`'s row is the wrong one.**

### 3.1 The price, per part, MEASURED

| part | term | code lines |
|---|---|---:|
| 1 | `sucV-inj` | 13 |
| 2 | `IsSuc`, `isPropIsSuc` | 11 |
| 3 | `Closed`, `isPropClosed`, `Split`, `ord-split` | 42 |
| 4 | `isPropInit` | 11 |
| | **the dichotomy, total** | **77** |
| B1 | `Inj`, `comp-inj`, `transport-sq`, `ord-emb`, `sq-suc` | 34 |
| B3, B4 | `SqBelow`, `LimitBand`, `Below`, `step`, `sq-core`, `sq-below` | 56 |
| | **`sq-below`, total** | **90** |
| | **the leg, total** | **167** |

Counted as non-blank non-comment lines, the DD8 caliber.

**AGAINST THE ESTIMATE.** `[LJ-1.335]:304-317` estimated **120 lines for
`sq-below`** on the delivered comparable `Upper`
(`src/L/StageCardinal.lagda.md:498-566`, 59 lines) plus two probe terms at 25
and 32. **MEASURED: `sq-below` is 90. The estimate was 33 percent high.** The
reason is nameable: **`[LJ-1.335]` counted `transport-sq` and `ord-emb` into
`sq-below`, and it also counted `sq-suc`; my PART B1 is those three at 34 lines,
against the 57 the estimate carried for them.**

**AND THE DICHOTOMY'S OWN LINES WERE OUTSIDE THAT 120, correctly.** `[LJ-1.335]`
left them unpriced under P-l because no comparable existed. **They are 77.**

### 3.2 The check cost, MEASURED

**Every run: ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no
heap exhaustion, no wall. Slots counted before every invocation with the
brief's command.**

| run | file | exit | real s | slots before | 1-min load |
|---|---|---:|---:|---:|---:|
| 1 | A, scope error on `⟪_⟫` | 42 | 2.1 | 0 | n/a |
| 2 | A, level error on the absurd motive | 42 | 2.1 | 0 | 20.82 |
| 3 | **A, GREEN** | **0** | 1.4 | 1 | 16.10 |
| 4 | A, **CONTROL 1** | 42 | 1.4 | 0 | n/a |
| 5 | A, **CONTROL 2** | 42 | 2.0 | 0 | n/a |
| 6 | A, **CONTROL 3** | 42 | 2.1 | 0 | n/a |
| 7 | **B, GREEN** | **0** | 2.5 | 0 | 13.80 |
| 8 | **C, GREEN** | **0** | 1.6 | 0 | 16.35 |
| 9 | B, **CONTROL B1** | 42 | 1.8 | 0 | n/a |
| 10 | B, **CONTROL B2** | 42 | 2.4 | 0 | n/a |
| 11 | B, **CONTROL B3** | 42 | 2.5 | 0 | n/a |
| 12 | **D, GREEN** | **0** | 2.5 | 0 | 11.49 |
| 13 | **A, interfaces deleted, GREEN** | **0** | **1.324** | 0 | 15.81 |
| 14 | **B, interfaces deleted, GREEN** | **0** | **1.711** | 0 | 15.81 |
| 15 | **C, interfaces deleted, GREEN** | **0** | **0.904** | 0 | 15.81 |
| 16 | **D, interfaces deleted, GREEN** | **0** | **1.720** | 0 | 15.81 |

**Runs 13 to 16 are the figures to quote.** I deleted the four probe interfaces
under `_build/2.8.0/agda/agents/tasks/LJ-1-337/` and re-ran, so each figure is
the file's own re-check and not a cache hit.

**EVERY FIGURE IS WARM ON `src/`.** Every interface under `src/` was already
built by an earlier task. **No cold cost is measured here, and P-l forbids me
from pricing a landing by analogy with these seconds.** What they do price is
the MARGINAL check cost of the new content, which is what the ledger's
check-cost row moves by: **about 3.0 seconds for the dichotomy plus `sq-below`
together.**

**AND THIS IS THE C-56 RESULT.** `[LJ-1.332]` measured **400 seconds,
interrupted**, for the TRUNCATED assembly of the same four bands
(`agents/tasks/LJ-1-332/lj-1.332-report.md` section 4.1). **The untruncated
assembly is 1.711 seconds.** C-56 says a truncated proof that walls is paying
for its assembly. **MEASURED here at a ratio of more than 200 to 1.**

### 3.3 The one place the delivered term could replace mine

**`ord-suc-inj` makes PART 1 redundant, IF the home can import
`L.Choice.Stage`. It can, and it costs FOUR masters.**

**MEASURED**, by `agents/tasks/LJ-1-337/probe-imports.py`, which runs no Agda:

| question | answer |
|---|---|
| `L.Ordinal.SquareLaw` imports `L.Choice.Stage` | **LEGAL, no cycle** |
| `L.Choice.Stage` imports `L.Ordinal.SquareLaw` | LEGAL too, so neither reaches the other |
| closure of `L.Ordinal.SquareLaw` today | 26 masters |
| closure with the new edge | **30 masters** |
| the four that enter | `L.Choice.Stage`, `L.Ordinal.Stages`, `L.Rank`, `L.Stage` |

**RECOMMENDATION: keep the 13-line local `sucV-inj` and pay ZERO new masters.**
`src/L/Ordinal/SquareLaw.lagda.md:29-31` already imports `∈-irrefl`,
`∈sucV-elim` and `self∈sucV`, which is everything PART 1 uses. **The only
import change is two names widened in existing `using` lists: `isPropIsOrd`
from `L.Constructible` and `setIsSet` from an already-imported cubical module.**

**AND I SAY THE HONEST HALF (C-42): that choice DUPLICATES a delivered term.**
`src/` would then hold `ord-suc-inj` and `sucV-inj` with the same content. This
is the finding `[LJ-1.335]:76-83` made for `ord-emb` and `_↪_`, which already
exist two and three times. **I price no deduplication and I propose none. The
orchestrator decides between 13 duplicated lines and 4 masters.**

## 4. `isProp (Init δ)`: VERIFIED ABSENT, and built

**VERIFIED ABSENT. MEASURED** by semantic search over `src/`, `archive/` and
`agents/tasks/`: no term of that type exists in any of the three.

**Built at `ProbeLJ1337A.agda:192-203`, 11 lines.** Every row was already a
proposition:

- row 1: `isPropIsOrd`, `src/L/Constructible.lagda.md:144`;
- row 2: `⟨ ω ∈ˢ α ⟩` is an hProp by construction;
- row 3: `isPropClosed`, which is `isPropLim` already written at
  `agents/tasks/LJ-1-301/Descent.agda:179-180`;
- row 4: six `isPropΠ` and `Empty.isProp⊥`.

**CONTROL B1 measures that the assembly cannot proceed without it.**

## 5. `sq-below`, AND THE BOUND IT DOES NOT NEED

**`agents/tasks/LJ-1-337/ProbeLJ1337B.agda`, exit 0.** The statements are
`[LJ-1.335]` section 4.1's, unchanged:

```agda
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

LimitBand : Type (ℓ-suc ℓ)
LimitBand = (δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩ → Closed δ → (Init δ → Empty.⊥)
          → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
          → sq δ

sq-below : (α : S) → IsOrd α → LimitBand → SqBelow α
```

**A FINDING `[LJ-1.335]` DID NOT PREDICT: the bound is not used.** The core is

```agda
sq-core : LimitBand → (δ : S) → IsOrd δ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ
```

at `ProbeLJ1337B.agda:203-204`, and it names no `α`. **`sq-below` is `sq-core`
with the ordinality of `δ` read off `mem-ord` at `sucV α`.** So the lemma holds
at EVERY infinite ordinal, and the bound of the delivered parameter costs
nothing and buys nothing here. MEASURED, from the type.

**THE FOUR BRANCHES, and which delivered term serves each:**

| branch | supplier | at |
|---|---|---|
| δ ∈ ω | refuted by the hypothesis | `ProbeLJ1337B.agda:155` |
| δ ≡ ω | `squareω` | `src/L/InjChain.lagda.md:184-185` |
| δ closed and `Init δ` | `via-col-square` | `src/L/Ordinal/SquareLaw.lagda.md:960-961` |
| δ closed and not `Init δ` | **the band. THE ONE OPEN OBLIGATION** | `ProbeLJ1337B.agda:169` |
| δ a successor | `sq-suc` on the induction hypothesis | `ProbeLJ1337B.agda:103-109` |

**THE SUCCESSOR BRANCH HAS A CASE `[LJ-1.332]`'s SHAPE HAS NO ROOM FOR.** The
predecessor may BE ω. `ShiftAbs` (`src/L/Absorption.lagda.md:73-76`) asks for
`γ ∉ ω` and for the numerals inside γ, and BOTH hold at γ ≡ ω. **I read both
off ONE `∈sucV-elim`, at `ProbeLJ1337B.agda:180-196`, with a written type on
the motive (I-5).** CONTROL 3 measures why the other shape fails.

**THE REWRITE THE BRIEF ORDERED IS FREE. MEASURED.** `Inj X Y` is written out
at `ProbeLJ1337B.agda:65-66` in the raw Σ shape of
`src/L/Ordinal/SquareLaw.lagda.md:686-687`. **`ShiftAbs.shift↪` is stated with
`L.Cardinal`'s `_↪_` (`src/L/Absorption.lagda.md:189-190`,
`src/L/Cardinal.lagda.md:47-48`), and `sq-suc` feeds it straight to
`transport-sq`, which asks for `Inj`. The file is green, so the two are
definitionally the same and no mathematics changed.**

### 5.1 The consumer, END TO END (C-40)

**`agents/tasks/LJ-1-337/ProbeLJ1337D.agda:41-46`, exit 0, 1.720 s:**

```agda
stage-card-from-band : (α : S) (oα : IsOrd α) → LimitBand
                     → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
stage-card-from-band α oα lb =
  SC.Upper.stage-card-upper α oα (self∈sucV α)
  where
  module SC = L.StageCardinal {ℓ} lem α oα (sq-below α oα lb)
```

**So the caller supplies ONE BAND and gets the delivered chapter's conclusion.**
`[LJ-1.335]:230-235` said the diff to `src/L/StageCardinal.lagda.md` and
`src/L/BoundedSubset.lagda.md` is EMPTY. **MEASURED: it is. I changed neither
file and the instantiation is green.**

**AND THE OPEN OBLIGATION IS EXACTLY THE ONE `[LJ-1.332]` ISOLATED.**
`LimitBand` is `limit-truncated` (`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`)
with the truncation removed. **CONTROL B3 measures that the remaining distance
is one truncation bar and nothing else.**

## 6. THE NEGATIVE CONTROLS. Every one MEASURES

**Each was applied, run and reverted. They are recorded here because nothing
typechecks these probes once this task closes.** Six controls, six runs.

**CONTROL 1, ON THE ONE HYPOTHESIS OF `sucV-inj`.** Drop `IsOrd a` and try to
kill the two-cycle by irreflexivity alone:

```agda
control1 : (a b : S) → sucV a ≡ sucV b → a ≡ b
control1 a b e = ∈sucV-elim {A = b} {x = a} (isSetS a b)
  (subst (λ w → ⟨ a ∈ˢ w ⟩) e (self∈sucV a))
  (λ a∈b → Empty.rec (∈-irrefl a a∈b)) (λ p → p)
```

Agda named it, 1.4 s, 0 slots before the run:

```
error: [UnequalTerms]
b != a of type (Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
when checking that the expression a∈b has type ⟨ a ∈ˢ a ⟩
```

**So the ordinal hypothesis is load-bearing, and for ONE step: transitivity
turns `a ∈ b` and `b ∈ a` into `a ∈ a`. Irreflexivity alone does not reach.**

**CONTROL 2, ON THE UNTRUNCATION.** Ask for the predecessor out of a truncation
with `refl` for propositionality, which is what a caller without injectivity
would have to write:

```agda
control2 : (α : S) → ∥ IsSuc α ∥₁ → IsSuc α
control2 α = PT.rec (λ x y → refl) (λ s → s)
```

Agda refused, 2.0 s, 0 slots before the run:

```
error: [UnequalTerms]
x != y of type Σ S (λ γ → IsOrd γ × ⟨ γ ∈ˢ α ⟩ × (α ≡ sucV γ))
when checking that the expression refl has type x ≡ y
```

**THAT IS SECTION 2 IN ONE ERROR MESSAGE.** The machine names the two
predecessors it cannot identify. **Identifying them IS `sucV` injectivity, and
that is the exact reason `[LJ-1.301]`'s descent stayed truncated and never
needed the delivered `ord-suc-inj`.**

**CONTROL 3, ON `[LJ-1.332]`'s STATED SHAPE.** Its `Split`
(`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:236`) asks the successor branch for
`⟨ ω ∈ˢ γ ⟩`. Offer it the membership the dichotomy actually delivers:

```agda
control3 : (α : S) → Split α
         → Closed α ⊎ (Σ[ γ ∈ S ] (IsOrd γ × (⟨ ω ∈ˢ γ ⟩ × (α ≡ sucV γ))))
control3 α (inl c) = inl c
control3 α (inr (γ , (oγ , (γ∈α , p)))) = inr (γ , (oγ , (γ∈α , p)))
```

Agda refused, 2.1 s, 0 slots before the run:

```
error: [UnequalTerms]
γ != Cubical.HITs.CumulativeHierarchy.Base.V.sett
     (...SetStructure.X InfinitySet.ωStructure)
     (...SetStructure.ix InfinitySet.ωStructure)
of type Cubical.HITs.CumulativeHierarchy.Base.V ℓ
when checking that the expression γ∈α has type ⟨ ω ∈ˢ γ ⟩
```

**MEASURED: `[LJ-1.332]`'s `Split` is STRICTLY STRONGER than the dichotomy, and
it is FALSE at `α ≡ sucV ω`, where the predecessor IS ω and `⟨ ω ∈ˢ ω ⟩` is
refuted by `∈-irrefl`.** So an assembly written against that shape has a hole at
one ordinal. **My `IsSuc` carries `⟨ γ ∈ˢ α ⟩`, which is true at every
successor, and section 5 reads the `ShiftAbs` hypotheses off one elimination
instead.**

**CONTROL B1, ON `isProp (Init δ)`.** Give `lem` the `Init` decision with `refl`
in place of the propositionality:

```agda
limit closed = decide (lem (Init δ , (λ x y → refl)))
```

Agda refused, 1.8 s, 0 slots before the run, and it printed the whole predicate:

```
error: [UnequalTerms]
x != y of type
Σ (IsOrd δ)
(λ _ → ⟨ ω ∈ˢ δ ⟩ ×
   ((γ : S) → ⟨ γ ∈ˢ δ ⟩ → ⟨ sucV γ ∈ˢ δ ⟩) ×
   ((β : S) → IsOrd β → ⟨ β ∈ˢ δ ⟩ → ⟨ ω ∈ˢ β ⟩ →
    (f : ⟪ δ ⟫ → ⟪ β ⟫ × ⟪ β ⟫) →
    ((m n : ⟪ δ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥))
when checking that the expression refl has type x ≡ y
```

**So `isProp (Init δ)` is not a convenience. Without it the initial band cannot
be decided at all, and the machine names all four rows it must cover.**

**CONTROL B2, ON THE ONE OPEN BAND.** Drop the band and try the delivered
collapse at a non-initial limit:

```agda
decide (inr ni) = via-col-square δ ni
```

Agda refused, 2.4 s, 0 slots before the run:

```
error: [UnequalTerms]
(Init δ → Empty.⊥) !=< (Σ (IsOrd δ) (λ _ → ...four rows...))
when checking that the expression ni has type Init δ
```

**MEASURED: the ONLY branch the delivered chapter cannot serve is the
non-initial limit, and the gap is exactly one negation.** Every other branch of
section 5 closes on a delivered term.

**CONTROL B3, ON THE TRUNCATION, AT MY OWN SITE (P-l).** `[LJ-1.332]`'s
`limit-truncated` returns `∥ sq δ ∥₁`. Offer it where `LimitBand` takes `sq δ`:

```agda
controlB3 : ((δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩ → Closed δ → (Init δ → Empty.⊥)
           → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
           → ∥ sq δ ∥₁)
          → LimitBand
controlB3 t = t
```

Agda refused, 2.5 s, 0 slots before the run:

```
error: [UnequalTerms]
∥ sq δ ∥₁ !=<
Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
(λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)
```

**THAT IS THE WHOLE REMAINING DISTANCE OF THIS LEG, IN ONE ERROR MESSAGE.** The
dichotomy, `sq-below` and the consumer are done. **One truncation bar at one
band is what is left.**

## 7. LEM: what the dichotomy needs, in one line

**It needs the excluded middle TWICE, and no choice.** Once to decide
`Closed α`, once to turn the failure of `Closed α` into a mere witness. **The
site carries it:** `lem` is already the module parameter of
`src/L/Ordinal/SquareLaw.lagda.md:26`, of `src/L/Ordinal/Linear.lagda.md:39` and
of `src/L/Choice/Stage.lagda.md:42`.

**A constructive proof is impossible, and the reason is one line the chapter
already wrote:** the dichotomy decides a Π-statement over the whole carrier, and
`src/L/Ordinal/Linear.lagda.md:11-16` records the same argument for
trichotomy,「the statement implies the excluded middle」. **Nothing here is
stronger than what the chapter already pays.**

## 8. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's axis is AC against GCH, fixed at
`scripts/measure/ledger.py:50`.

**MY AXIS: is the dichotomy TOWER-BLIND, and does its home make that true?**

**Answer: the dichotomy is tower-blind and its home keeps it so. The assembly
is NOT, and I say which half is which.**

- **`ord-split`, `sucV-inj`, `IsSuc`, `Closed`, `Split`: pure ordinal
  arithmetic.** Their imports are `V.Hierarchy`, `V.Model`, `L.Constructible`
  for `IsOrd`, `L.Ordinal` and `L.Ordinal.Linear`. **They name no `Lset`, no
  `Formula`, no `⊨` and no tower.** MEASURED, from
  `ProbeLJ1337A.agda:31-37`. **So they should be written once and inherited by
  both ends, and a home in `L.Ordinal.SquareLaw` costs ZERO new import edges.**
- **`isPropInit` is NOT tower-blind in the same way.** It reads `Init`, which
  is this chapter's own predicate. **Its home is `L.Ordinal.SquareLaw` by P-k,
  beside `Init` at `:692-698`, and nowhere else.**
- **`sq-below` is not tower-blind at all.** It reads `ShiftAbs`
  (`L.Absorption`), which is a chapter about elements of L. **MEASURED, by
  `probe-imports.py`: `L.Ordinal.SquareLaw` importing `L.Absorption` or
  `L.InjChain` is a CYCLE, both ways.** So `[LJ-1.335]` section 1.3 stands: a
  new master, or `L.Absorption` itself.

**WHICH CLOSURE PAYS.** `[LJ-1.335]` section 2 measured that
`L.Ordinal.SquareLaw` is in the GCH closure and NOT the AC one, so the
dichotomy landed there is **GCH-only today**. **I re-verified the graph half:
`L.Ordinal.SquareLaw` closes over 26 masters, and adding the dichotomy adds
none.** I did NOT re-run `ledger.py`, so I quote none of its line figures as
mine.

**AND THE HONEST HALF, which the axis makes visible.** A dichotomy this generic
sitting inside a chapter about the square law is a placement of convenience.
**`ord-suc-inj` in `src/L/Choice/Stage.lagda.md` is the same problem already
landed: a general ordinal fact inside a chapter about definition stages.** The
generic home for both is `L.Ordinal` or `L.Ordinal.Linear`. **I price no such
move and I propose none: `[LJ-1.335]` settled placement and the brief forbids
re-opening it. I record the observation for whoever prices the ordinal
chapters.**

## 9. WHAT I DID NOT SETTLE

I name these rather than guess.

1. **The cold cost.** Every second here is warm on `src/`. **I measured no cold
   check of any master, and P-l forbids pricing a landing from these figures.**
2. **The untruncation of the limit band.** It is untouched. `LimitBand` is a
   hypothesis in my files, exactly as `[LJ-1.332]` left it. **CONTROL B3
   measures the distance and nothing here shortens it.**
3. **Whether `ord-suc-inj` and `sucV-inj` should be deduplicated**, and whether
   the ordinal facts scattered across `L.Choice.Stage` and `L.Ordinal.SquareLaw`
   belong in `L.Ordinal`. **Observed, not priced.**
4. **The sweep (C-42).** I searched for the dichotomy, for `sucV` injectivity
   and for `isProp (Init δ)`. **I did not sweep `src/` for other terms
   `[LJ-1.335]`'s literal filters may have missed, and I claim no count.** The
   two false negatives I found were both in `src/L/Choice/Stage.lagda.md`, which
   suggests that chapter is worth one sweep.
5. **Whether the archived `ord-case` shape is better than mine.** It has three
   branches and an `hProp`-valued `isSucc`. **I did not port it and I did not
   compare line counts.**
6. **`L.BoundedSubset` still has no consumer in `src/`.** `[LJ-1.335]` section 6
   states the DD13 question. **My work changes nothing about it, and `sq-below`
   supplies a chapter that nothing reads** (C-45).

## 10. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-335/lj-1.335-report.md`, READ WHOLE.** Line read
  `:297-299`:「Two smaller pieces are also absent. MEASURED, by
  `grep -rn "isPropInit\|sucV-inj\|sucV-injective" src/`, which returns
  nothing」. **TOOK: the target, and the filter that produced it. REFUTED: the
  filter cannot match `ord-suc-inj`, and probe C closes the type with the
  delivered term.** The rest of the report I took whole: the homes, the
  statements of `SqBelow` and `LimitBand`, and the estimate I measured against.
- **`agents/tasks/LJ-1-330/lj-1.330-report.md`, READ.** Line read `:32-35`:
  「The repair exists and the brief did not name it. `squareω : sq ω`,
  `src/L/InjChain.lagda.md:184-185`, is the canonical element at ω」. **TOOK:
  the ω base of my assembly**, at `ProbeLJ1337B.agda:156`. I also took `sq-suc`
  from `ProbeLJ1330A.agda:120-127`, restated on `Inj`.
- **`agents/tasks/LJ-1-332/lj-1.332-report.md`, READ.** Line read `:383-385`:
  「The successor-or-limit dichotomy. `Split` at `ProbeLJ1332A.agda:234-236` is
  a HYPOTHESIS in my file, not a theorem」. **TOOK: the target. CORRECTED: its
  stated `Split` is false at `sucV ω`, and CONTROL 3 measures it.** I also took
  the 400-second wall figure as the C-56 comparison in section 3.2, marked as
  theirs.
- **`agents/tasks/LJ-1-301/Descent.agda`, READ `:140-271`.** Line read
  `:250-258`:「`successor (inr ¬s) = Empty.rec (¬lim lim)`」. **TOOK: the proof
  that the split is exhaustive, and the `Lift`ed absurd motive at `:230-238`
  which my `two-cycle` copies. WHAT DID NOT TRANSFER: its whole descent is
  TRUNCATED, so it never reads a predecessor and never needed injectivity.**
- **`archive/src/2026-08-09-rud-route/L/Rud/OrdArith.lagda.md`, READ
  `:68-80` and `:230-251`, SHAPE ONLY.** Line read `:240-241`:
  「`ord-case : (α : S) → IsOrd α → (α ≡ ∅) ⊎ (⟨ isSucc α ⟩ ⊎ ⟨ isLimit α ⟩)`」.
  **TOOK, SHAPE ONLY: that the classification is two `lem` decisions and that
  the successor case must carry the predecessor's ordinality. WHAT WOULD NOT
  TRANSFER: it is a THREE-way split with an `hProp`-valued `isSucc`, and my
  consumer needs neither the zero branch nor the `hProp` packaging.** Nothing
  imports across the archive boundary and I imported nothing.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:60` (L3.32-T25):「Bridge's successor hypothesis, gated | SPLIT」. **TOOK,
  SHAPE ONLY: the retired route also gated a successor hypothesis and the
  dispatch came back SPLIT. WHAT WOULD NOT TRANSFER:** that route's modules are
  under `archive/`, its report lives in `_build/`, and no figure of it is
  readable today. I quote none.

## 11. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`, READ, and it BEARS.** Line
  read `:291-292`:「**Is `A` a proposition?** Then unique choice applies (HoTT
  Book Corollary 3.9.2), and the truncation was never needed」. **TOOK: this is
  step 2 of the digest's own checklist, and it is exactly what `isPropIsSuc`
  buys.** The dichotomy's mere witness becomes data because the target is a
  proposition, not because any choice principle was added. **So this leg spends
  NO step 3 (`rec→Set`, `2-Constant`) and NO step 4 (`leastOf`).** The limit
  band still owes step 3 or step 4, and this task did not touch it.
- **NOT READ, and WHY NOT: `dev/literature/devlin-II5.md`.** It is the
  definable-hull and condensation material. **A successor-or-limit dichotomy is
  textbook ordinal arithmetic that every source uses without comment, and the
  interesting question was CONSTRUCTIVE, which section 7 answers from the
  tree's own chapter and not from a source.**
- **NOT READ, and WHY NOT: the remaining digests under `dev/literature/`.**
  None of them bears on deciding whether one ordinal is a successor.

## 12. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-337/` only.** Six files: this report, four probes
  and `probe-imports.py`. **Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.**
- **I read the sibling probes and reports and changed no line of them.** I
  re-ran none of them.
- **LAND NOTHING. Nothing is landed.** `src/Everything.lagda.md` untouched.
- **C-12: slots counted before EVERY invocation** with the brief's command,
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **ONE agda process.
  `GHCRTS="-A64m -I0 -M8g"` on every run. Cap never raised. No heap exhaustion.
  No invocation exceeded 3 seconds, so there was no wall and no bisection.**
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`. I ran `git` not at all.
- `.venv/bin/python scripts/gate/lint-agda.py --check` on all four probes: exit
  0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this report: exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: clean, 3,175 tracked files,
  no probe outside `agents/tasks/`.
- `.venv/bin/python scripts/dispatch/rules.py --for build`: run, every statement
  read. I opened the full `dev/LESSONS.md` entries for the laws I acted on.
- **MEASURED: no em dash in any file I wrote.** A `grep -c` for the character
  returns 0 on all six.
- **`_build/`:** I deleted only my own four `.agdai` files and re-created them.
  The tree `_build/2.8.0/**` is declared at `dev/build-manifest.toml:106`.

## 13. THE RULES THIS TASK ANSWERS

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  **I ran the semantic search FIRST, and it overturned two of the three
  negatives the brief rested on.** Section 1.
- **C-44. The brief warned about its own premise.** **The premise「the dichotomy
  is absent」is HALF FALSE: the truncated dichotomy is proved in a live probe
  and `sucV` injectivity is live in `src/`.** What was genuinely absent is the
  untruncated form and `isProp (Init δ)`.
- **C-56. A truncated proof that walls is paying for its assembly. Write the
  untruncated control first.** **I wrote the untruncated one only. MEASURED:
  1.711 s against `[LJ-1.332]`'s 400 s interrupted for the truncated assembly
  of the same four bands.**
- **P-l. A measured cure does not transfer by analogy.** Every second here is
  mine, at my site. **The 400 s is marked as `[LJ-1.332]`'s, and the cold cost
  is marked unmeasured.**
- **C-40. Verify the CONSUMERS of a changed file, never the file alone.**
  **Probe D instantiates the delivered consumer and reads its conclusion.** A
  green `sq-below` alone would not have proved the narrowing.
- **C-42. A refutation measures the site it names.** Section 9 item 4 says which
  sweep I did and which I did not.
- **C-45. `exit 0` is not a supply.** Section 9 item 6: the chapter this serves
  still has no consumer.
- **I-5. Written types on every eliminated branch.** `isPropGate` and the
  `Gate` motive at `ProbeLJ1337B.agda:180-196`, and the `Lift`ed motive at
  `ProbeLJ1337A.agda:167-172`.
- **D-1. The abort criterion was fixed before the run**, and section 14 answers
  it row by row.

## 14. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **THE DICHOTOMY IS DELIVERED SOMEWHERE. Say where** | **PARTLY TAKEN.** Truncated and proved at `agents/tasks/LJ-1-301/Descent.agda:249-258`; archived and proved at `archive/src/2026-08-09-rud-route/L/Rud/OrdArith.lagda.md:240-241`. **`sucV` injectivity is LIVE at `src/L/Choice/Stage.lagda.md:239`.** The UNTRUNCATED dichotomy as a named lemma is absent, MEASURED, and I built it |
| **IT BUILDS. Report its lines and seconds** | **TAKEN. 77 lines, 1.324 s, exit 0** |
| **IT NEEDS CLASSICAL LOGIC** | **TAKEN. Two `lem` uses, no choice. The site carries `lem` already.** Section 7 |
| **IT IS EXPENSIVE** | **NOT TAKEN.** 1.324 s for the dichotomy, 1.711 s for `sq-below`, 1.720 s for the consumer instantiation |
| **A WALL** | **NOT TAKEN.** No invocation exceeded 3 seconds. No bisection was needed |
