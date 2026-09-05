# LJ-1.160 report: the 845-line level substrate against `levelIn` and `cover`

tier: opus (version `override`). **No master was changed. One probe was
written and it ran GREEN. No commit, no push.** Every negative is marked
**MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

### 0.1 The one sentence the brief asked for

**The substrate does not discharge `levelIn` or `cover`. It ROUTES AROUND the
wall, and the re-route is MEASURED GREEN at the current route's own two types.**

**This is the brief's second abort criterion. I stop here and I say so first.**

### 0.2 What is measured, in three lines

`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, exit 0, no unsolved meta:

1. **`FOL.Absoluteness.Single` opens at the collapse image `C.πX` in ONE
   line**, because `C.πX-trans` is delivered (`src/V/Collapse.lagda.md:89`) and
   `isTrans` is definitionally `Single`'s third parameter
   (`src/V/Collapse.lagda.md:25-26` against `src/FOL/Absoluteness.lagda.md:57-59`).
2. **The current `levelIn` closes in 6 in-fence lines** from the archive's
   `CrossOut` plus `HasLevels`, at the verbatim type of
   `src/L/BoundedSubset.lagda.md:917`.
3. **The current `cover` closes in 10 in-fence lines** from `CrossOut` plus
   `Covered` plus the delivered `C.πX-intro` (`src/V/Collapse.lagda.md:86`), at
   the verbatim type of `src/L/BoundedSubset.lagda.md:918-919`.

**16 in-fence lines supply BOTH hypotheses from one crossing face.**

### 0.3 The term I did not write, and I did not try

**`π (Lset m') ≡ Lset (π m')` appears NOWHERE in the probe. MEASURED**, by
`grep` over `ProbeLJ1160A.agda`. The probe names `C.π` only as the argument of
`C.πX-intro`, which is delivered.

**The wall is not broken. It is BYPASSED, and the bypass has a price nobody has
paid.** Section 3 names the replacement obligation.

### 0.4 The honest counterweight, and it is the size of the finding

**The archive never supplied `CrossOut`.** Its own mechanism for it rests on a
Δ₀ witness for a level story whose Def-step clause is `⊤̇`
(`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md:200`). **`[LJ-1.11]`
refuted exactly that**: a story with a `⊤̇` step recognizes no level, and its
target is classically FALSE (`dev/PLAN.md:238`).

**So I take the SHAPE and I refuse the claim.** The archive's `Assembly` is
parametric in the formula. The refutation kills the archive's INSTANCE. It does
not touch the derivation.

### 0.5 Why the bypass is not a fantasy

**The current tree already delivers the Levy witness the archive lacked.**
`Σ₁-cert : ∀ {n} (C T B N : Fin n) → Σ₁ (existCertAt C T B N)` at
`src/L/Condensation.lagda.md:269-270`, over about forty delivered `Δ₀-*`
witnesses at `:88-600`. **That is the twelve-row substrate, and it exists
because the Def step does NOT collapse on this route.**

**And the literature says this is Devlin's own chain.** The digest reads the
transfer as "along the collapse to M; 1.9.15 converts M's satisfaction of the
Σ₀ matrix into ambient Φ; (a) turns Φ into `v = L_γ`"
(`dev/literature/devlin-II5.md:102-106`). **Devlin's `M` is the transitive
collapse. He never commutes the collapse with the level construction.**

## 1. WHAT THE SUBSTRATE PROVES, AND WHAT IT ASSUMES

### 1.1 `LevelKit.lagda.md`, 587 in-fence, read WHOLE

It is `module LevelKit (u : V ℓ) (utr : isTransV u)` at `:98`. It has TWO
parameters and no more.

It delivers, for one transitive carrier:

| block | lines | what it is |
|---|---|---|
| four meta-level clauses | `:106`, `:110`, `:114`, `:120` | `pairhood`, `singleValued`, `zeroClause`, `exactDom` |
| the object formulas | `:154` to `:205` | plus `isOrdAt`, the truth clause `Cl = ⊤̇`, the range read `Rg` |
| the two-way decodes | `:241` to `:530` | `pair∈`, four clause decodes, `isOrd`, `exactDom`, `r-ok` |
| the successor atom | `:563` to `:654` | `sucKcov`, `sucAt`, `sucAt-ok`, `succPairAt`, `succPair-ok` |
| `OneWaySucc` | `:662` to `:717` | the successor clause, parametric in its conclusion atom |
| the story assembly | `:749` to `:832` | `StoryClause`, `Conj`, `ConjForm`, `story-ok` |

**What it assumes: a transitive carrier, the pair-atom kit, and the inner
semantics `DefOf u`. Nothing else.** The chapter states it at `:846`: "Nothing
here mentions which tower the carrier belongs to."

**MEASURED and it is the sharpest number in this section: `LevelKit` names
`Lset` ZERO times**, in fence and in prose, and it imports no `L.Rud` module.
Its four `rud` mentions are all prose.

### 1.2 The brief's `:562` entry point, and it is a false friend

**The brief flagged `sucKcov` at `:562` because it "carries a successor atom's
COVERAGE body", and called that "the same word as `cover`".**

**MEASURED FALSE.** `sucKcov k a = (var zero ∈̇ var (suc a)) ∨̇ (var zero ≐ var
(suc a))` at `:563-564`. It says every member of `k` is a member of `a` or is
`a` itself. **That is the third clause of `k = a ∪ {a}`, the set successor.** It
has no relation to `cover`, which is Devlin's second condensation inclusion.

**I report this because a later reader will find the same word and stop there.**

### 1.3 `LevelFormula.lagda.md`, 258 in-fence, read WHOLE

`module LevelAt (α : S) (K : ⟪ Lset α ⟫)` at `:94` is the first instantiation.
It sets `u = Lset α` (`:96`) and `utr = layer-trans (Lset-layer α)` (`:99`).

It adds the carrier-specific half: `isLimit` (`:107`), `limitClause` (`:113`),
`limitForm` (`:182`), the limit decodes (`:217`, `:240`, `:267`, `:315`), the
adequacy `a-ok` (`:391`), the Def-step `collapse` (`:424`) and `read-off`
(`:467`).

**`read-off` is the level-hood adequacy at the Def tower**: a member of the
level lies in the set carved by one object formula exactly when a tower initial
segment approximates the tower and ranges over that member.

**`LevelFormula` names `Lset` 13 times in fence. It is the per-tower half.**

### 1.4 The Def-step clause is where the archive is FALSE

`Cl = ⊤̇` at `LevelKit.lagda.md:200`. `LevelFormula` justifies it at `:424-441`
by `collapse`: at the carrier `Lset α`, every member is definable at a member of
the carrier, so the truth clause is adequate THERE.

**At an arbitrary transitive carrier it is not adequate, and that is
`[LJ-1.11]`'s refutation.** A story whose step clause is `⊤̇` does not pin the
value. So `CrossOut` for the archive's own formula is FALSE.

**I take nothing from the archive that depends on `Cl = ⊤̇`.**

### 1.5 `InitialSegment.lagda.md`, 114 in-fence, the named lines

`:155` is `σ-in`, and `:234` is `face-iff`, the two-way adequacy the consumer
takes away. The chapter says at `:239-245` that the statement layer "provably
depends on nothing in the tower content", and that negative controls were run.

**MEASURED: `InitialSegment` names `Lset` ZERO times and imports no rud
module.** It is the reusable adequacy FRAME.

### 1.6 The archived `Condensation.lagda.md`, the named lines

`:142` opens the level-hood sentence at a transitive set carrier. `:160-187`
declares the whole crossing face:

```agda
  CrossOut : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b
             → fst v ≡ Lset (fst b)
```

`HasLevels φ` at `:173-175`, `Covered φ` at `:177-180`, `SucClosed` at `:182`,
`Condenses` at `:186-187`.

`:208` is `module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ)`. **It is
parametric in the formula.** Inside it:

- `succ-step` at `:210-227`.
- **`level-in` at `:240-247`.** Its type is
  `HasLevels φ → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ Lset δ ∈ˢ M ⟩`.
- `M⊆L` at `:249-257`, from `Covered φ`.

**The whole face plus the assembly is 51 in-fence lines**, measured over
`:160-260` by the ledger's in-fence rule.

`:260-297` is the meaning-preserving transport, and `:791-855` is the Levy
content: `σᴹ`, `levelΔ₀`, `levelΣ₁`, `level-transfer` by `σ₁-up`, and the class
mirror `σL` with `levelΠ₁L`.

**MEASURED: the archived Condensation's ten `π` occurrences are ALL the Π₁
absoluteness names** (`π-Δ₀`, `π-∀`, `π₁-down`, `mapΠ₁`, `levelΠ₁L`). **There is
no Mostowski collapse map anywhere in the archived level substrate or its
crossing.**

## 2. QUESTION 1: DOES IT DISCHARGE `levelIn` OR `cover`?

**NO, and I mark that MEASURED. It DERIVES both from a face it never supplies.**

### 2.1 The shape match, at `file:line`

| current route | archived route |
|---|---|
| `levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩` (`src/L/BoundedSubset.lagda.md:917`) | `level-in : HasLevels φ → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ Lset δ ∈ˢ M ⟩` (`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:240-241`) |
| `cover` (`src/L/BoundedSubset.lagda.md:918-919`) | `Covered φ` plus `CrossOut φ` (`archive/.../L/Condensation.lagda.md:177-180`, `:168-170`) |

**The two types agree up to the carrier name and the argument order.** The
archive states its fact at a transitive `M`. The current route states it at the
collapse image `C.πX`. **`C.πX` IS transitive** (`src/V/Collapse.lagda.md:89`).

### 2.2 The derivation, MEASURED at the current types

`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, module `Reroute`, exit 0.

| obligation | probe lines | body |
|---|---:|---|
| `levelIn` | **6** | one `PT.rec`, one `subst` along `crossOut` |
| `cover` | **10** | one `PT.rec`, one `subst`, `piIntro` at the hull member |
| **both** | **16** | |

The three hypotheses are the module telescope, about 14 lines. **The probe adds
no axiom and no postulate.** `check-unbound-hyp.py` is clean.

**`module AtSite (M : S)` then applies `Reroute` at the REAL site**, with
`C.πX`, `C.π` and `C.πX-intro` supplied by `Collapse M`. **Only the three
crossing facts stay open.** That is the measurement that makes the shape match a
typecheck and not a reading.

### 2.3 What this buys, and what it does not

**It buys a REDUCTION: two hypotheses become one crossing face plus two
inner-story facts.** `Condense`'s telescope today takes `levelIn` and `cover`
separately. Both come from `CrossOut` at the same formula.

**It does not buy a supply.** `CrossOut`, `HasLevels` and `Covered` are all
open. **C-38 as extended binds and I obey it: I report a restatement, not a
discharge.**

## 3. QUESTION 2: DOES IT HOLD THE TERM `[LJ-1.51]` COULD NOT WRITE?

**NO. It holds a route that never needs that term. MEASURED.**

### 3.1 The two routes, side by side

`[LJ-1.51]`'s route (`agents/tasks/archive/LJ-1-51/lj-1.51-report.md:135-153`)
stays in the HULL and then pushes the value through the collapse:

1. Get witnesses `K' v' w' ∈ M` by elementarity of the hull.
2. Show `v' = Lset m'` by the twelve-row agreement re-based at the hull.
3. **Show `π (Lset m') ≡ Lset (π m')`.** This is the wall.
4. `πX-intro v'` finishes.

The archive's route works AFTER the collapse, at the transitive image:

1. The inner world of `C.πX` believes the level formula at an ordinal index.
2. **`σ₁-up` at `C.πX` gives the ambient reading. It needs transitivity only.**
3. The ambient adequacy identifies the value as `Lset` at that index. This is
   `CrossOut`.
4. `level-in` finishes in one `subst`.

**Step 3 of the first route has no counterpart in the second.** The
identification happens INSIDE the transitive image, at the ambient level. No
value is pushed through the collapse.

### 3.2 Why the bypass exists, stated as a mechanism

**The wall is an artifact of WHERE the argument is done, not of the
mathematics.** A hull is not transitive, so a statement proved there must be
carried across the collapse, and carrying `Lset` across is the wall. The
collapse image IS transitive, so Σ₀ absoluteness applies to it directly, and
nothing needs carrying.

**The literature agrees and it is not my inference.**
`dev/literature/devlin-II5.md:102-106` runs the transfer "from L_α to X
(Σ₁-elementarity, downward) and along the collapse to M", and then applies
1.9.15 AT M. **1.9.15 is Σ₀ absoluteness at a transitive carrier, which is our
`abs₀` (`src/FOL/Absoluteness.lagda.md:122`).** The digest's DD4 table classes
that step C3 as **EITHER TOWER** (`:378`).

**No step of Devlin's chain commutes the collapse with the level
construction.** MEASURED, by reading `:95-110` whole.

### 3.3 The replacement obligation, named honestly

**The bypass moves the debt. It does not delete it.** The open terms become:

| term | what it needs | state |
|---|---|---|
| `CrossOut φ` | inner belief at `C.πX` implies `v ≡ Lset b` | **OPEN.** The archive's version is refuted by `[LJ-1.11]` |
| `HasLevels φ` | every ordinal of `C.πX` has a believed value | **OPEN.** Needs the hull's elementarity, transported along the collapse isomorphism |
| `Covered φ` | every member of `C.πX` lies in a believed value | **OPEN.** Same source |

**`HasLevels` and `Covered` need satisfaction to transport along the collapse
isomorphism.** The two directions of that isomorphism are DELIVERED as `iso` at
`src/V/Collapse.lagda.md:203-206`, with `π-inj` and `πX-trans` beside it
(`:214`). **The transport itself is a structural induction on the formula, and
it names no tower. I did not write it and I did not price it. INFERRED that it
is the remaining gap.**

**`[LJ-1.51]` already needed the hull's elementarity for its own step 1**
(`:141-143`, "an unbuilt TV/ElemDown instance"). **So the elementarity term is
common to both routes and it does not separate them.** MEASURED, from the two
reports read side by side.

### 3.4 I stop here, and I say why

**The brief forbids me to break the wall, and it is right to.** Supplying
`CrossOut` at the current tree means writing the adequacy wrapper that turns the
delivered `Σ₁-cert` into a level identification. **That is a chapter and it needs
the owner's funding.**

**I name the next probe with its abort criterion fixed in advance (D-1, C-34).**

> **The obligation**: instantiate `FOL.Absoluteness.Single` at `C.πX` and
> supply `TransferM` for ONE delivered `Σ₁` certificate, namely `Σ₁-cert`
> (`src/L/Condensation.lagda.md:269-270`). Report the in-fence line count for
> that ONE transfer.
>
> - **GO** at or below 60 lines. Then `CrossOut`'s transfer half is cheap, and
>   the open term narrows to the ambient identification alone.
> - **NO-GO** if the certificate's formula does not sit at the image's carrier
>   without re-labelling. Then the relabelling kit
>   (`src/FOL/Manipulation/Bounding.lagda.md:146`) enters the price, and the
>   archive's `Transport` at `:260-297` is the delivered comparable.

## 4. RE-PRICE OF `[LJ-1.146]`'s 1.0k BAND

### 4.1 The refusal I make first, and it is the honest one

**`[LJ-1.146]`'s 1.0k band prices the HULL route. My comparable prices a
DIFFERENT route. So I do NOT re-centre that band, and a report that did would
be comparing two things.**

**What I can give is one measured figure for one term, with its basis (DD8).**

### 4.2 The one term that moves, and it moves hard

`[LJ-1.123]`'s four bands carry two terms that this task measures:

| `[LJ-1.123]` band | its figure | my measurement |
|---|---:|---|
| the three transfer lemmas at the hull | 0.10k to 0.25k | **replaced.** The image route needs no hull transfer |
| the assembly into `Co` | 0.03k to 0.08k | **MEASURED at 0.016k**, probe A, both hypotheses |

**One best-effort figure: the assembly term is about 0.03k in-fence lines, band
0.02k to 0.05k.** **Basis**: 16 measured probe lines for the two derivations,
plus about 14 for the face's three statements, against the archive's own 51
in-fence lines for the same content at `Condensation.lagda.md:160-260`. **Two
independent artifacts, one measured today and one delivered on the retired
route, and they agree inside a factor of three.**

### 4.3 The term that does NOT move, and it is the larger one

**`CrossOut` is unpriced and I give it no number.** `[LJ-1.123]`'s
"certificate truth at the hull ordinals" band, 0.10k to 0.25k, was for a
different statement at a different carrier.

**And the 845 lines are NOT a price anchor for it. This is the finding that
runs against the brief's own framing, so I state it plainly.** `LevelKit` plus
`LevelFormula` build the level-hood adequacy for a story whose Def step is
`⊤̇`. **The current route's counterpart is the twelve-row substrate, which is
already delivered and far larger.** So the 845 measures the WRAPPER, not the
content, and the current tree already paid the content.

**The wrapper is what the current tree lacks.** `InitialSegment`'s 114-line
face is its reusable part, and `[LJ-1.1]:255` marked it ADAPTABLE.

### 4.4 The verdict on the band, in one line

**`[LJ-1.146]`'s band HOLDS at 0.6k to 1.5k for the hull route, and it is now
pricing a route that has a measured alternative.** The alternative's assembly
term is 0.03k. Its certificate term is unpriced. **Nobody should carry 1.0k as
the price of `levelIn` and `cover` without saying which route it prices.**

## 5. WHAT TRANSFERS AND WHAT DOES NOT, ITEM BY ITEM

| item | transfers? | why |
|---|---|---|
| `LevelKit`'s clause kit, `:98-530` | **SHAPE YES, CODE NO** | It is carrier-generic and names no tower. But the current tree's level story is the twelve-row substrate, which is already delivered and is a different object. **MEASURED**: `LevelKit` names `Lset` zero times |
| `LevelKit`'s `Cl = ⊤̇`, `:200` | **NO** | `[LJ-1.11]` refuted it. The Def step does not collapse on this route |
| `LevelKit`'s `sucKcov`, `:563` | **NO** | It is the set successor's coverage clause, not `cover`. Section 1.2 |
| `LevelKit`'s story assembly, `:749-832` | **SHAPE YES** | `Conj`, `ConjForm` and the decode walk are a generic fold over a clause list. Nothing tower-specific. **INFERRED**: I did not port it |
| `LevelFormula`'s limit clause, `:113-183` | **SHAPE YES, INSTANCE NO** | It names `Lset` 13 times in fence. A J tower restates it at its own union step |
| `InitialSegment`'s face, `:155`, `:234` | **YES** | Zero `Lset` mentions, marked ADAPTABLE by `[LJ-1.1]:255`. It is the adequacy frame the current tree lacks |
| `Condensation`'s `CrossOut` face, `:160-187` | **YES, as a STATEMENT** | It is parametric in the formula. The archive's own instance is refuted; the statement is not |
| `Condensation`'s `Assembly`, `:208-257` | **YES, MEASURED** | Probe A rebuilds `level-in` and the `cover` consumer at the current types, exit 0 |
| `Condensation`'s `levelΔ₀`, `:826` | **NO** | It certifies a `⊤̇`-step story. `[LJ-1.2]` measured NO-GO for a Δ₀ witness on the Def tower |
| `Condensation`'s `level-transfer` by `σ₁-up`, `:851` | **MECHANISM YES, WITNESS NO** | `σ₁-up` is delivered at `src/FOL/Absoluteness.lagda.md:182`. The current tree's own witness is `Σ₁-cert` at `src/L/Condensation.lagda.md:269` |
| `Condensation`'s `Transport`, `:260-297` | **SHAPE YES** | The relabelling kit is delivered as `src/FOL/Manipulation/Bounding.lagda.md:146`. **INFERRED**: I did not port it |
| the archived `Condenses` target, `:186` | **NO** | `[LJ-1.11]` ruled it classically FALSE |

**P-l binds twice and I say where.** The archive ran on the rud tower and this
route runs on Def. **Every SHAPE above is a hypothesis until something
elaborates it.** The one row marked MEASURED is the one I elaborated.

## 6. DD4

**Maximize the code the two proofs share, and write it generic.**

### 6.1 The archive's own split, measured

| file | in-fence | `Lset` in fence | class |
|---|---:|---:|---|
| `LevelKit.lagda.md` | 587 | **0** | **SHARED** |
| `InitialSegment.lagda.md` | 114 | **0** | **SHARED** |
| `LevelFormula.lagda.md` | 258 | 13 | **PER-TOWER** |
| total | 959 | | **73 percent shared** |

**MEASURED** by `grep` inside ` ```agda ` fences. No file imports a rud module.

### 6.2 Which correction the archive supports

**The brief asked which of two corrections this rud-tower code supports. It
supports `[LJ-1.151]` and `[LJ-1.153]`, not `[LJ-1.146]` section 6.**

`[LJ-1.146]:475-482` put the certificate and its instantiation on the per-tower
side and called that side the larger half. **The archive built the same content
and put 73 percent of it at a generic transitive carrier.** `[LJ-1.151]:292`
measured 19 of 21 lines tower-free at a different site and reached the same
correction independently.

**Three artifacts now agree**: `[LJ-1.151]`'s probe, `[LJ-1.153]`'s repaired
statements, and 959 lines of delivered archive. **`[LJ-1.146]` marked its split
INFERRED and said no J tower exists to measure against, so this corrects an
inference and contradicts no measurement.**

### 6.3 And the re-route itself is the DD4 move

**The archive's `Assembly` is parametric in the formula.** A J tower supplies a
different `φ` and a different `CrossOut`, and `level-in` and `cover` come out
unchanged. My probe's `Reroute` module takes `Bel : S → S → Type` as a
parameter and never inspects it.

**Of the 16 measured lines, the only tower-specific token is `Lset` in the two
conclusion types.** The bodies are one `PT.rec` and one `subst` each.

**The limit of this claim, stated so nobody over-reads it.** The SUPPLY of
`CrossOut` is per-tower content: it is the level-hood certificate, and
`dev/literature/devlin-II5.md:375` row C1 classes it PER-TOWER. **So the
re-route shares the assembly and not the certificate. INFERRED**, and it agrees
with `[LJ-1.146]`'s direction while correcting its magnitude.

**No stop-line pushed me toward writing fixed. The generic form was the short
form here, exactly as at `[LJ-1.151]`.**

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the substrate discharges `levelIn` | **MEASURED FALSE.** It derives it from an unsupplied face |
| the substrate discharges `cover` | **MEASURED FALSE.** Same |
| the substrate holds `π (Lset m') ≡ Lset (π m')` | **MEASURED FALSE.** Zero collapse maps in the whole substrate |
| the substrate routes around that term | **MEASURED TRUE.** Probe A, exit 0, and no `π` in either derivation |
| `C.πX` is transitive on the current tree | **MEASURED TRUE.** `src/V/Collapse.lagda.md:89` |
| the absoluteness machine opens at `C.πX` | **MEASURED TRUE.** Probe A, `module AtSite` |
| `sucKcov` is related to `cover` | **MEASURED FALSE.** It is the set successor's third clause. Section 1.2 |
| the archive's `CrossOut` instance is usable | **MEASURED FALSE.** Its story's step clause is `⊤̇`, refuted by `[LJ-1.11]` |
| the archive's `Assembly` is usable | **MEASURED TRUE in shape.** Probe A rebuilds it at the current types |
| the 845 lines anchor the certificate price | **MEASURED FALSE.** They price the wrapper. The current tree already paid the content. Section 4.3 |
| the 845 lines anchor the ASSEMBLY price | **MEASURED TRUE.** 51 archived in-fence lines against my 16. Section 4.2 |
| `[LJ-1.146]`'s 1.0k band is wrong | **NOT CLAIMED.** It prices a different route. Section 4.1 |
| the bypass removes all debt | **MEASURED FALSE.** Three facts stay open. Section 3.3 |
| the hull elementarity term separates the two routes | **MEASURED FALSE.** Both need it. Section 3.3 |
| satisfaction transports along the collapse isomorphism | **INFERRED.** `iso` is delivered; the induction is not written |
| `[LJ-1.2]`'s Δ₀ NO-GO kills the bypass | **INFERRED FALSE.** Devlin needs Σ₁ with a Σ₀ matrix, not Δ₀, and `Σ₁-cert` is delivered. `dev/literature/devlin-II5.md:243-246` |
| no supply for `CrossOut` exists | **NOT CLAIMED.** C-36 binds. I did not search for one |
| the archive follows Devlin | **MEASURED TRUE in shape, FALSE in instance.** Section 8 |
| the substrate is rud-specific and transfers nothing | **MEASURED FALSE.** Zero rud imports, zero `Lset` in 701 of its 959 in-fence lines |

## 8. LITERATURE: CONFIRMED, AND THE ARCHIVE FOLLOWS DEVLIN IN SHAPE ONLY

**`[LJ-1.146]` found `levelIn` and `cover` are Devlin's content rather than our
encoding's. I CONFIRM it, and I add where the archive departs.**

**Confirmed.** `dev/literature/devlin-II5.md:102-110` is Devlin's chain (c) to
(q). Its forward half gives `L_γ ∈ M` for every γ < β, and its reverse half
gives `M ⊆ ⋃_{γ<β} L_γ`. **Those are `levelIn` and `cover`.**

**The archive FOLLOWS Devlin on three points.**

1. It states the crossing at a TRANSITIVE carrier, as Devlin does at his
   collapsed `M` (`:104-106`).
2. Its `CrossOut` is Devlin's "(a) turns Φ into `v = L_γ`" (`:96-98`, `:105`).
3. Its transfer is `σ₁-up`, which is Devlin's 1.9.15 at a transitive carrier
   (`:105`). **The DD4 table classes that step EITHER TOWER** (`:378`).

**The archive DEPARTS from Devlin on one point, and it is the fatal one.**
Devlin's Σ₀ matrix is the BOUNDED Def-step description, with every unbounded
quantifier bound by `K(u)` (`:247-252`). **The archive's step clause is `⊤̇`,
which is not a bounded description of the step. It is no description at all.**

**And the digest already answered `[LJ-1.2]`'s NO-GO.** At `:243-246`: "a Δ₀
witness for the satisfaction leaves is NOT what Devlin's argument needs.
Level-hood is used at Σ₁ strength". **So the current tree's `Σ₁-cert` is the
right shape and the archive's `Δ₀` story is not.**

## 9. GATES AND MEASUREMENTS

**The machine was quiet. Load averages 3.05 to 4.06, one user, 2026-08-14
00:21 to 00:22. My figures are LINES and SHAPE, so a busy machine would have
cost me time only.** I say so as the brief instructed.

| run | file | result | notes |
|---|---|---|---|
| probe A | `agents/tasks/LJ-1-160/ProbeLJ1160A.agda` | **exit 0** | no unsolved meta, no hole, no postulate |

`GHCRTS="-A64m -I0 -M8g"`. **One agda process. The cap was never raised. No heap
exhaustion, no kill, no wall.**

| figure | value |
|---|---:|
| `levelIn` derivation | **6** |
| `cover` derivation | **10** |
| **both derivations** | **16** |
| probe file, non-blank non-comment | 61 |
| probe file, non-blank | 110 |
| probe file, all lines | 130 |

**Checkers.**

- `scripts/lint-agda.py --check` on the probe: **exit 0**.
- `scripts/check-unbound-hyp.py` on the probe: **clean (1 file)**.
- `scripts/check-probes.py --check`: **clean**, 1,760 tracked files.
- `scripts/lint-prose.py --check` on this report: run at the close.
- `scripts/ledger.py --brief`: standing **28,940 lines over 85 masters**, from
  HEAD. Thresholds SUSPENDED per the ledger header.
- **No `make check`.** The orchestrator runs it.

**Prohibitions.** No master edited. `src/Everything.lagda.md` not opened. The
three `*Agree` masters not opened. No commit, no push, no `git checkout`,
`stash`, `reset` or `clean`. **My only files are
`agents/tasks/LJ-1-160/lj-1.160-report.md` and
`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`.** The probe is tracked, it sits
beside the report, and it is never deleted.

## 10. THE RULES, ANSWERED

- **DD18.** This task is the archive survey's repair. Section 11 is the return.
- **P-l.** Sections 5 and 4.3. I marked every SHAPE a hypothesis and elaborated
  exactly one. **The comparable is on a different tower and I say so at every
  row.**
- **C-35.** The archive's `Assembly` had a consumer that was deleted by D32, so
  it was never audited. **My probe is its first consumer since, and it found the
  shape sound and the instance refuted.**
- **C-36.** Section 7's last rows. I do not claim no supply for `CrossOut`
  exists. The archive's own instance fails; that is a spelling, not an
  impossibility.
- **C-38 as extended.** Section 2.3. **I report a RESTATEMENT, not a
  discharge.** The three crossing facts have no instance.
- **C-39.** Section 12.
- **C-40.** Section 4.1. I refuse to re-centre a band that prices another
  route, and I name the term my own figure does not cover.
- **C-12.** One agda process, `-M8g`, cap never raised. Load beside the figure.
- **C-22.** This file was a skeleton before I read the archive.
- **C-31, C-32, C-33, C-34, C-37.** Section 3.4 states the next obligation as an
  obligation, with its abort criterion fixed in advance. No cure is left named
  and unpriced.
- **D-1.** The probe is in `agents/tasks/LJ-1-160/`, it ran while my task was
  live, and it is tracked.
- **D-10.** **This law bit.** The recorded residue is `[LJ-1.51]`'s wall. I
  priced its TRUTH before its proof and found it is a truth about ONE supply
  route, not about the statement.
- **D-26.** Section 6.3 uses the digest's per-step carrier column.
- **D-29, D-30.** Section 2.3 reports the reduction from two hypotheses to one
  face and does not bank it as a saving.
- **I-5.** The probe leaves no unsolved meta.
- **DD8.** One best-effort figure per term, each with its basis. Section 4.
- **DD13.** Section 4.3 prices the ideal form first: the wrapper written fresh
  against the delivered `Σ₁-cert`, not the archived 845 lines ported.
- **DD23.** No mathematical prose was written. The probe carries comments only.
- **DD4.** Section 6.

## 11. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md`, 587 in-fence, READ
  WHOLE.** TOOK the module header (`:98`), the four clauses (`:106-123`), the
  object formulas (`:154-205`), the decodes (`:241-530`), the successor atom
  and `sucKcov` (`:563-654`), `OneWaySucc` (`:662-717`), the story assembly
  (`:749-832`), and the recap's tower-free claim (`:846`). **Section 1.2
  refutes the brief's `:562` entry point.**
- **`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`, 258 in-fence,
  READ WHOLE.** TOOK `LevelAt` (`:94-102`), the limit clause (`:107-183`), the
  limit decodes (`:217-363`), the adequacy (`:377-393`), the Def-step
  `collapse` (`:424-441`), and `read-off` (`:467`).
- **`archive/src/2026-08-09-rud-route/L/InitialSegment.lagda.md`**, read
  `:145-165` and `:225-250`. TOOK `σ-in` (`:155`), `face-iff` (`:234`), and the
  content-free claim (`:239-245`).
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`**, read
  `:1-310` and `:700-885`. **TOOK the crossing face (`:163-187`), `Assembly`
  (`:208`), `succ-step` (`:210-227`), `level-in` (`:240-247`), `M⊆L`
  (`:249-257`), `Transport` (`:260-297`), and the Levy content (`:791-855`).**
  **This is the file the finding rests on, and the brief named only four of its
  lines.**
- **`agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:255`**, the ADAPTABLE line the
  brief asked me to find and quote:

  > `archive/rud-route/src/L/LevelKit.lagda.md` (859),
  > `LevelFormula.lagda.md` (492), `InitialSegment.lagda.md` (290),
  > `PairAtoms.lagda.md` (386), `WellOrder/Combinators.lagda.md` (417),
  > `V/Presentation.lagda.md` (42): ADAPTABLE. They are the level-story
  > substrate and carry no rud imports (T257 5.2). In-fence 587, 258, 114,
  > 219, 263, 18.

  **And `:241`, which the brief did not name and which matters more:**

  > `archive/rud-route/src/L/Condensation.lagda.md` (751): ADAPTABLE IN SHAPE
  > ONLY. The delivered core (Believes, CrossOut, HasLevels, Covered,
  > SucClosed, Condenses; succ-step, level-in, M⊆L; amb-agree; σᴹ and σL with
  > level-transfer) is usable. The crossing application was deleted by D32 and
  > never rebuilt.

  **`[LJ-1.1]` named `level-in` explicitly, three phases ago.** MEASURED: the
  recon carried the answer and no later brief cited that row.
- **`agents/tasks/LJ-1-146/lj-1.146-report.md`, READ WHOLE.** TOOK the two
  statements (`:74-95`), the three-term reduction (`:99-112`), the four
  consumer sites (`:114-121`), the wall's location (`:160-184`), the four bands
  (`:229-242`), the instantiation term (`:260-289`), the DD4 split I correct
  (`:449-484`), and the literature reading (`:542-573`).
- **`agents/tasks/LJ-1-151/lj-1.151-report.md`, READ WHOLE.** TOOK the 21-line
  GO (`:11-19`), the separability finding (`:61-70`), the DD4 correction
  (`:288-318`), and the shape split (`:202-260`).
- **`agents/tasks/archive/LJ-1-51/lj-1.51-report.md`**, read `:125-180`. TOOK
  the wall section title and the term the agent could not write (`:135-153`),
  the unbuilt elementarity instance (`:141-143`), and the 200 to 400 line
  contingent price (`:166-168`). **Section 3.1 sets its route beside the
  archive's.**
- `agents/tasks/LJ-1-157/lj-1.157-report.md`: taken through the brief's quote
  at `:30`. **Its M3 finding is correct on the files and wrong on the reason:
  the substrate is a price anchor for the ASSEMBLY, not for the certificate.**
- **`src/L/BoundedSubset.lagda.md`**, read `:880-935` and `:1400-1420`. TOOK
  `HullStage` (`:904-911`), `M` (`:913`), `module C = Collapse M` (`:915`), and
  the `Condense` telescope (`:916-919`). **NOT edited.**
- **`src/V/Collapse.lagda.md`**, read `:1-110` and `:195-230`. **TOOK
  `isTrans` (`:25-26`), `πX` (`:75`), `πX-member` (`:78`), `πX-intro` (`:86`),
  `πX-trans` (`:89`), `iso` (`:203-206`) and `mostowski` (`:214`). These are
  the probe's whole site content.**
- **`src/FOL/Absoluteness.lagda.md`**, read `:55-70`, `:122`, `:182-190`. TOOK
  `module Single`'s telescope, `abs₀`, `σ₁-up` and `π₁-down`.
- **`src/L/Condensation.lagda.md`**, read `:85-290` and `:6990-7030`. TOOK the
  `Δ₀-*` family (`:88-600`), **`Σ₁-cert` (`:269-270`)**, and `LeafAgree`
  (`:7013`). **NOT edited.**
- `src/FOL/Manipulation/Bounding.lagda.md`, read `:120-170`. TOOK `Relabel`
  (`:146`) and `liftFo` (`:162`).
- **`dev/PLAN.md`**: `:236` (DD2, `[LJ-1.2]`'s NO-GO), `:238` (DD5,
  **`[LJ-1.11]`'s refutation**), `:245` (DD18).
- **`dev/LESSONS.md`**: P-l read WHOLE at `:2323-2400`, C-35 at `:3218`, C-36
  at `:3302`, C-38 at `:3445`, C-39 at `:3539`, C-40 at `:3620`, C-12 at
  `:2093`, C-22 at `:2255`, D-1 at `:1038`. D-10, D-26, D-29, D-30, C-31 to
  C-34, C-37, I-5 loaded through `scripts/rules.py --for recon`.
- `archive/dev/`: **NOT read.** The `D` series is superseded by `DD`, and the
  one archived ruling that bears here, D32, is quoted inside the archived
  master itself (`Condensation.lagda.md:857`).

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:95-115`, `:240-262`, `:368-396`.**

- **`:95-110` is Devlin's chain (c) to (q).** TOOK the transfer's route: "from
  L_α to X (Σ₁-elementarity, downward) and along the collapse to M; 1.9.15
  converts M's satisfaction of the Σ₀ matrix into ambient Φ; (a) turns Φ into
  `v = L_γ`". **This is section 3.2's whole evidence that Devlin works at the
  transitive collapse and never commutes it with the level construction.**
- **`:243-256` is the answer to `[LJ-1.12]` and it re-decides `[LJ-1.2]`.** TOOK
  "a Δ₀ witness for the satisfaction leaves is NOT what Devlin's argument
  needs. Level-hood is used at Σ₁ strength". **Section 8 uses it, and it is why
  the archive's Δ₀ story is the wrong shape and the current `Σ₁-cert` is the
  right one.**
- **`:374-382` is the per-step DD4 table.** TOOK row C1 (level-hood formula,
  PER-TOWER), row C3 (Σ₀ absoluteness at transitive carriers, **EITHER
  TOWER**), and row C4 (transfer, EITHER TOWER). **Row C3 is the row the
  re-route stands on.**

**The brief's question, answered directly: `[LJ-1.146]` is CONFIRMED.**
`levelIn` and `cover` are Devlin's content. **The archived substrate follows
Devlin in SHAPE and departs from him at ONE point**: Devlin's Σ₀ matrix is the
bounded Def-step description with the bound `K(u)` inside the carrier, and the
archive's step clause is `⊤̇`. **That single departure is `[LJ-1.11]`'s
refutation, restated from the literature side.**

`_build/literature/dev2.txt`: **NOT opened.** Every citation is through the
digest.

`dev/literature/devlin-errata.md`: **NOT read.** `[LJ-1.136]` measured that the
errata touch no part of II.5, taken through
`agents/tasks/LJ-1-146/lj-1.146-report.md:735-738`.

## 13. C-39: WHAT A PROHIBITION CLOSED

**Two brief lines closed doors, and one of them nearly cost the finding.**

**"Do not try to break the wall."** This is correct and I obeyed it. But the
same sentence, read as a shape rather than a test, forbids the probe that
MEASURES the bypass. **I read it as its test: do not SUPPLY the wall term.** My
probe supplies nothing. It measures that two delivered types follow from a face
that never mentions the wall. **A stricter reading would have returned "845
lines, ADAPTABLE, no measurement", and the phase would still be blocked.**

**"`LevelKit.lagda.md` FIRST, whole", plus a SCOPE that named only four lines of
the archived `Condensation.lagda.md`.** The finding is not in `LevelKit`. **It
is in `Condensation.lagda.md:208-257`, which the brief listed as four line
numbers and none of them the right ones.** `[LJ-1.1]:241` had already named
`level-in` in plain text.

**The lesson for the next brief, offered and not assumed.** The brief's own
entry point, `sucKcov` at `:562`, was a word coincidence. **Section 1.2 measures
it false.** An entry point found by grep is a hypothesis about where the content
is, and it should be written as one.

**No other brief line blocked a route.** The write scope cost nothing. The
one-process rule cost nothing: the machine was quiet and my probe is light.
