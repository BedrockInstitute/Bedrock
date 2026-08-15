# LJ-1.332 report: the limit band, the last gap in `sq`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: ONE-TRUNCATION

**The limit band's law is TRUE and PROVABLE from the descent's own induction
hypothesis. It is provable TRUNCATED. The untruncation is the only thing
missing, and no second obstruction sits behind it.**

`limit-truncated`, `agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`, green,
2 seconds, 0 agda slots counted before the run.

```agda
limit-truncated : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
                → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
                → (Init α → Empty.⊥)
                → IH α → ∥ sq α ∥₁
```

**And the brief's lead is DEAD, but NOT by `[LJ-1.324]`'s killer.** Section 1
says exactly why, and a one-line term states the new killer.

**The truncation is NOT `κ-inj`. The brief's third abort row names the wrong
supplier.** `src/L/Cardinal.lagda.md:133-134` is one truncated supplier. The
limit band has a nearer one, and it is `Init`'s own fourth row. Section 3.

## 1. DOES `[LJ-1.324]`'s KILLER APPLY AT THIS PAIR? NO, MEASURED

**`[LJ-1.324]`'s killer was the MOTIVE'S INDEX COUNT.** `Upper.P` has one index
and both carriers move with it (`src/L/StageCardinal.lagda.md:530-532`).
`CanonInj` needs two, `α` and `m`, and it runs big into small
(`agents/tasks/LJ-1-324/lj-1.324-report.md:113-131`).

**AT THIS PAIR THE MOTIVE HAS ONE INDEX. MEASURED, from the definition:**

```agda
sq : S → Type ℓ
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
         ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)
```

`src/L/Ordinal/SquareLaw.lagda.md:685-687`. Source `⟪ α ⟫ × ⟪ α ⟫`, target
`⟪ α ⟫`, ONE index, and both carriers move together. **That is the same shape as
`Upper.P` and the opposite of `CanonInj`.** So `[LJ-1.324]`'s refutation says
nothing here, and C-42 is satisfied: it measured its own site.

**THE LEAD DIES OF A DIFFERENT DEFECT, AND IT IS CHEAPER. MEASURED BY A TERM.**

`L.StageCardinal` takes the square law at every bounded infinite δ as a MODULE
PARAMETER, `src/L/StageCardinal.lagda.md:17-19`. `LimitStep` spends it at
`:283`, as `module B = Bound α oα infα (sq α α∈suc infα)`, at the SAME α as the
site.

I checked that the parameter is what I say it is, by machine and not by reading
the telescope. `ProbeLJ1332B.agda:37-48`:

```agda
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

stage-card-at : (α : S) (oα : IsOrd α) (h : SqBelow α)
              → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
stage-card-at α oα h = SC.Upper.stage-card-upper α
  where
  module SC = L.StageCardinal {ℓ} lem α oα h
```

Green, exit 0, 3 seconds. **So `SqBelow α` IS the only way to name
`stage-card-upper` with `α` as its own bound.**

**And `SqBelow α` already contains the goal.** `ProbeLJ1332A.agda:79-81`:

```agda
lead-hypothesis-is-goal : (α : S) → SqBelow α
                        → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → sq α
lead-hypothesis-is-goal α h = h α (self∈sucV α)
```

**Green. This is `[LJ-1.324]`'s `missing-is-goal` in a new mechanism: the lead's
hypothesis is the goal, so no work moves.** `stage-card-upper` is a CONSUMER of
`sq` at the site, so it cannot supply `sq` at the site.

**I MEASURED THE STRONGEST FORM OF THE LEAD AND NOT A WEAK ONE.**
`stage-card-upper` outputs `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, which is not `sq α`. The route
that would close the difference is an injection of the index square into the
stage, and I wrote it: `lset-route`, `ProbeLJ1332A.agda:87-90`, green.

```agda
lset-route : (α : S) → (⟪ α ⟫ × ⟪ α ⟫) ↪ ⟪ Lset α ⟫
           → ⟪ Lset α ⟫ ↪ ⟪ α ⟫ → sq α
```

**So even the best version of the lead reduces to `stage-card-at`, and
`stage-card-at` demands `sq α`. The lead is dead at its strongest point, not at
a weak one (C-36).**

**WHAT IS NOT REFUTED, and I say it plainly (C-36, C-42).** The GENERIC engine
`[LJ-1.324]` extracted (`agents/tasks/LJ-1-324/Graft.agda:86-129`, 39 lines,
tower-blind) carries NO `sq`. Nothing here refutes the engine. What is refuted
is the DELIVERED `stage-card-upper` as a supplier of `sq`, at every α.

## 2. IS THE LIMIT BAND NON-EMPTY? YES

**The consumer quantifies over it with no restriction. MEASURED.**
`BoundedSubsetAt`'s `sq` parameter, `src/L/BoundedSubset.lagda.md:1388-1391`:

```agda
    (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
        → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
```

**There is no `Init δ`, no successor hypothesis and no limit hypothesis.** The
consumer demands the law at every infinite δ at or below α. `[LJ-1.314]`
measured the same for the consumers below the site.

**The tree already NAMES a candidate site. MEASURED, by reading the chapter.**
`+ω` at `src/L/Ordinal/StageArith.lagda.md:41-42`, `+ω-ord` at `:76-77`,
`+ω-mem` at `:62-63` and `+ω-iter` at `:68-69`. **So `+ω ω` is an ordinal, ω is
a member of it, and every finite iterate `sucIter n ω` is a member of it.**

**INFERRED, and I mark it INFERRED, twice:** that `+ω ω` is a LIMIT and that it
fails `Init`. **I built neither.** The first needs successor monotonicity on
ordinals; the second needs the canonical decomposition of `ω + ω`, which is
ordinal subtraction. **D-1 says a probe buys the cheapest decisive answer, and
the consumer's unrestricted quantification is already decisive.**

**So the fourth abort row, EMPTY-BAND, does NOT fire.**

## 3. THE TERM, AND WHAT THE WALL ACTUALLY IS

### 3.1 The band reduces to ONE untruncated injection

`member-inj→sq`, `ProbeLJ1332A.agda:145-148`, green:

```agda
member-inj→sq : (α β : S) → IsOrd α → ⟨ β ∈ˢ α ⟩
              → ⟪ α ⟫ ↪ ⟪ β ⟫ → sq β → sq α
```

It is `[LJ-1.330]`'s `transport-sq` composed with the free back leg `ord-emb`.
**The back leg is free at every ordinal, so the whole obligation at a limit is
ONE untruncated injection of the site's index into a member's index**, and the
member's own law comes from the descent (`member-inj→sq-ih`, `:152-155`).

### 3.2 The band's law is TRUE, and the truncation is the ONLY gap

**`Init`'s fourth row is the nearest supplier, and the brief named a further
one.** `src/L/Ordinal/SquareLaw.lagda.md:697-699`:

```agda
       × ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
```

At a non-initial limit the first three rows hold, so **the fourth row FAILS**.
A failed row is a mere witness under LEM, with no choice:

```agda
notRow4→merely : (α : S) → (Row4 α → Empty.⊥) → ∥ Witness α ∥₁
```

`ProbeLJ1332A.agda:180-186`, green. `Witness α` holds an infinite member β and
an injection `⟪ α ⟫ ↪ (⟪ β ⟫ × ⟪ β ⟫)`, `:175-178`. The member's own law
collapses the square, `witness→sq` at `:188-194`, and `limit-truncated` at
`:196-204` assembles the two.

**THE MEASUREMENT: the limit band's mathematics is finished. Its statement is
`∥ sq α ∥₁` and not `sq α`.**

**AND THE TRUNCATED LAW IS NEW.** MEASURED, and I name the search and its
filter: `grep -rn "∥ sq" src/` returns TWO lines,
`src/L/Ordinal/SquareLaw.lagda.md:956` (`Initial.truncated`) and `:963`
(`via-col-truncated`). **Both sit under `Init`.** So nothing in `src/` gives
`∥ sq α ∥₁` outside `Init`. **The filter is literal and it would miss a
differently spelled statement**, so read this as「the obvious spelling has two
hits」and not as a proof of absence.

### 3.3 So the wall is not where the brief put it

The brief's third row reads「IT NEEDS THE TRUNCATED `κ-inj` AND NOTHING ELSE」.

**MEASURED: the limit band never reaches `src/L/Cardinal.lagda.md:133-134`.** My
term imports no `LeastCardInjL` and names no least cardinal. The truncation it
meets is `Init`'s fourth row, which is nearer and cheaper: it asks for ONE
member, not for the LEAST one.

**Both are the same shape.** `κ-inj` gives `∥ ⟪ α ⟫ ↪ ⟪ κ ⟫ ∥₁` at the least
equinumerous κ. `notRow4→merely` gives `∥ ⟪ α ⟫ ↪ ⟪ β ⟫ × ⟪ β ⟫ ∥₁` at some
member β. **The second is weaker and it is enough**, because the member's own
square law collapses the product. **A cure that untruncates either one closes
the band.**

### 3.4 Which live candidate the question returns to

**`[LJ-1.321]` section 8 item 4 is now RETIRED by section 1 of this report**, as
item 3 was retired by `[LJ-1.330]`.

**Item 1 and item 2 remain, and item 2 is the one this measurement points at.**
`agents/tasks/LJ-1-321/lj-1.321-report.md`, section 8:

- **Item 2, a weakly constant endomap of `sq α`.** Kraus and others prove this
  is EXACTLY equivalent to the untruncation. **My result makes item 2 the whole
  remaining question at the limit band**, because everything else is now a
  green term.
- **Item 1, the pointwise-least map.** Untouched by me and not refuted by
  anything here.

## 4. LINES, SECONDS AND LOAD

Two files, both in `agents/tasks/LJ-1-332/`.

| file | total | non-blank | code |
|---|---:|---:|---:|
| `ProbeLJ1332A.agda` | 340 | 303 | 143 |
| `ProbeLJ1332B.agda` | 75 | 66 | 26 |

**The new mathematics is 32 code lines**: `Row4`, `Witness`, `notRow4→merely`,
`witness→sq` and `limit-truncated` are 26, and `member-inj→sq` with
`member-inj→sq-ih` are 6. `transport-sq`, `ord-emb`, `sq-suc` and `sq-suc-inf`
are re-derived from `[LJ-1.330]` and are not new (C-44).

Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. `GHCRTS="-A64m -I0
-M8g"` on every run. ONE process. Cap never raised. No heap exhaustion.

| run | what | exit | real s | agda slots before | 1-minute load |
|---|---|---:|---:|---:|---:|
| 1 | A, full, one arity error at `stage-card-at` | error | 2 | 1 | 9.93 |
| 2 | A, full, INTERRUPTED | none | **600** | 1 | n/a |
| 3 | A without `L.StageCardinal`, INTERRUPTED | none | **600** | 0 | n/a |
| 4 | A, PARTs 1 to 3 | **0** | 3 | 0 | n/a |
| 5 | A, PARTs 1 to 4 | **0** | 2 | 0 | n/a |
| 6 | A, plus `sq-suc` and `sq-suc-inf` | **0** | 2 | 0 | n/a |
| 7 | A, plus `Split` and `IHT` | **0** | 2 | 0 | n/a |
| 8 | A, plus `bands-suc` | **0** | 2 | 0 | n/a |
| 9 | A, plus `noninit-branch`, INTERRUPTED | none | **400** | 0 | n/a |
| 10 | A, `noninit-branch` cut, GREEN | **0** | 2 | 0 | 13.51 |
| 11 | **B, GREEN** | **0** | 3 | 0 | 11.97 |
| 12 | A, **NEGATIVE CONTROL 1** | error | 2 | 0 | 11.51 |
| 13 | A, **NEGATIVE CONTROL 2** | error | 3 | 0 | 10.05 |
| 14 | B, **NEGATIVE CONTROL 3** | error | 2 | 0 | 11.37 |
| 15 | A, **NEGATIVE CONTROL 4** | error | 2 | 0 | 10.48 |
| 16, 17 | controls recorded in comments, A and B GREEN | **0** | 5 both | 0 | 16.11 |
| 18 | A, unused imports removed, GREEN | **0** | 2 | 0 | 9.83 |

**Every figure is WARM.** Every interface under `src/` was already built. **No
cold cost is measured here** and P-l forbids me from pricing a landing by
analogy with these seconds.

### 4.1 The wall, bisected

**Run 2 exceeded 600 seconds. I interrupted it and bisected, as the brief
orders.** Runs 3 to 9 are the bisection. **The wall is ONE definition**,
`noninit-branch`, recorded in a comment at `ProbeLJ1332A.agda:253-279` because
nothing typechecks this file after the task closes.

```agda
noninit-branch : (α : S) → IsOrd α → IHT α → ∥ Witness α ∥₁ → ∥ sq α ∥₁
noninit-branch α oα iht = PT.rec squash₁ step
  where
  step : Witness α → ∥ sq α ∥₁
  step (β , oβ , β∈α , ω∈β , sqr) =
    PT.map (λ sqβ → member-inj→sq α β oα β∈α (comp↪ sqr sqβ) sqβ)
      (iht β β∈α oβ ω∈β)
```

**MEASURED: 400 seconds, interrupted, against 2 seconds for the same
mathematics under the UNTRUNCATED hypothesis** (`witness→sq`, run 5). The two
differ in one thing: `noninit-branch` nests a `PT.map` inside a `PT.rec`, so the
descent carries `∥ sq d ∥₁` instead of `sq d`.

**So the cost sits in the ASSEMBLY, never in the mathematics.** I did not cure
it and I do not price the cure. **This is a new measurement and I offer it as a
candidate law only, with its measurement, for the orchestrator to number:
nesting two propositional-truncation eliminations over a Σ-type whose fields
mention the ambient `S` walls, while the same terms under an untruncated
hypothesis check in 2 seconds.**

**I did not run `make check`.** I never raised the cap. Run 2 and run 3 hit my
own 600-second harness limit, not the brief's 30-minute line. Run 9 hit 400
seconds. **I report them as INTERRUPTED and not as heap walls: no heap
exhaustion occurred.**

## 5. THE FOUR NEGATIVE CONTROLS, AND WHAT EACH ONE NAMED

Each control was applied, run and reverted. All four are recorded in the probe
files, at `ProbeLJ1332A.agda:281-340` and `ProbeLJ1332B.agda:50-75`, because
nothing typechecks these files once the task closes. **All four MEASURE.**

**CONTROL 1, ON THE TRUNCATION AT THE LIMIT BAND.** I offered the truncated
injection where PART 3's reduction takes the honest one. Agda named the blocker,
2 s:

```
error: [UnequalTerms]
∥ ⟪ α ⟫ ↪ ⟪ β ⟫ ∥₁ !=<
(Σ (⟪ α ⟫ → ⟪ β ⟫) (λ f → (x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y))
when checking that the expression t has type ⟪ α ⟫ ↪ ⟪ β ⟫
```

**The reduction needs a FUNCTION, and every supplier at this band offers a
truncation.**

**CONTROL 2, ON THE ELIMINATION AT THIS SITE.** I eliminated the witness into
the untruncated goal, with `refl` for propositionality. Agda refused, 3 s:

```
error: [UnequalTerms]
x != y of type
Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
(λ f → (x₁ y₁ : ⟪ α ⟫ × ⟪ α ⟫) → f x₁ ≡ f y₁ → x₁ ≡ y₁)
when checking that the expression refl has type x ≡ y
```

**The goal is not a proposition, and the machine names the two arbitrary
pairing functions.** That is `[LJ-1.321]`'s `2-Constant` obligation, stated by
Agda, at the limit band.

**CONTROL 3, ON THE LEAD'S CIRCULARITY.** I fed `stage-card-at` the descent's
hypothesis, which supplies the law at MEMBERS of α, in place of the module's own
parameter, which supplies it at α too. Agda refused, 2 s, and it expanded
`sucV α` to its union representation while doing so:

```
error: [UnequalTerms]
∥ Σ-syntax (SetStructure.X (UnionStructure ⁅ α , ⁅ α ⁆s ⁆)) ... ∥₁
!=< (fst (δ ∈ α))
when checking that the expression δ∈sα has type ⟨ δ ∈ˢ α ⟩
```

**THE MACHINE NAMES THE CIRCULARITY.** The module parameter's range is `sucV α`,
so it reaches α itself; a descent's hypothesis never does. **A descent cannot
feed `stage-card-upper` at its own site.**

**CONTROL 4, ON THE WHOLE RESULT.** I asked `limit-truncated` for the
untruncated law and changed nothing else. Agda refused, 2 s:

```
error: [UnequalTerms]
∥ _B_547 ∥₁ !=<
Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
(λ f → (x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)
```

**THAT IS THE VERDICT IN ONE ERROR MESSAGE.** Everything in the limit band is
built. The distance to the goal is the pair of truncation bars, and nothing
else.

## 6. WHAT REMAINS OF `[LJ-1.8]`'s BLOCKER

| band | supplier | status after this probe |
|---|---|---|
| ω | `squareω`, `src/L/InjChain.lagda.md:184-185` | **DELIVERED, untruncated** |
| `Init` ordinals | `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` | **DELIVERED, untruncated** |
| successors above ω | `sq-suc`, `agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127` | **BUILT, untruncated, not landed** |
| **non-initial LIMITS** | `limit-truncated`, `ProbeLJ1332A.agda:196-204` | **BUILT, TRUNCATED, not landed** |

**The blocker is no longer a missing construction. It is a missing
untruncation, at ONE band.** Every other band has an untruncated supplier, and
the limit band has a truncated one that this probe built.

**AND THE BAND'S SHAPE IS NOW SIMPLER THAN THE PROJECT BELIEVED.**

1. **It is not about the LEAST cardinal.** `notRow4→merely` asks for SOME
   infinite member β with `⟪ α ⟫ ↪ ⟪ β ⟫ × ⟪ β ⟫`. `LeastCardInjL` computes the
   least such ordinal and pays for the well-order search
   (`src/L/Cardinal.lagda.md:100-152`). **The limit band never needs that
   search.**
2. **It is not about a bijection.** `[LJ-1.330]` corrected that, and my term
   uses two injections with the back leg free.
3. **It is not about `Lset` or the stages.** My term names no stage.

**WHAT I DID NOT SETTLE, and I name it rather than guess.**

- **The untruncation itself.** C-36 binds: I refuted one supplier
  (`stage-card-upper`) and built the truncated law. **I did not prove the
  untruncated law impossible and nothing here says it is.**
- **The successor-or-limit dichotomy.** `Split` at `ProbeLJ1332A.agda:234-236`
  is a HYPOTHESIS in my file, not a theorem. The full four-band assembly needs
  it, and it is ordinal bookkeeping I did not write.
- **The assembly under a truncated induction hypothesis.** It WALLS. Section
  4.1.
- **`Init (+ω ω)` is refutable.** INFERRED, not built. Section 2.
- **The sweep (C-42).** I measured ONE shape, `sq` at the limit band. **I did
  not sweep `src/` for other hypotheses that a module parameter supplies to its
  own site, and I claim no count.**
- **The landing cost.** Every second here is warm and P-l forbids pricing a
  landing from them.

## 7. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's own axis is AC against GCH, fixed in
code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the term name a tower, a stage or a formula?**

**Answer: `limit-truncated` and everything it rests on are TOWER-BLIND, MEASURED
from my own imports** at `ProbeLJ1332A.agda:26-45`.

- `Row4`, `Witness`, `notRow4→merely`, `witness→sq` and `limit-truncated` name
  `S`, `IsOrd`, ambient membership, `ω`, `sucV` and `sq`. **They name no
  `Lset`, no `Formula`, no `𝒟ₒ` and no `⊨`.**
- `member-inj→sq` names two ambient carriers and two injections only.
- **`[LJ-1.330]`'s property is KEPT, and the brief asked me to keep it.** My
  term takes a POINT of a delivered injection type and never a total map out of
  `sq α`. That is why it reaches its site, and it is why `[LJ-1.329]`'s object
  could not exist.
- **The one import that is NOT tower-blind is `Lset`**, and it enters only
  through `lset-route` and `ProbeLJ1332B.agda`, which exist to REFUTE the lead.
  **No term I would propose for landing names a stage.**

**WHAT MY TERM WOULD ADD TO THE GCH CLOSURE. MEASURED where I can, INFERRED
where I cannot.**

- **MEASURED: my imports pull nothing new.** `L.Ordinal.SquareLaw`,
  `L.Ordinal.Linear`, `L.Ordinal`, `L.Constructible`, `L.Cardinal`,
  `V.Hierarchy`, `V.Presentation` and `V.Model` are all already in both
  closures.
- **MEASURED: `limit-truncated` does NOT import `L.Absorption` or
  `L.InjChain`.** Only `sq-suc` does, and `sq-suc` is `[LJ-1.330]`'s term and
  not mine. **So the 2.0-point rise `[LJ-1.330]` inferred is NOT charged by my
  term.** The limit band rides the existing GCH closure.
- **INFERRED, and I mark it INFERRED:** landing `limit-truncated` alone would
  move no ledger row, because it adds no import edge. **I did not run
  `ledger.py --reuse` with my term, because the term is not landed.** The
  standing figure I quote comes from `ledger.py --brief` under my own hand:
  **32,474 lines over 94 masters, measured from HEAD.** The tool reports the
  endpoint REFUSED and the DD5 benchmarks NOT MEASURED, so I quote neither.

## 8. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **IT BUILDS** | **NOT TAKEN.** The law builds TRUNCATED, not untruncated. `sq` is not yet total and `[LJ-1.8]`'s blocker is not gone |
| **THE MOTIVE KILLS IT, as it killed `[LJ-1.324]`** | **NOT TAKEN, and I say so in section 1.** The motive has ONE index here. **The lead dies of a different defect: it consumes `sq` at its own site** |
| **IT NEEDS THE TRUNCATED `κ-inj` AND NOTHING ELSE** | **TAKEN, with the supplier CORRECTED.** It needs ONE untruncation. The supplier is `Init`'s fourth row, not `κ-inj`, and it is weaker and cheaper. Section 3.3. The live candidate is `[LJ-1.321]` section 8 item 2 |
| **THE LIMIT BAND IS EMPTY OR UNREACHABLE** | **NOT TAKEN.** The consumer quantifies over it with no restriction, `src/L/BoundedSubset.lagda.md:1388-1391` |
| **A WALL past 30 MINUTES** | **NOT TAKEN at the 30-minute line.** Three runs were INTERRUPTED at my own 600-second and 400-second harness limits, and section 4.1 bisects the cause to ONE definition. No heap exhaustion. The cap was never raised |

## 9. THE RULES THIS CHAIN EARNED, ANSWERED

- **C-44. The brief warned about its own premise.** **The premise「
  `stage-card-upper` is the lead」is FALSE, and section 1 refutes it with a
  term.** That is the fifth check in a row to find something.
- **C-36. A failed substitution is not a proof of impossibility.** I refuted the
  DELIVERED `stage-card-upper` at every α. **I did not refute
  `[LJ-1.324]`'s generic engine, and I say so in section 1.**
- **C-42. A refutation measures the site it names.** `[LJ-1.324]` measured
  `CanonInj`'s pair. **It does not reach this pair, and section 1 measures
  why.** My own refutation measures one shape and I claim no count.
- **D-10. Price the TRUTH of a recorded residue before pricing its proof.** I
  priced the truth first, in section 2, and then found the residue is TRUE and
  provable up to a truncation.
- **C-45.「`exit 0` is not a supply.」** Both probes are green and land nothing.
  **The `sq` hypothesis still has no consumer in `src/`:** `BoundedSubsetAt` at
  `src/L/BoundedSubset.lagda.md:1385` is its only site, MEASURED by `[LJ-1.330]`
  and unchanged by me.
- **P-l.** I priced nothing by analogy. Every second is warm and section 4 says
  so.
- **D-1.** The abort criterion was fixed before the run and section 8 answers it
  row by row.

## 10. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-332/` only**, three files: this report,
  `ProbeLJ1332A.agda` and `ProbeLJ1332B.agda`. Nothing in `src/`, nothing in
  `dev/`, no other task directory, no `.claude/`, no `AGENTS.md`.
- **I read the sibling probes and changed no line of them.** I read
  `agents/tasks/LJ-1-330/ProbeLJ1330A.agda` and `agents/tasks/LJ-1-324/Graft.agda`
  and re-derived from them rather than editing them.
- **I did NOT land `[LJ-1.330]`'s successor lemma.** `sq-suc` sits in my probe,
  in `agents/tasks/`, and I changed no chapter.
- **I did NOT attempt `[LJ-1.329]`'s alternative 2.**
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda: eighteen invocations, ONE process at a time.** Slots counted before
  every one with the brief's command. `GHCRTS="-A64m -I0 -M8g"` on every run.
  Cap never raised. **A sibling held one slot during runs 1 and 2 only; every
  other run counted 0.**

## 11. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-324/lj-1.324-report.md`, READ WHOLE, as the brief
  ordered.** Line read `:113-131`, section 2.3:「**ONE index. Source and target
  move TOGETHER.** That is what makes the induction close ... `CanonInj`'s
  motive would have to FIX the target `δ` and move the source」. **TOOK: the
  exact statement of the killer, and it is what let me measure that this pair
  has one index and is therefore untouched by it.** Also `:85-93`, which names
  `sq` as `stage-card-upper`'s own module parameter. **That line is the seed of
  my whole section 1, and `[LJ-1.324]` recorded it without spending it.**
- **`agents/tasks/LJ-1-330/lj-1.330-report.md`, READ WHOLE.** Line read
  `:77-82`:「ONE leg is free at every ordinal ... So the whole obligation is ONE
  untruncated injection」. **TOOK: `transport-sq` and `ord-emb`, re-derived at
  `ProbeLJ1332A.agda:106-130`, and the shape of my section 3.1.**
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ section 8 whole.** Line
  read, item 2:「A weakly constant endomap of `sq α` by any other route. Kraus
  et al. Theorem 16 says this is exactly equivalent to what is wanted」. **TOOK:
  the candidate my measurement returns the question to.** **Item 4 I now
  RETIRE**, as `[LJ-1.330]` retired item 3.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:214` (L3.32-T185):「Statement-shape probe: below-lim as an induction over
  limits | GREEN at 139 of 150: the induction assembles and the T182 wall IS the
  hypothesis」. **TOOK, SHAPE ONLY: the retired route also met a limit case
  where the induction assembled and the residue moved into the hypothesis, which
  is the shape of my section 4.1.** **WHAT WOULD NOT TRANSFER:** every figure in
  that row prices modules of a retired tower that no longer exist, and its report
  lives in `_build/`, a temporary folder, so no figure of it is readable today
  and I quote none. **Its wall was a LINE BUDGET; mine is a CHECK TIME. The two
  are not comparable and I do not compare them.**

## 12. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`. IT BEARS.** READ `:279-284` and `:411-417`.

  **THE BRIEF'S ONE-LINE QUESTION, answered: DEVLIN HAS NO SEPARATE LIMIT CASE,
  AND THAT IS THE POINT.** Line read `:280-284`:「|L_α| = |α| for infinite α
  (1.1(vii)), and the cardinal fact |γ| = |α| < κ with κ a cardinal implies
  γ < κ ... Strength: ... the level-size equation and initial-ordinal
  arithmetic」. **He reduces EVERY infinite α, limit or successor, to its
  initial ordinal by cardinal arithmetic. He never builds a pairing at a
  non-initial limit.**

  **AND HIS REDUCTION IS AN EQUINUMEROSITY, WHICH IS THE TRUNCATION.** Line read
  `:411-415`:「|L_α| = |α| for α ≥ ω ... is generic cardinal arithmetic over the
  level-size equation」. A cardinality equation asserts that a bijection EXISTS.
  **In this setting that is `∥ ... ∥₁`, and `limit-truncated` is exactly that
  statement, built.**

  **SO THE DEVICE THIS TREE IS MISSING IS NOT IN DEVLIN.** His argument is
  complete at the truncated level and mine now matches it there. **The
  untruncation is a demand this formalization makes and his proof never owes.**
  That is why five tasks searched for an object his proof does not contain.

  **WHY NOT re-fetched:** the digest carries locators into `dev2.txt` and I take
  statement-level facts only.
- **`dev/literature/truncation-and-selection.md`. NOT READ, and WHY NOT:**
  `[LJ-1.329]` and `[LJ-1.324]` used it to price a well-order on a function
  type. **My term needs no order on any function type**, so its subject does not
  reach my construction. **It WOULD bear on the untruncation that remains**, and
  a brief that funds `[LJ-1.321]` item 2 should carry it.
- **Jech 13, Schindler and Zeman, Kraus and others. NOT READ at this task, and
  WHY NOT:** my question is whether one construction exists in this tree at one
  band. **The type checker settles that and no classical source can.** Kraus and
  others bears on the REMAINING question, not on mine, and `[LJ-1.321]` already
  read it.

## 13. CHECKS RUN

- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-332/ProbeLJ1332A.agda`: exit
  0, 2 s.
- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-332/ProbeLJ1332B.agda`: exit
  0, 3 s.
- `.venv/bin/python scripts/gate/lint-agda.py --check` on both probe files: exit
  0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file: exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: recorded in section 14.
- `.venv/bin/python scripts/dispatch/rules.py --for probe`: run, every statement
  read. **I opened the full `dev/LESSONS.md` entry for D-1, C-42 and P-l**, the
  three laws I acted on.
- `.venv/bin/python scripts/measure/ledger.py --brief`: run under my own hand,
  and section 7 quotes it and nothing else.
- MEASURED: no em dash in any of the three files I wrote, by `grep -c`, 0 in all
  three.
- MEASURED: `grep -c "postulate\|TERMINATING\|{!\|trustMe"` on both probe files:
  0. Both are `--safe` with no hole and no postulate.
- **Every `ProbeLJ1332A.agda:<line>` and `ProbeLJ1332B.agda:<line>` citation in
  this report was re-verified against the files after my last edit**, by
  printing the cited start line and reading the identifier there.

## 14. LINT AND TREE STATE

- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-332/ProbeLJ1332A.agda agents/tasks/LJ-1-332/ProbeLJ1332B.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-prose.py --check agents/tasks/LJ-1-332/lj-1.332-report.md`:
  exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: **clean, 3,141 tracked files,
  no probe outside `agents/tasks/` and no generated file.**
- `git status --porcelain`: **my three new files only.** No tracked file is
  modified. I ran no `git` command that writes.
- **I removed four imports I did not use** after the last green run
  (`∈-induction`, `∈sucV-elim`, `mem-ord`, `ord-tri`) and one more (`V`), then
  re-checked: exit 0, 2 s. **`lint-agda.py` passed before and after; I removed
  them for craft, not because a gate demanded it.**
