# LJ-1.324 report: transplant `stage-card-upper` to `CanonInj`'s pair

## 0. VERDICT

**REFUTED.**

**The transplant is not expensive. It is CIRCULAR, and a term says so.**
`stage-card-upper`'s value map pairs the stage index `m : ⟪ α ⟫` with a formula
count (`src/L/StageCardinal.lagda.md:322`). At its own pair the index already
lives in the target, so that component is the identity. At `CanonInj`'s pair the
target is `⟪ δ ⟫` with `δ ∈ α`, so the index must be placed there injectively,
and **that placement IS `CanonInj`**. The identity function typechecks between
the two types:

```agda
missing-is-goal : MissingIndex → CanonInj
missing-is-goal x = x
```

`agents/tasks/LJ-1-324/Graft.agda:375-376`. Green, exit 0.

**What IS refuted, exactly:** the transplant of `stage-card-upper`'s
construction to `CanonInj`'s pair. **`CanonInj` itself is NOT refuted**, and
`[LJ-1.321]` section 7's well-order route is untouched.

**What the run also delivered, and it survives the refutation:**
`stage-card-upper`'s engine, extracted GENERIC, with `Lset`, `Formula`, `V` and
`L` all removed (`Graft.agda:86-129`, 39 non-blank non-comment lines). It is
tower-blind, so it is shared machinery by construction (DD4).

**And one half of the transplant DOES work**, MEASURED by a term: the COVER.
`cover-ord` at `Graft.agda:220-246` builds the definability decomposition at
`CanonInj`'s source with no new hypothesis. **The lead was half right.**

Everything below is typechecked in `agents/tasks/LJ-1-324/Graft.agda`, exit 0,
13.6 s, 0 agda slots counted before every run, `GHCRTS="-A64m -I0 -M8g"`, cap
never raised.

## 1. `CanonInj`'s target pair, as I read it

`agents/tasks/LJ-1-321/Door.agda:193-195`:

```agda
CanonInj = (α : V ℓ) (m : ⟪ α ⟫) → IsOrd α
         → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ → ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫
```

In my own words. Write `δ = ⟪ α ⟫↪ m`, the member of `α` that the index `m`
names.

- **SOURCE** `⟪ α ⟫`, the carrier of an AMBIENT ordinal `α`. Its elements are
  the ordinals below `α`. `α` is a `V ℓ`, not an `S` of `L`.
- **TARGET** `⟪ δ ⟫`, the carrier of a MEMBER `δ ∈ α`. The target is STRICTLY
  SMALLER as an ordinal.
- **HYPOTHESES** `IsOrd α`, and the TRUNCATED injection `∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁`.
- **CONCLUSION** the UNTRUNCATED injection. It must be a function of `α` and
  `m` alone, because the truncation is a proposition.

**So `CanonInj` is a BIG-INTO-SMALL injection.** I copied it verbatim into
`Graft.agda:138-141` and every term below is stated against that copy.

**THE PAIR IS NOT WRONG.** I looked for the fourth abort case and did not find
it. `canon→step` (`Door.agda:202-208`) consumes `CanonInj` exactly at the least
member index `m₀` that `leastWat` returns, and `sq-transport`
(`Door.agda:94-110`) consumes the result at that same member. The type matches
its consumer.

## 2. The three differences, each measured

### 2.1 The carriers

| | `stage-card-upper` | `CanonInj` |
|---|---|---|
| source | `⟪ Lset α ⟫` | `⟪ α ⟫` |
| target | `⟪ α ⟫` | `⟪ ⟪ α ⟫↪ m ⟫` |
| indices | ONE, `α`, and both carriers move with it | TWO, `α` and `m` |
| direction | stage into its own index | ordinal into a MEMBER of itself |

`src/L/StageCardinal.lagda.md:564-566` against `Door.agda:193-195`.

**The difference that matters is not the size. It is the NUMBER OF INDICES.**

### 2.2 The hypotheses

`stage-card-upper` carries three at its own signature and one in its module
telescope:

- `IsOrd α`, `⟨ α ∈ˢ sucV α₀ ⟩` (bounded) and `⟨ α ∈ˢ ω ⟩ → Empty.⊥`
  (infinite), `src/L/StageCardinal.lagda.md:564-565`.
- **`sq`, the SQUARE LAW at every bounded infinite δ**, the module parameter at
  `src/L/StageCardinal.lagda.md:17-19`. **MEASURED: `stage-card-upper` is a
  CONSUMER of the square law**, and the square law is what `[LJ-1.8]` is trying
  to build. It is consumed at `:283` as `module B = Bound α oα infα (sq α ...)`.

`CanonInj` carries `IsOrd α` and the truncated injection, and nothing else.

**Two of these move in opposite directions, and only one is a problem.**

1. **The truncated injection is EXTRA and it is free.** `stage-card-upper` has
   no such hypothesis. Adding one costs nothing.
2. **The pairing at the target is MISSING from `CanonInj`'s type, and it is
   RECOVERABLE.** MEASURED by reading the consumer: `canon→step` holds
   `ih : IH α` in scope, and `IH α = (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → sq δ`
   (`Door.agda:199-200`, used at `:202-208`). At the call `ci α m₀ oα (snd got)`
   the term `ih (⟪ α ⟫↪ m₀) (member α m₀) : sq δ` is available. **So a
   strengthened `CanonInj` that also takes `sq δ` costs the reduction nothing.**
   I did not need this, because the refutation below does not turn on it.

**INFERRED, not measured:** that `δ` is infinite. `⟪ α ⟫` injects into `⟪ δ ⟫`
and `α` is infinite in the branch that matters, so `δ` is infinite. I did not
write that term, because the refutation does not need it.

### 2.3 The motive. THIS IS THE ONE THAT KILLS IT.

`Upper.P` at `src/L/StageCardinal.lagda.md:530-532`:

```agda
  P : S → Type (ℓ-suc ℓ)
  P α = IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ] ((x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y)

  stage-card-upper = ∈-induction step
```

**ONE index. Source and target move TOGETHER.** That is what makes the
induction close, and section 3 shows exactly where.

`CanonInj`'s motive would have to FIX the target `δ` and move the source, or
carry both indices. `∈-induction` (`src/V/Hierarchy.lagda.md:177-180`) recurses
on one. **The brief predicted that a difference in the motive is what usually
kills a transplant. MEASURED: it is.**

## 3. The limit step, because it is the case with no supplier

`limit-step` (`src/L/StageCardinal.lagda.md:396-403`) is `LimitStep.h` and
`LimitStep.h-inj` (`:277-394`). I extracted its engine, generic, at
`Graft.agda:86-129`, and then fed the transplant to it ingredient by ingredient.

### 3.1 The engine, and it is not the content

```agda
module Engine (Src Tgt Cod : ...) (Amb : ...) (setAmb : isSet Amb)
              (order : SWO Tgt)
              (into : Src → Amb) (into-inj : ...)
              (name : Cod → Amb)
              (val : Cod → Tgt) (val-inj : ...)
              (cover : (x : Src) → ∥ Σ[ c ∈ Cod ] (name c ≡ into x) ∥₁)
```

`Graft.agda:86-95`. Read it against `class-pred` (`:319-323`), `nonempty`
(`:325-348`), `h` (`:350-351`) and `h-inj` (`:353-394`): the delivered code uses
these fields and nothing else.

**MEASURED: the engine alone buys nothing at any pair.** `coding→canon`
(`Graft.agda:153-166`) turns an engine input into `CanonInj`, and
`canon→coding` (`Graft.agda:172-175`) turns `CanonInj` back into an engine
input. **So the content of `stage-card-upper` is never the engine. It is the
delivered code type that feeds it.**

### 3.2 What the engine needs at `CanonInj`'s pair, item by item

| ingredient | at `CanonInj`'s pair | evidence |
|---|---|---|
| `Amb`, `setAmb` | FREE, `S` and `isSetS` | `Graft.agda:163` |
| `into`, `into-inj` | FREE, `⟪ α ⟫↪` and `↪-inj` | `Graft.agda:164` |
| `order` on `⟪ δ ⟫` | FREE, `ordSWO δ oδ`, `δ` is an ordinal by `mem-ord` | `Graft.agda:163` |
| `Cod`, `name` | FREE, transplanted verbatim | `Graft.agda:199-203` |
| **`cover`** | **TRANSPLANTS. MEASURED.** | `Graft.agda:220-246` |
| **`val`, `val-inj`** | **REFUTED. MEASURED.** | `Graft.agda:264-285` |

### 3.3 The cover TRANSPLANTS, and this is a real positive

`stage-card-upper`'s cover is built from `Lset-out`
(`src/L/Constructible.lagda.md:336-338`) and `𝒟ₒ-inv` (`:306-308`): every member
of a stage is merely definable over an earlier stage. Its source is
`⟪ Lset α ⟫`. `CanonInj`'s source is `⟪ α ⟫`.

**It still works**, because every member of an ordinal is a member of that
ordinal's own stage (`Lower.α⊆Lset`, `src/L/StageCardinal.lagda.md:193-195`,
re-derived at `Graft.agda:193-196`):

```agda
cover-ord : (α : S) (oα : IsOrd α) (x : ⟪ α ⟫)
          → ∥ Σ[ c ∈ Code α ] (codeName α c ≡ ⟪ α ⟫↪ x) ∥₁
```

`Graft.agda:220-221`. Green. **So `⟪ α ⟫` DOES have a delivered naming
structure. That was the thing I most expected to be missing, and it is not.**

### 3.4 The value map is REFUTED, by a term

`stage-card-upper`'s value map is `B.pair m (cnt m φ)`
(`src/L/StageCardinal.lagda.md:322`), where `B.pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫`
(`:68-69`) and `cnt m : F m → ⟪ α ⟫` (`:288-289`).

**Its FIRST component is the stage index `m : ⟪ α ⟫` itself.** At the own pair
that index is already an element of the target, so the placement is the
identity. **This is what `stage-card-upper` gets for free, and it is free only
because the motive has ONE index.**

At `CanonInj`'s pair, the term:

```agda
val→goal : (α : S) (δ : S) (val : Code α → ⟪ δ ⟫)
         → ((c d : Code α) → val c ≡ val d → c ≡ d)
         → ⟪ α ⟫ ↪ ⟪ δ ⟫
val→goal α δ val val-inj = f , inj
  where
  sect : ⟪ α ⟫ → Code α
  sect m = m , ⊥̇
  ...
  inj m n e = cong fst (val-inj (sect m) (sect n) e)
```

`Graft.agda:264-274`. Green. The section picks the closed formula `⊥̇`
(`src/FOL/Syntax.lagda.md:98`), which exists over every parameter type.

**So ANY injective value map on the transplanted code type already contains
`CanonInj`'s conclusion.** Stated at the pair, `Graft.agda:278-285`:

```agda
transplant-not-cheaper :
    ((α : S) (m : ⟪ α ⟫) → IsOrd α → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
     → Σ[ val ∈ (Code α → ⟪ ⟪ α ⟫↪ m ⟫) ] (injective))
  → CanonInj
```

**MEASURED. The transplant cannot be cheaper than its goal.**

### 3.5 The second killer: the branch runs the other way

`cnt m φ` needs an injection of `⟪ Lset (⟪ α ⟫↪ m) ⟫` into the target, and that
is `branch` (`src/L/StageCardinal.lagda.md:534-559`, consumed at `:562`).

**At the own pair the branch is FREE.** It composes the induction hypothesis
`⟪ Lset γ ⟫ ↪ ⟪ γ ⟫` with the small-into-big embedding `⟪ γ ⟫ ↪ ⟪ α ⟫`
(`:506-515`, used at `:556`). I re-derived that composition at
`Graft.agda:324-328`:

```agda
own-branch : (α : S) (oα : IsOrd α)
           → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫)
           → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
```

Green. **The free direction is small-into-big, and it is free because the
target is the induction's own index.**

**At the transplanted pair the target is `⟪ δ ⟫` with `δ ∈ α`, so the same
composition runs big-into-small.** MEASURED at `Graft.agda:348-354`:

```agda
branch→member : (α : S) (oα : IsOrd α) (δ : S)
              → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
              → (m : ⟪ α ⟫) → ⟪ ⟪ α ⟫↪ m ⟫ ↪ ⟪ δ ⟫
```

Green, by composing with the delivered lower half
(`src/L/StageCardinal.lagda.md:197-205`, re-derived at `Graft.agda:332-345`).
**A transplanted branch carries `CanonInj`'s own shape at EVERY member of `α`,
and it is demanded at all of them at once.**

## 4. The term I could not write (C-36)

Two types, both machine-checked as types, neither inhabited.
`Graft.agda:362-382`.

```agda
MissingIndex = (α : S) (m : ⟪ α ⟫) → IsOrd α
             → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
             → Σ[ f ∈ (⟪ α ⟫ → ⟪ ⟪ α ⟫↪ m ⟫) ]
                 ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y)

missing-is-goal : MissingIndex → CanonInj
missing-is-goal x = x
```

**`missing-is-goal x = x` TYPECHECKS.** `MissingIndex` IS `CanonInj`. **This is
the refutation in one line: the transplant's first ingredient is the goal, and
no work has been moved.**

```agda
MissingBranch = (α : S) (m : ⟪ α ⟫) → IsOrd α
              → (k : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ k) ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫
```

`Graft.agda:380-382`. Section 3.5 measures what it carries.

**THE HONEST RESIDUE, and I did not close it.** `val→goal` uses
`stage-card-upper`'s FULL code type, which is what the delivered construction
uses (`src/L/StageCardinal.lagda.md:320-322` quantifies over all `m` and all
`φ`). **A transplant on a RESTRICTED code type, holding only codes that name
members of `α`, escapes `val→goal` if the restriction blocks the section
`m ↦ (m , ⊥̇)`.** I did not measure whether it blocks it. **INFERRED, not
measured:** it does not block it, because `defSet A ⊥̇` is the empty set at every
`A` and the empty set is a member of every non-zero ordinal, so the section
survives the restriction. **Proving that needs a term I did not write.** Section
3.5's branch killer is independent of the restriction and stands either way.

## 5. Cost, with its basis (DD8)

**BASIS: A BUILD.** Not a comparable, not a survey.

| figure | value |
|---|---|
| `agents/tasks/LJ-1-324/Graft.agda` | 380 lines, 343 non-blank, **202 non-blank non-comment** |
| the generic engine, `Graft.agda:86-129` | **39 non-blank non-comment** |
| the delivered `class-pred` to `h-inj`, `src/L/StageCardinal.lagda.md:319-394` | 73 non-blank non-comment |
| the delivered stability lemmas, `:288-317` | 26 non-blank non-comment |

**THE PRICE OF THE TRANSPLANT ITSELF IS NOT A NUMBER OF LINES.** Its remaining
term is `CanonInj`, definitionally (section 4). **A refuted transplant has no
line price, and quoting one would be false.**

### Runs

Every run with 0 agda slots counted first by
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`.

| run | exit | elapsed | 1-minute load |
|---|---|---|---|
| `Graft.agda`, first attempt, one parse error | 1 | 2.4 s | 16.88 |
| `Graft.agda`, green | 0 | 13.6 s | 13.61 |
| `Graft.agda`, with PART 6, green | 0 | 13.6 s | 5.16 |

Cap `GHCRTS="-A64m -I0 -M8g"` on every run, never raised. **MEASURED FALSE: any
invocation past 30 minutes, and any heap exhaustion.** Dependencies were warm,
so **these seconds price a warm incremental check of one file and nothing
else.** The load figures are the machine's, which was not quiet; my deliverable
is a TERM, so they do not bear on it.

### The live ruling

**My result does not depend on how the trophies are STATED.** `Graft.agda`
imports neither `src/L/GCH.lagda.md` nor `src/L/Model.lagda.md`. MEASURED by the
import list, `Graft.agda:37-58`. I touched neither file.

## 6. DD4, stated and answered, with my axis (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's own axis is AC-against-GCH, fixed in
code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the construction name a tower?**

**`Engine` names NO tower. MEASURED by reading its own parameter list**
(`Graft.agda:86-95`): `Src`, `Tgt`, `Cod`, `Amb` are bare types, and `order` is
a bare `SWO`. No `V`, no `L`, no `Lset`, no ordinal, no stage. **It would compile
against any carrier.** That is the DD4 asset this run produced, and it survives
the refutation: **`stage-card-upper`'s technique is now available with both
towers removed, in 39 lines, for either end to use.**

Everything else in `Graft.agda` names the AMBIENT ordinals (`V ℓ`, `IsOrd`) and
the L stages (`Lset`, `DefOf.defSet`), because the transplant it measures does.

### Does the `pullOrder` DD4 gain survive?

**IT SURVIVES, because nothing here touches it.** MEASURED by my import list:
`Graft.agda:37-58` imports nothing from `src/L/Choice/`. `[LJ-1.321]`'s route
(`pullOrder` at `src/L/Choice/Step.lagda.md:252-258`, re-used from the AC
trophy's own machinery) is untouched and is still the live route.

**And it is not in competition with what I built.** `Engine` and `pullOrder` are
the same shape read from two ends: `pullOrder` moves a well-order ALONG an
injection; `Engine` builds an injection FROM a code class that a well-order
searches. Both call `leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`), which
is shared. **My engine adds no GCH-only import**: `L.WellOrder.Base`,
`L.Ordinal.SquareLaw` and `L.Ordinal.Stages` are all shared machinery.

**I did not run `ledger.py` and I quote no size figure from it.**
`dev/ledger.toml:204` records that the GCH closure is read from a STATEMENT
whose proof is not wired, so it UNDERSTATES.

## 7. The abort criterion, fixed before the run (D-1)

The brief fixed five. Which fired:

1. **It transplants and I build it.** DID NOT FIRE.
2. **It transplants with a gap.** DID NOT FIRE. The cover transplants (3.3),
   but the value map is not a gap; it is the goal (3.4).
3. **It does not transplant.** **FIRED.** Section 2.3 names the difference that
   kills it (the motive's index count), and section 4 writes the term I could
   not write.
4. **The pair is wrong.** DID NOT FIRE. Section 1.
5. **A wall past 30 minutes.** DID NOT FIRE. Section 5.

## 8. C-42: the sweep after the refutation

**A refutation measures the site it names.** This one measures ONE site: the
transplant of `stage-card-upper` to `CanonInj`'s pair.

**The sweep, MEASURED.** `grep -rn "leastOf" src/` returns 54 uses across 11
chapters. **I did not classify all 54** and I do not claim the engine's shape is
absent elsewhere. **What I do claim, and it is measured by the terms in section
3.2: every ingredient of the engine except the value map is available at
`CanonInj`'s pair.** So a NEW code type with an injective value map into
`⟪ δ ⟫` would close it, and `[LJ-1.321]` C-42 already says a census of `src/`
says nothing about what a NEW term could supply.

## 9. What I did not do

- I did not build the transplant on a restricted code type, and I did not
  measure whether the restriction blocks `val→goal`'s section (section 4).
- I did not typecheck that `δ` is infinite, or that the descent's `ih` supplies
  `sq δ` at the call site. Both are READINGS, at `Door.agda:199-208`, and
  neither is load-bearing for the refutation.
- I did not attempt `godSWO` or `god` against `CanonInj`
  (`[LJ-1.321]` section 8 item 3). Out of scope.
- I did not attempt the pointwise-least map (`[LJ-1.321]` section 8 item 1).
  Out of scope, and NOT refuted by anything here.
- I did not re-refute any of `[LJ-1.321]` section 8's four maps.
- I did not run `make check`, did not commit, did not push, and ran no
  destructive git command.
- I wrote only inside `agents/tasks/LJ-1-324/`. I edited nothing in `src/`,
  `dev/`, `AGENTS.md`, `.claude/` or any sibling task directory. I read and
  re-read `agents/tasks/LJ-1-321/Door.agda` and changed no line of it.

## 10. ARCHIVE USED (DD18), one line read per file

- `agents/tasks/LJ-1-321/lj-1.321-report.md:331-342`, section 8 item 4: the lead
  itself, and its refusal to price by analogy. **Read WHOLE**, with
  `Door.agda`. **Its section 8 lists four maps, none refuted; I re-refuted
  none.**
- `agents/tasks/LJ-1-314/lj-1.314-report.md:72-77`: `leastOf` demands a
  PROPOSITION-valued predicate, `src/L/WellOrder/Base.lagda.md:159`. **TOOK:
  that is why `Engine`'s `pred` (`Graft.agda:97-98`) is a truncation, and why
  the engine is canonical at all.**
- `agents/tasks/LJ-1-305/lj-1.305-report.md:145-146`: `sq α` is NOT an hProp,
  countermodel `sq-not-prop` at `agents/tasks/LJ-1-305/NotProp.agda:203-204`.
  **TOOK: it is why the target cannot be untruncated by propositionality and the
  whole `CanonInj` question exists.**
- `archive/dev/TASKS-archived.md:300` (L3.32-T158), **taken as SHAPE and never
  as a claim**: the retired route met its choice-shaped obligation by re-entering
  L through the DESCRIPTION side, not by an ambient device. **The same shape as
  the residue here.** Also `:192` (L3.32-T162): `pullSWO` stayed as SHARED
  machinery, which is `pullOrder`'s ancestor and section 6's DD4 point.
  **WHAT WOULD NOT TRANSFER:** every figure in those rows prices modules of a
  retired tower that no longer exist. A verdict on the AC route's bridge is not
  a verdict on the ambient-to-code crossing (P-l).

## 11. LITERATURE USED (DD18)

### READ

- `dev/literature/truncation-and-selection.md`, section 1 (`:14-52`, the
  classical move under a definable well-order) and section 5 item 2
  (`:310-315`).

**THE BRIEF'S ONE-LINE QUESTION, answered.** **NO: the transplant does not move
the object across that line, and it fails because the object it needs is already
on the wrong side.** `stage-card-upper` codes by SYNTAX, an ambient inductive
`Formula` with a numbering (`src/FOL/Count.lagda.md:81`'s `code`, used at
`src/L/StageCardinal.lagda.md:127`), which sits on the SET side and needs no
`<_L`. **The missing object at `CanonInj`'s pair is an INJECTION
`⟪ α ⟫ → ⟪ δ ⟫`, an ambient FUNCTION**, which is the side the digest says the
ordering cannot reach. `:313-315`: a canonical injection needs a well-order on
the INJECTIONS, which `<_L` supplies classically and an ambient function type
does not have.

**And the digest's section 5 item 2 already contains this refutation in
words.** Its `ω · 2` into `ω` failure is the same obstruction section 2.3
measures as a motive with two indices: the target is fixed while the source
grows, so the assembly at a limit has nothing left to place.

### NOT READ, WITH WHY NOT

- Devlin II.5, Jech 13, Schindler and Zeman. NOT READ at this task: my question
  is whether one delivered Agda construction re-instantiates at a second pair.
  That is settled by the type checker, and no classical source can settle it.
- Kraus, Escardó, Coquand and Altenkirch, LMCS 13(1) 2017. NOT READ directly:
  `[LJ-1.321]` uses it at `Door.agda:394-402` and nothing in my sections turns
  on it. My engine never asks for a weakly constant endomap.
- HoTT Book. NOT READ: the digest quotes what bears, and no number from the book
  is load-bearing here.

## 12. CHECKS RUN

- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-324/Graft.agda`: exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-324/Graft.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file: recorded
  in section 13.
- `grep -c "postulate\|TERMINATING\|{!\|trustMe" agents/tasks/LJ-1-324/Graft.agda`:
  0. The file is `--safe` with no holes and no postulate.
- MEASURED: no em dash in either file I wrote, by `grep -c`, 0 in both.
- `.venv/bin/python scripts/dispatch/rules.py --for probe`: run, every statement
  read. I opened the full `dev/LESSONS.md` entry for D-1 and for C-42, the two
  laws I acted on.

## 13. LINT RESULT

- `.venv/bin/python scripts/gate/lint-prose.py --check agents/tasks/LJ-1-324/lj-1.324-report.md`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-324/Graft.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: clean, 3081 tracked files,
  no probe outside `agents/tasks/`.
- Em dash count in both files I wrote: 0, by `grep -c`.
- `git status --porcelain`: my two files only. The `LJ-1-323` entries are the
  sibling's, and I did not touch them.
- **Every `Graft.agda:<line>` citation in this report was verified against the
  file after the last edit**, by printing the cited start line and reading the
  identifier there.
