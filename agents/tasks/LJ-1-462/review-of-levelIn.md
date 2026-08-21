# LJ-1.462 review of `levelIn`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The consumer's type, copied from `src/L/BoundedSubset.lagda.md:917`:

```agda
levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
```

The probe restates the site. It does not import the module parameter.
Telescope: `agents/tasks/LJ-1-462/Probe462.agda:78-90`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below `module Condense`
is copied. There is no term named `levelIn`. The witness meter reports
`1 UNRESOLVED of 1` (`agents/tasks/LJ-1-462/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at D-10 step 3. This is not `[LJ-1.451]`'s absence. The formula
is delivered. The two formula types do not meet. The W3 type is
well-formed and unbuilt:

```agda
lset-code :
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))
```

at `Probe462.agda:109-111`. Three forced rechecks, exit 0, caliber
`-A64m -I0 -M8g`. Median wall **4.71 s**. Median peak RSS
**1240268800 bytes**. `runs/w3-{1,2,3}.out`.

This is an obstruction of the hull-language route. It is not a
refutation of `levelIn`. I did not build a term of the negation. I did
not prove the type false.

## WHICH PREMISE MOVED

`[LJ-1.451]` (`agents/tasks/LJ-1-451/lj-1.451-report.md:68`) is NO-GO
at D-10 step 3 because `Code` has `base` and `wit` only and the formula
was judged not delivered. The constructor measurement still stands
(`src/L/Hull.lagda.md:72-74`).

`[LJ-1.458]` (`agents/tasks/LJ-1-458/lj-1.458-report.md:71`) is GO:
`LsetAt` is `LsetGraphAt` at `src/L/Coding/Sequence.lagda.md:349`,
adequacy `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` with extra
`IsOrd`.

What moved is the formula question. The constructor question did not.

## THE FOUR STEPS, AS TYPES

1. Collapse membership. GO. Delivered.

       C.πX-member :
           (z : S) → ⟨ z ∈ˢ C.πX ⟩
         → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

   Site: `src/V/Collapse.lagda.md:78-79`. The probe inhabits it as
   `step1` (`Probe462.agda:133-134`).

2. Hull closure and commutation. Unbuilt. Not the failing step.

       HullClosedLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

       πCommuteLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

   Site: `Probe462.agda:136-142`.

3. Definability. FAIL. This is W3. `lset-code` at `Probe462.agda:109-111`.
   The two formula types do not meet.

       LsetGraphAt : ∀ {n} → Fin n → Fin n → Formula CS.S n
       -- src/L/Coding/Sequence.lagda.md:349
       -- lives in Type (ℓ-suc ℓ)

       wit : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code
       -- src/L/Hull.lagda.md:74
       -- lives in Type ℓ

   A `subst` cannot join them. Packaging is `absFo` at
   `src/FOL/Manipulation/Parameters.lagda.md:260`. The probe inhabits
   it as `packaged` (`Probe462.agda:66-67`) and feeds it to `wit` as
   `feed` (`Probe462.agda:101-102`). `feed` needs a further
   `Vec Code (countFo LsetGraph)`. Those codes are not delivered.
   `Lset-only` needs `IsOrd` (`src/L/Hierarchy.lagda.md:334-335`).
   That hypothesis does not arise on `Code`.

4. Absoluteness. Unbuilt. Same type as `πCommuteLset`. Not reached.

## THE MEETING, AND WHAT REMAINS AFTER IT

`packaged = absFo {ℓz = ℓ} LsetGraph` has type
`Formula (⊥* {ℓ}) (2 + countFo LsetGraph)` (`Probe462.agda:66-67`).
That type meets `wit`'s formula slot at `k = suc (countFo LsetGraph)`.

`feed` is not `lset-code`. It takes an extra `Vec Code`. The
constants of `LsetGraphAt` are class-carrier numerals:
`tagAtL` names `con (numeralL k)` at
`src/L/Coding/Model.lagda.md:586`. `constantsFo LsetGraph` is
`Vec CS.S`, not `Vec Code`.

`erase` at `src/FOL/Count.lagda.md:598` is not the packaging.
`Count` is parameterised by `K : Type ℓ` (`:222`). At `K = CS.S`
that `ℓ` is `ℓ-suc ℓ`.

The hull carries no ordinality. The D-10 correction
`lset-code-ord` (`Probe462.agda:118-121`) adds `IsOrd`. It is
still unbuilt.

`Code` still has two constructors (`src/L/Hull.lagda.md:72-74`).
I did not add a third. `base` names seed elements of `X` only
(`src/L/Hull.lagda.md:323`).

## THIS IS NOT A REFUTATION OF THE TYPE

`levelIn` may still hold by another route. `[LJ-1.160]` closed it from
unpaid `CrossOut` and `HasLevels`
(`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:83-88`). `[LJ-1.121]` did
not refute it (`agents/tasks/LJ-1-121/lj-1.121-report.md:7-8`). D-10:
the hull-language route dies at step 3, now as a type-meeting failure,
not as an absent formula. The original target is not recorded as false.

## THE SWEEP (C-42)

This return is not a refutation, so the count is of the named unpaid
shape, not of a false statement. I re-counted on this tree. I did not
copy `[LJ-1.451]`'s line numbers.

Shape: `(δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → ⟨ Lset δ ∈ˢ πX ⟩`.

A grep over live `src/` returns exactly nine `levelIn` lines.

COUNT of binders: 4.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:917` | `Condense` parameter |
| `src/L/BoundedSubset.lagda.md:1555` | `Co` restatement |
| `src/L/StageBound.lagda.md:67` | `Instantiation.Co` parameter |
| `src/L/StageBound.lagda.md:93` | truncated `Co` parameter |

COUNT of applied spends as data: 1, at
`src/L/BoundedSubset.lagda.md:1020`, inside `Lβ⊆πX` at `:1012`.

COUNT of pass-down spends as module arguments: 3.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:1560` | `module Cn = HS.Condense levelIn cover` |
| `src/L/StageBound.lagda.md:72` | `module C = BSA.Co levelIn cover` |
| `src/L/StageBound.lagda.md:105` | `module C = I.Co levelIn cover` |

COUNT of comments: 1, at `src/L/BoundedSubset.lagda.md:1011`.

COUNT of producers in `src/L/Condensation.lagda.md`: 0. `grep` for
`levelIn` and for `cover` both return no match. No producer exists
anywhere in live `src/`. One producer at the `Condense` level pays
all eight live sites, because the three pass-downs sit below binders
of the same shape.

## W2 (DD4)

Every type above is generic in `ℓ`, `lam` and `X`. No ordinal is
fixed. No second copy at a concrete stage.

## WHAT THE NEXT BRIEF MUST ORDER

Not `LsetAt` again. Not `LsetGraphAt` as a drop-in argument to `wit`.
The types do not meet.

One of these, after this measurement:

1. Hull codes for `constantsFo LsetGraph`, then the equality at
   `Lset-only` under `IsOrd`. Do not assume `Lset-only` reads
   `wit`'s satisfaction: `Lset-only` is at the class carrier
   (`src/L/Hierarchy.lagda.md:73`), and `wit` searches in the
   stage `TermAlgebra` (`src/L/Hull.lagda.md:323`).
2. A `Formula (⊥* {ℓ}) 2` with no class-carrier constants, so
   `wit 1 ψ (c ∷ [])` is well-typed without an extra `Vec Code`.
   `[LJ-1.451]` named that type `MissingFormula`. It is still unbuilt.
3. A route that does not go through the hull language.

This task does not pay `cover`.
