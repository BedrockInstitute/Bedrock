# LJ-1.451 review of `levelIn`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The consumer's type, copied from `src/L/BoundedSubset.lagda.md:917`:

```agda
levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
```

The probe restates the site. It does not import the module parameter.
Telescope: `agents/tasks/LJ-1-451/Probe451.agda:43-55`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below `module Condense`
is copied. There is no term named `levelIn`. The witness meter reports
`1 UNRESOLVED of 1` (`agents/tasks/LJ-1-451/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at D-10 step 3. The hull's `Code` cannot name `Lset`. The W3 type
is well-formed and unbuilt:

```agda
LsetCode :
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))
```

at `Probe451.agda:82-84`. Three forced rechecks, exit 0, caliber
`-A64m -I0 -M8g`. Median wall **1.95 s**. Median peak RSS
**477036544 bytes**. `runs/w3-{1,2,3}.out`.

This is an obstruction of the hull-language route. It is not a
refutation of `levelIn`. I did not build a term of the negation. I did
not prove the type false.

## THE FOUR STEPS, AS TYPES

1. Collapse membership. GO. Delivered.

       C.πX-member :
           (z : S) → ⟨ z ∈ˢ C.πX ⟩
         → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

   Site: `src/V/Collapse.lagda.md:78-79`. The probe inhabits it as
   `step1` (`Probe451.agda:69-70`).

2. Hull closure and commutation. Unbuilt. Not the failing step.

       HullClosedLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

       πCommuteLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

   Site: `Probe451.agda:73-79`.

3. Definability. FAIL. This is W3. `LsetCode` at `Probe451.agda:82-84`.
   `Code` has two constructors (`src/L/Hull.lagda.md:72-74`):

       data Code : Type ℓ where
         base : K → Code
         wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code

   There is no constructor `lset : Code → Code`. I did not add one.
   `base` names seed elements of `X` only
   (`src/L/Hull.lagda.md:323`). `wit` is the only other constructor,
   and it needs the formula.

4. Absoluteness. Unbuilt. Same type as `πCommuteLset`. Not reached.

## THE SITE 120-123 IS NOT A CONSTRUCTOR

The brief named `src/L/Hull.lagda.md:120-123`. That site is `closed`:

```agda
closed : (φ : Formula Code 1)
       → ∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
       → ∥ Σ[ a ∈ S𝒮 ] (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ []) ⊨c φ ⟩) ∥₁
```

`closed` is closure under definable existence. It is not a constructor
of `Code`. It consumes a `Formula Code 1`. No such formula for `Lset`
is delivered. `Hull` exports `Code`, `base` and `closed`. The inner
`open T using` at `src/L/Hull.lagda.md:324` omits `wit`. That is not
an access barrier: `module T` at `:323` is not private, and this probe
spends `wit` at `Probe451.agda:58`.

The missing object is the formula. Two packagings, same gap:

- For `closed`: a `Formula Code 1` that holds of `a` just when
  `fst a ≡ Lset (fst (val c))`.
- For `wit`: `MissingFormula` at `Probe451.agda:97-100`:

      Σ[ ψ ∈ Formula (⊥* {ℓ}) 2 ]
        ((c : Code) → fst (val (wit 1 ψ (c ∷ []))) ≡ Lset (fst (val c)))

## THE FORMULA THAT EXISTS, AT THE WRONG LANGUAGE

`LsetGraphAt` is the graph of `Lset` at the class carrier:

    open RecShape StepAt public renaming ( GraphAt to LsetGraphAt

at `src/L/Coding/Sequence.lagda.md:349`. `LsetGraph : Formula S 2`
sits at `:353`. Its type is `Formula S n` with `S` the constructible
carrier. It is not `Formula Code n`. It is not `Formula (⊥* {ℓ}) n`.
Devlin names the same object as a Σ₀ formula Φ of LST
(`dev/literature/devlin-II5.md:95-96`). Transplanting that graph into
the hull language is the next brief. This task does not transplant it.

The vehicles are delivered: `embed` at
`src/FOL/Manipulation/Relabelling.lagda.md:117`, and `absFo` at
`src/FOL/Manipulation/Parameters.lagda.md:260`. `closed` already
spends `absFo` at `src/L/Hull.lagda.md:125-126`. Whether they carry
this transplant is a measurement for the next brief.

## THIS IS NOT A REFUTATION OF THE TYPE

`levelIn` may still hold by another route. `[LJ-1.160]` closed it from
unpaid `CrossOut` and `HasLevels`
(`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:83-88`). `[LJ-1.121]` did
not refute it (`agents/tasks/LJ-1-121/lj-1.121-report.md:7-8`). D-10:
the hull-language route dies at step 3. The original target is not
recorded as false.

## THE SWEEP (C-42)

This return is not a refutation, so the count is of the named unpaid
shape, not of a false statement.

Shape: `(δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → ⟨ Lset δ ∈ˢ πX ⟩`.

A grep over live `src/` returns exactly nine `levelIn` lines.

COUNT of binders: 4.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:917` | `Condense` parameter |
| `src/L/BoundedSubset.lagda.md:1555` | `Co` restatement |
| `src/L/StageBound.lagda.md:58` | `Instantiation.Co` parameter |
| `src/L/StageBound.lagda.md:84` | truncated `Co` parameter |

COUNT of applied spends as data: 1, at
`src/L/BoundedSubset.lagda.md:1020`, inside `Lβ⊆πX` at `:1012`.

COUNT of pass-down spends as module arguments: 3.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:1560` | `module Cn = HS.Condense levelIn cover` |
| `src/L/StageBound.lagda.md:63` | `module C = BSA.Co levelIn cover` |
| `src/L/StageBound.lagda.md:96` | `module C = I.Co levelIn cover` |

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

The formula. One of these two types, not both:

1. `MissingFormula` (`Probe451.agda:97-100`), a
   `Formula (⊥* {ℓ}) 2` that `wit` can spend.
2. A `Formula Code 1` that `closed` can spend
   (`src/L/Hull.lagda.md:120-123`).

The class-carrier graph `LsetGraphAt` is the source to transplant.
The Relabelling and Parameters machinery is the vehicle. This task
does not pay `cover`.
