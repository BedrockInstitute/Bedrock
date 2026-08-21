# LJ-1.484 review of `cover`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The consumer's type, copied from `src/L/BoundedSubset.lagda.md:918-919`:

```agda
cover : (y : S) → ⟨ y ∈ˢ M ⟩
      → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁
```

The probe restates the site. It does not import the module parameter.
Telescope: `agents/tasks/LJ-1-484/Probe484.agda:44-56`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below `module Condense`
is copied. There is no term named `cover`. The witness meter reports
`1 UNRESOLVED of 1` (`agents/tasks/LJ-1-484/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at D-10 step 4. W3 is GO. The ambient covering is GO and does
not pay the obligation. The W3 type is inhabited:

```agda
code-of : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁
```

at `Probe484.agda:68-69`. Three forced rechecks, exit 0, caliber
`-A64m -I0 -M8g`. Median wall **2.56 s**. Median peak RSS
**471498752 bytes**. `runs/w3-{1,2,3}.out`.

The failing type is well-formed and unbuilt:

```agda
CoverWitnessesInHull :
    (y : S) → ⟨ y ∈ˢ M ⟩
  → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
```

at `Probe484.agda:123-126`. This is an obstruction of the walk from
a hull member to a covering index inside the hull. It is not a
refutation of `cover`. I did not build a term of the negation. I did
not prove the type false.

## WHICH PREMISE MOVED

No predecessor delivered `cover`. `[LJ-1.462]`
(`agents/tasks/LJ-1-462/lj-1.462-report.md:77`) is NO-GO at D-10
step 3 for the sibling `levelIn`. The statement is not named FALSE.
This task does not inhabit `levelIn`. It does not take `levelIn`
as a hypothesis.

`[LJ-1.160]` (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`)
measured that the hull is not transitive. That measurement still
stands.

## THE DECOMPOSITION, AS TYPES

1. Hull membership. GO. Delivered.

       hull-member :
           (x : S) → ⟨ x ∈ˢ Hull ⟩
         → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁

   Site: `src/L/Hull.lagda.md:337-339`. The probe inhabits it as
   `code-of` (`Probe484.agda:68-69`).

2. A stage bound read off a Code. UNBUILT. Wrong shape.

       StageBoundOfCode :
           (c : Code) → Σ[ γ ∈ S ] (IsOrd γ × ⟨ fst (val c) ∈ˢ Lset γ ⟩)

   Site: `Probe484.agda:110-112`. `Code` is `base` or `wit`
   (`src/L/Hull.lagda.md:72-74`). Neither carries an ordinal.

3. Ambient covering at the stage. GO. Not the obligation.

       ambient-cover : (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁

       ambient-level : (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

   Sites: `Probe484.agda:80-82` and `:88-98`. Suppliers:
   `src/L/Constructible.lagda.md:336-337` (`Lset-out`),
   `src/L/Hull.lagda.md:330-331` (`Hull⊆L`),
   `src/L/Axioms/Basic.lagda.md:196` (`Lset-suc`),
   `src/L/Ordinal.lagda.md:96` (`suc-ord`) and `:221` (`mem-ord`).
   The index is in `lam`, not in `M`. The membership is of `y`,
   not of `C.π y`.

4. Witnesses inside the hull. FAIL. This is the literature step.

       CoverWitnessesInHull :
           (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

   Site: `Probe484.agda:123-126`. Devlin transfers
   `∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)` into the hull
   (`dev/literature/devlin-II5.md:107-108`). Ambient covering
   does not give `γ ∈ M`, because the hull is not transitive
   (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). The tree's
   Φ is `LsetGraphAt` at `src/L/Coding/Sequence.lagda.md:349`.
   `wit` takes `Formula (⊥* {ℓ}) (suc k)` at
   `src/L/Hull.lagda.md:74`. Those types do not meet.

5. Membership along the collapse. GO. Both ends in `M`.

       π∈-fwd : (x y : S) → y ∈ᵗ x → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩

   Site: `src/V/Collapse.lagda.md:102-103`. The probe inhabits
   it as `π-mem` (`Probe484.agda:131-132`).

6. The index in the image. GO. The preimage in `M`.

       πX-intro : (y : S) → ⟨ y ∈ˢ X ⟩ → ⟨ π y ∈ˢ πX ⟩

   Site: `src/V/Collapse.lagda.md:86-87`. The probe inhabits it
   as `index-in-image` (`Probe484.agda:137-138`).

7. Decode at the image. Unbuilt. Not reached as a term.

       CoveredAtImage :
           (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd (C.π γ)
                       × ⟨ C.π y ∈ˢ Lset (C.π γ) ⟩) ∥₁

   Site: `Probe484.agda:145-149`. Devlin uses Φ and Σ₀
   absoluteness at the transitive collapse image
   (`dev/literature/devlin-II5.md:102-108`). It does not
   commute `π` with `Lset`.

## THIS IS NOT A REFUTATION OF THE TYPE

`cover` may still hold by another route. D-10: the walk from a
hull member to a covering index inside the hull dies at step 4.
The original target is not recorded as false.

## THE SWEEP (C-42)

This return is not a refutation, so the count is of the named unpaid
shape, not of a false statement. I re-counted on this tree.

Shape: `(y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁`.

COUNT of binders: 4.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:918` | `Condense` parameter |
| `src/L/BoundedSubset.lagda.md:1556` | `Co` restatement |
| `src/L/StageBound.lagda.md:81` | `Instantiation.Co` parameter |
| `src/L/StageBound.lagda.md:107` | truncated `Co` parameter |

COUNT of applied spends as data: 3.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:967` | inside `β-succ` |
| `src/L/BoundedSubset.lagda.md:1002` | inside `πX⊆Lβ` |
| `src/L/BoundedSubset.lagda.md:1606` | inside `x∈Lκ` |

COUNT of pass-down spends as module arguments: 3.

| file:line | what |
|---|---|
| `src/L/BoundedSubset.lagda.md:1560` | `module Cn = HS.Condense levelIn cover` |
| `src/L/StageBound.lagda.md:85` | `module C = BSA.Co levelIn cover` |
| `src/L/StageBound.lagda.md:118` | `module C = I.Co levelIn cover` |

COUNT of other binders named `cover` that are not this shape: 1, at
`src/L/Axioms/Separation.lagda.md:351` (`replaceAt`). That type is
`(z : S) → ⟨ ReplImage a φ z ⟩ → ⟨ fst z ∈ Lset σ ⟩`. It is not
the condensation hypothesis.

COUNT of producers in `src/L/Condensation.lagda.md`: 0. `grep` for
`cover` there returns no match. No producer exists anywhere in live
`src/` for this shape. One producer at the `Condense` level pays
all four live binders, because the three pass-downs sit below
binders of the same shape.

## W2 (DD4)

Every type above is generic in `ℓ`, `lam` and `X`. No ordinal is
fixed. No second copy at a concrete stage.

## WHAT THE NEXT BRIEF MUST ORDER

Not `code-of`. Not a stage bound read off a `Code`. Not
`ambient-cover`. Those three are settled.

One of these, after this measurement:

1. `CoverWitnessesInHull`: a covering index that lies in `M`.
   Do not send `LsetGraphAt` to `wit` without re-measuring the
   formula meeting at this consumer. `[LJ-1.462]` measured that
   meeting for `levelIn`. C-42 forbids the transfer by analogy.
2. A route that does not go through the hull language, and that
   still puts the index in `C.πX`.
3. `CoveredAtImage` only after the index is in `M`. Do not
   commute `π` with `Lset`. Do not take `levelIn` as a
   hypothesis of a `cover` probe.

This task does not pay `levelIn`.
