# LJ-1.494 review of `GraphSatAtStage`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The type the brief names, `agents/tasks/LJ-1-494/LJ-1.494.md:11-13`:

```agda
GraphSatAtStage :
    (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
  → ⟨ ((Lset-at δ) ∷ δ ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩
```

No predecessor probe delivered this type. `[LJ-1.492]` is NO-GO at
`CoverWitnessesInHull` (`agents/tasks/LJ-1-492/lj-1.492-report.md:133`).
I did not inhabit that type.

The brief's spelling of `GraphSatAtStage` does not form.

1. `Lset-at` is not a name in live `src/`. Grep finds it only in this
   brief.
2. `LsetGraphAt` is `Formula CS.S n`
   (`src/L/Coding/Sequence.lagda.md:349`).
3. `AbsL.⊨ᵐ` takes `Formula SL n`. `SL = AbsL.SM`
   (`src/L/Hull.lagda.md:153-156`). `𝒮 ↾ M` has carrier
   `Σ[ x ∈ S ] (x ∈ᶜ M)` (`src/FOL/ZFStructure.lagda.md:146`).
4. A map `CS.S → SL` is a total map from `L` into `Lset α`. No such
   map exists. The brief forbids a reflection hypothesis
   (`agents/tasks/LJ-1-494/LJ-1.494.md:100-101`).

The probe restates the obligation name at
`agents/tasks/LJ-1-494/Probe494.agda:67-68` as the W3 type. There is
no term of the brief's type. The witness meter reports
`1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-494/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at W3, the stage membership of the approximation. The W3 type
forms. The W3 term is not written. The obligation term is not
written.

W3, as a type, at `Probe494.agda:49-53`:

```agda
hier-in-stage : Type (ℓ-suc ℓ)
hier-in-stage =
    (δ : CS.S) (oδ : IsOrd (fst δ))
  → ⟨ fst δ ∈ˢ Lset α ⟩
  → ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset α ⟩
```

The brief's spelling `⟨ hierL (fst δ) _ _ ∈ˢ Lset α ⟩` does not form:
`hierL` returns `CS.S` (`src/L/Hierarchy.lagda.md:621`) and `𝒮ᵥ`'s
`∈ˢ` takes `S` (`src/FOL/ZFStructure.lagda.md:48`). The intended
membership is the first projection. Three forced rechecks of the
W3-only file, exit 0, caliber `-A64m -I0 -M8g`. Median wall
**1.93 s**. Median peak RSS **403013632 bytes**. `runs/w3-{1,2,3}.out`.

Nothing in the tree inhabits that type. `hierL` is built by
`hasReplacementL` (`src/L/Hierarchy.lagda.md:595`).
`hasReplacementL` exports no stage bound
(`src/L/Axioms/Full.lagda.md:277-280`). `stage-mem`
(`src/L/Stage.lagda.md:188-189`) places a constructible set in some
stage, not in `Lset α`. I did not postulate the bound. I did not add
a reflection hypothesis. I did not build a term of the negation. I
did not prove the type false.

## WHICH ROUTE IS NEARER, AND WHAT IT LACKS

**Defines direction at `𝒮ʟ` is delivered.** `Lset-defines`
(`src/L/Hierarchy.lagda.md:646-648`) is the same statement at the
class world. Its witness is `hierL δ` (`:656`). That witness is an
element of `𝒮ʟ`. It is not shown to be an element of `Lset α`.

**The stage world is `AbsL.𝒮M`, not `𝒮ʟ`.** `AbsL` is `𝒮ᵥ`
restricted to one stage (`src/L/Hull.lagda.md:153`). The existential
of `GraphAt` (`src/L/Coding/Sequence.lagda.md:291-292`) must be
witnessed inside that stage. That is W3. The tree does not supply it.

**`hull-closed` is not reached.** The critic named `hull-closed`
(`src/L/Hull.lagda.md:415-417`) as the cheapest spelling of the
consumer's hypothesis
(`agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:168-177`). This task
never applies it. The graph side is blocked at W3.

## WHICH PREMISE MOVED

`[LJ-1.492]` (`agents/tasks/LJ-1-492/lj-1.492-report.md:133`) is
NO-GO at `CoverWitnessesInHull` via `closed`. The statement is not
named FALSE. This task does not inhabit `CoverWitnessesInHull`. It
does not rebuild `coverFo`, `code-of` or `ambient-level`.

`[LJ-1.230]` (`agents/tasks/LJ-1-230/lj-1.230-report.md:75-79`)
measured that no master places `hierL` in `Lset`. That measurement
still stands.

`[LJ-1.233]` (`agents/tasks/LJ-1-233/lj-1.233-report.md:287-291`)
measured that `hierL` lands in some stage by `stage-mem`, and that a
bound in terms of the argument is absent. That measurement still
stands.

## WHAT I DID NOT DO

- I did not inhabit `GraphSatAtStage` as the brief spelled it.
- I did not inhabit `hier-in-stage`.
- I did not inhabit `CoverWitnessesInHull` or `cover`.
- I did not take `levelIn` as a hypothesis.
- I did not postulate a stage bound.
- I did not add a reflection hypothesis.
- I did not rebuild `coverFo`, `code-of` or `ambient-level`.
- I did not attempt the only direction.
- I did not import a probe.
- I did not write in `src/`.
