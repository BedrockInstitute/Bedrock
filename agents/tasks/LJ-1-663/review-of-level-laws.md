# review-of-level-laws: Complete resists at SatAtPacked, not at the witness search

**THIS IS A STOP, AND IT IS THE DELIVERABLE.** The brief orders one term,
`level-laws`, of type

```
Σ[ lf ∈ Formula Code 2 ] (Sound lf × Complete lf)
```

with `Sound` and `Complete` copied from
`agents/tasks/LJ-1-659/Probe659.agda:155-161`. **That term is not in
`Probe663.agda` and this file says why.** The probe is green and carries no
hole (`runs/p-final.out`, exit 0 in 3.75 s at 730,890,240 bytes); the
obligation reads `missing` (`runs/meter-obligation.out`, `1 UNRESOLVED of 1`,
`probe_red=False`); the other eleven names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 11`).

**THE STOP IS NOT "I COULD NOT FIND THE PROOF OF COMPLETE".** Section 2 of
the probe splits Complete. The membership half is built. The satisfaction
half is the wall the campaign has already named, and Agda prints it.

## 1. COMPLETE SPLITS, AND THE MEMBERSHIP HALF IS FREE

`Complete lf` asks for a `v : SL` with `fst v ≡ Lset (fst γ)` and with
`(γ ∷ v ∷ []) ⊨c lf`. The first conjunct does not mention the formula.

Three terms, all green (`runs/meter-names.out`):

| name | line | what it says |
|---|---|---|
| `index-of` | `Probe663.agda:103-106` | an ordinal of the stage is a member of `lam`, by `rank-fix` and `rank-Lset`. |
| `Lset∈suc` | `:110-115` | `Lset γ ∈ Lset (suc γ)`, the EnvSupply spelling of `𝒟ₒ-intro` at `⊤̇` (`src/L/Coding/EnvSupply.lagda.md:127-129`). |
| `value-in-stage` | `:118-123` | `Lset(γ) ∈ Lset lam`, by `succλ` and `Lset-mono`. |
| `packed` / `packed-fst` | `:126-131` | that member, as an `SL`, with first projection `Lset(γ)` by `refl`. |
| `complete-from-sat` | `:144-146` | `SatAtPacked lf → Complete lf`. The packing is the witness. |

**So the truncated existence the brief named as W3 is not a search for
`v`.** The witness is `packed γ oγ`. The truncation is over
`SatAtPacked`:

```
SatAtPacked lf = (γ : SL) (oγ : IsOrd (fst γ))
               → ⟨ (γ ∷ packed γ oγ ∷ []) ⊨c lf ⟩
```

at `Probe663.agda:135-138`.

## 2. AGDA SAYS THE SAME THING IN ITS OWN WORDS

`runs/NO-SAT.agda.txt`, `runs/nosat-2.out`, exit 42 in 3.03 s. The
satisfaction half attempted the only way Section 2 allows: hand the packed
equality through to `_⊨c_`.

```
fst (L.packed γ oγ) ≡ Lset (fst γ) !=<
Cubical.HITs.PropositionalTruncation.Base.∥
Σ (FOL.ZFStructure.ZFStructure.S L.P.ASt.AbsL.𝒮M)
(λ x →
   ⟨
   (x ∷ γ ∷ L.packed γ oγ ∷ []) L.T.AtCode.⊨
   FOL.Manipulation.Relabelling.mapFo L.P.slide
   (FOL.Manipulation.Renaming.renameFo
    (FOL.Manipulation.Renaming.liftρ L.P.swap) L.P.step2)
   ⟩)
∥₁
when checking that the expression L.packed-fst γ oγ has type
⟨ (γ ∷ L.packed γ oγ ∷ []) L.T.⊨c L.delivered ⟩
```

**The equality is not the satisfaction, and the satisfaction is an
existential over a third slot.** Agda unfolded `_⊨c_` of `[LJ-1.651]`'s
`delivered` to `∃̇ (renameFo (liftρ swap) step2)`: a bound `K` in the
stage, then the Δ₀ matrix at environment `(K ∷ γ ∷ Lset(γ) ∷ [])`. That is
Devlin's three-slot Φ with the bound existentially closed, searched inside
`Lset lam`. Nothing in the tree supplies that `K`.

## 3. I DID NOT PROVE THE OBLIGATION'S TYPE FALSE

I proved that Complete's membership conjunct is free, and that its
satisfaction conjunct is the 2.6(ii) wall. A refutation of `SatAtPacked`
or of `Sound` is a different task and this one does not attempt it.
`[LJ-1.494]` drew the same line about `hier-in-stage`
(`agents/tasks/LJ-1-494/review-of-GraphSatAtStage.md:67-69`): the type
forms, the term is not written, the type is not shown false.

`Sound` is uninhabited for the same reason from the other side: the
class-carrier decode is `Lset-only`
(`src/L/Hierarchy.lagda.md:334-335`), and the bounded-to-machine decode
at a real `K` is `HierInK` (`agents/tasks/LJ-1-532/lj-1.532-report.md:171`).
I did not spend this dispatch on a second copy of that wall.

## 4. THE CORRECTED OBLIGATION

Not `level-laws`. It is

```
SatAtPacked delivered
```

at `Probe663.agda:135-138`, with `delivered = P.lset-formula`. Everything
downstream of that one fact plus `[LJ-1.659]`'s `Sound` is already built:
`complete-from-sat` reaches `Complete`, `[LJ-1.659]`'s `level-from-laws`
reaches `LevelFormula`, and `laws-to-coded-cover` reaches `CodedCover`.

The history is `[LJ-1.52]` (`archive/dev/LJ-dispatch-index.md:101`),
`[LJ-1.494]`'s `hier-in-stage`, `[LJ-1.610]` wall 1, `[LJ-1.642]` wall 4.
All four name 2.6(ii): the sequence `(L_δ | δ ≤ γ)` as a member of the
stage. Price the next brief against that record.
