# review-of-carved-is-hier: the equation does not close from `table-sat` alone

**VERDICT: NO-GO.** `carved-is-hier` is not inhabited. The statement is
not false: the model knows it at the frame's earliest stage ([LJ-1.704],
report, five sentences, premise 2 of the brief). What the tree lacks is
one content lemma between the relativized graph satisfaction a carved
member carries and the tower equation `Lset-only` reads. The brief's
NO-GO row names exactly this: the reverse inclusion `704`'s model
argument did not internalize.

## THE STATEMENT THAT IS NOT INHABITED

The brief's type, with `[LJ-1.724]`'s obligation as the only
hypothesis:

    carved-is-hier :
        table-sat
      → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
      → At.carved γ oγ hγ ≡ fst (hierL γ hγ oγ)

`table-sat` is stated at `Probe725.agda:82-87` and is not inhabited.
The obligation name `carved-is-hier` is absent on purpose
(`Probe725.agda:301-310`). No postulate stands in for it.

## WHAT IS REAL, AND TYPECHECKS

1. **The first inclusion costs nothing beyond `table-sat`.**
   `hierL-into-carved` (`Probe725.agda:100-113`): a member of the table
   is `pr c (Lset c)` for `c ∈ γ` (`Recorded`,
   `src/L/Hierarchy.lagda.md:497`), and `table-sat` puts that pair in
   `carved` directly.
2. **A carved member is fully readable.** `carved-member-read`
   (`Probe725.agda:144-224`) turns membership in `carved` into `u ∈ γ`,
   `z ∈ Lset γ`, the pair equation via `prAtL-adequate`
   (`src/L/Coding/Model.lagda.md:125-130`), and one residual conjunct:
   the satisfaction of the RELATIVIZED tower graph
   `relativize (LsetS γ oγ) (LsetGraphAt zero (suc zero))`.
3. **The obligation closes from `table-sat` plus one more input.**
   `carved-is-hier-from` (`Probe725.agda:286-299`) assembles the
   equation from `table-sat` and `stage-read`
   (`Probe725.agda:251-258`). The whole distance is that one input.

## WHY `table-sat` ALONE DOES NOT PAY

The second inclusion needs the residual conjunct's content: from

    ⟨ (z ∷ u ∷ W ∷ []) ⊨ relativize (LsetS γ oγ) (LsetGraphAt zero (suc zero)) ⟩

with `fst u ∈ γ` and `fst z ∈ Lset γ`, conclude
`fst z ≡ Lset (fst u)`. That is `stage-read`.

The tree's graph readings consume the UNRELATIVIZED satisfaction over
`𝒮ᵥ ↾ isL`: `Lset-only` (`src/L/Hierarchy.lagda.md:334-337`) and
`approx-val` (`src/L/Hierarchy.lagda.md:274-277`) each take
`⟨ γ ⊨ LsetGraphAt w b ⟩` / `⟨ γ ⊨ ApproxAt f a ⟩` at
`AbsL._⊨ᵐ_` (`src/L/Hierarchy.lagda.md:79`) with no `relativize` in
the formula.

Three facts locate the wall precisely; none of the three is the
syntax gap.

1. **The syntax gap IS bridged.** `relativize-correct`
   (`src/FOL/Manipulation/Relativize.lagda.md:142-143`) turns the
   conjunct into the `A`-bounded semantics of the unrelativized graph
   at `A = Lset γ`, generic in the structure. A GO report that claims
   no bridge exists would be wrong.
2. **The bounded semantics guards every unbounded ∀ at `A`.**
   `LsetGraphAt` unrolls to `∃̇ (ApproxAt ∧̇ StepAt)` whose unbounded
   quantifiers are `domAt`'s `∀̇` (`src/L/Coding/Base.lagda.md:278-279`),
   `ApproxAt`'s two `∀̇`, and `extAt`'s member-wise `∀`
   (`src/L/Coding/Sequence.lagda.md:119-120`). Under the `A`-bounded
   semantics each instantiates only at members of `A = Lset γ`.
3. **The un-guarded readings instantiate them outside `A`.**
   `approx-val` and `step-Lset` use those ∀ at recorded pairs, whose
   components are members of members of `A` (the approximation `f`
   itself is an `A`-member). Converting needs the members-of-members
   fact for `Lset γ` as a SET. The class-level facts are landed:
   `Lset-out` (`src/L/Constructible.lagda.md:346`) and `Lset-mono`
   (`src/L/Constructible.lagda.md:365`) assemble it, but no landed
   lemma states it, and no landed lemma performs the spine conversion
   over the graph formula.

## PRICE, MEASURED AGAINST THE BRIEF'S ESTIMATE

The brief priced W3, the double inclusion, at 40 to 90 lines. The
delivered assemblies cost 190 in-file lines and show the estimate was
right for everything except the spine. The spine itself re-derives,
in bounded form, content `approx-val` already carries unboundedly: an
∈-induction on the argument plus the transitivity fact, over a formula
with three `∀` sites. That is a new content lemma, not an assembly of
landed readings, and it prices above this brief's W3 budget.

## THE CORRECTED TARGET

Fund `stage-read` as its own obligation, in two halves so the smaller
one is reusable:

1. `Lset-trans-set`: members of members of `Lset γ` lie in `Lset γ`.
   Assembled from `Lset-out` + `Lset-mono` plus the members-of-a-
   definable-subset reading. This half is independent of the graph.
2. The spine: from `relativize A (LsetGraphAt w b)`'s `A`-bounded
   satisfaction, with the environment's members in `A`, to
   `Lset-only`'s unguarded input. Both halves together are
   `stage-read` at `Probe725.agda:251-258`.

The moment that lemma lands, `carved-is-hier-from`
(`Probe725.agda:286-299`) delivers the equation and `[LJ-1.707]`'s
identification hypothesis becomes a report. Nothing else on the route
moves: `the-bound` stays `[LJ-1.705]`'s to deliver.

## WHAT I DID NOT DO

I did not inhabit `carved-is-hier`. I did not inhabit `table-sat`
(`[LJ-1.724]` runs beside this task). I did not inhabit `stage-read`.
I did not land anything in `src/`. I postulated nothing. The probe
carries `--safe` and no hole.
