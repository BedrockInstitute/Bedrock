# review-of-hier-in-K-placement: 𝒟ₒ-intro does not reach HierInK at the bridge stage

**VERDICT: NO-GO.** `hier-in-K-placement` is not delivered. The statement
`[LJ-1.532]` named is not false. Stage placement through `𝒟ₒ-intro` does
not inhabit it.

The brief's own stop condition names this case: **NO-GO** earns why
stage placement does not reach `HierInK`, which re-prices
`[LJ-1.684]`'s recipe: that composition stays GO as a hypothesis of
the bridge, and its unpaid membership is still unpaid.

## THE STATEMENT THAT IS NOT INHABITED

`agents/tasks/LJ-1-532/Probe532.agda:274-277`, restated at
`agents/tasks/LJ-1-693/Probe693.agda:77-80`:

    HierInK = (α : V ℓ) → IsLimit α
            → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
            → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

The obligation name `hier-in-K-placement` is absent on purpose
(`Probe693.agda:237-238`). No postulate stands in for it.

`ApproxInK` is not taken. It is FALSE
(`agents/tasks/LJ-1-532/Probe532.agda:206-209`).

## WHY 𝒟ₒ-INTRO DOES NOT REACH IT AT THE BRIDGE STAGE

The bridge wants membership in `Lset α` (`K ≡ Lset α` along `qK`,
`agents/tasks/LJ-1-688/Probe688.agda:86-93`). `𝒟ₒ-intro` at
`A = Lset σ` places `x` in `𝒟ₒ (Lset σ)`, which is `Lset (sucV σ)`
(`src/L/Axioms/Basic.lagda.md:196`). `door-next`
(`Probe693.agda:127-129`) is that row. A carve FROM `Lset α` lands
in `Lset (sucV α)`, which is not `HierInK`.

To land IN `Lset α` the door must fire at a strictly earlier stage:
`ThroughDoor` (`Probe693.agda:135-139`). `from-door`
(`:141-150`) is `ThroughDoor → HierInK`. `ThroughDoor` is not
inhabited.

`AtStage` at a generic ordinal σ, the shape of that bound, still
wants `Δ₀` (`AtBound.wants-Δ₀`, `Probe693.agda:166-171`, ascribed
from `src/L/Axioms/Separation.lagda.md:225-229`). A larger stage
does not drop the hypothesis.

The delivered graph is not `Δ₀` (`no-Δ₀-graph`, `Probe693.agda:194-195`)
and not `Σ₁` (`graph-not-Σ₁`, `:197-198`, imported from
`Probe520.agda:202-204`). The graded substitute is not `Δ₀`
(`no-Δ₀-levelFo`, `Probe693.agda:191-192`). Neither formula feeds
`AtBound.wants-Δ₀`. `σ₁-up`
(`src/FOL/Absoluteness.lagda.md:182-185`) does not apply to
`LsetGraphAt`. `SaysLevel` at `levelFo` is unpaid
(`Probe520.agda:183-188`).

## WHAT STAGE PLACEMENT DOES PAY, AND WHAT IT DOES NOT

`from-HierBelow : HierBelowAll → HierInK` (`Probe693.agda:221-225`)
is green. It is the row `[LJ-1.536]` stated in prose
(`agents/tasks/LJ-1-536/lj-1.536-report.md:171`). It takes
`HierBelowAll` as a hypothesis. `[LJ-1.536]` did not inhabit
`HierBelowAll`. The successor step of `HierBelow` is `AdjoinAt`
(`Probe536.agda:278-280`) and is not rebuilt. The limit collection
is not paid. Room is not the miss: `steps-stay` (`Probe693.agda:214-219`)
is green.

`DOWN` is not a route. `[LJ-1.688]` measured that
(`agents/tasks/LJ-1-688/lj-1.688-report.md:1`). This file does not
rebuild it.

## WHAT THE TREE STILL OWES

The classical fact is Devlin 2.6(ii): the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). The remaining target
beside this NO-GO is `ThroughDoor` (`Probe693.agda:135-139`), or
equivalently `HierBelowAll` (`:92-93`), whose unpaid case is
`HierBelowLimit` (`Probe536.agda:408-409`).

This file does not inhabit `HierInK`. It does not inhabit
`ThroughDoor`. It does not inhabit `HierBelow`. It does not inhabit
`StageHigh`. It does not postulate a bound.

## WHAT I DID NOT DO

I did not inhabit `ApproxInK`. I did not rebuild `Graph.up`. I did
not rebuild `Pin.down`. I did not rebuild `AdjoinAt`. I did not
land anything in `src/`. I postulated nothing.
