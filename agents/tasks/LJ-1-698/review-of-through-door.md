# review-of-through-door: ThroughDoor is not inhabited

**VERDICT: NO-GO.** `through-door` is not delivered. The statement
`[LJ-1.693]` named is not false. `𝒟ₒ-intro` does fire on a Δ₀
presentation of the delivered pair-graph. The carved set is not
identified with `hierL`, and the bounding stage is not shown to lie
in the bridge's `α`.

The brief's own stop condition names this case: **NO-GO** earns why
the door does not open ThroughDoor, which re-prices the `𝒟ₒ-intro`
route: the route is not retired. The remaining equation is the
identification of the carved set with the table.

## THE STATEMENT THAT IS NOT INHABITED

`agents/tasks/LJ-1-693/Probe693.agda:135-139`, restated as the type
of the missing term:

    ThroughDoor =
        (α : V ℓ) → IsLimit α
      → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
      → ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ α ⟩ × Door (Lset δ) (fst (hierL β hβ oβ))) ∥₁

The obligation name `through-door` is absent on purpose
(`Probe698.agda:188-192`). No postulate stands in for it.

`ApproxInK` is not taken. It is FALSE
(`agents/tasks/LJ-1-532/Probe532.agda:206-209`).

## WHAT 𝒟ₒ-INTRO DOES REACH

`Door` is `𝒟ₒ-intro`'s premise (`Probe693.agda:103-107`). It wants a
`Formula ⟪ Lset δ ⟫ 1` whose `defSet` is the table. It does not want
`Δ₀` (`carve∈𝒟ₒ`, `src/L/Axioms/Separation.lagda.md:198-199`).

`PairGraphAt` (`src/L/Coding/Sequence.lagda.md:328-329`) says `z` is
the pair `(c, L_c)`. Bound by the ordinal and relativized to a stage,
it is `Δ₀` (`recordedΔ₀`, `Probe698.agda:87-88`;
`src/FOL/Manipulation/Relativize.lagda.md:72`). That is the
differently presented `Δ₀` formula `[LJ-1.693]`'s critic did not
exclude (`agents/tasks/LJ-1-693/review-of-LJ-1-693-1.md:125-129`).

`mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`) bounds the
constants of that formula (`bound-of`, `Probe698.agda:97-101`).
`AtStage.carve` at that stage, then `𝒟ₒ-intro` via `carve∈𝒟ₒ`, is
`Carved.carved-door` (`Probe698.agda:128-129`). The door opens on
that carved set.

The empty table is definable by `⊥̇` over any stage
(`empty-door`, `Probe698.agda:173-177`;
`src/L/Axioms/Basic.lagda.md:491-502`). `IsLimit` already has
`∅ ∈ α` (`empty-in-limit`, `Probe698.agda:184-185`).

## WHY THAT IS NOT ThroughDoor

`Carved.carved-door` is `Door (Lset σ) carved` for
`σ = fst (bound-of γ oγ hγ)`. ThroughDoor wants
`Door (Lset δ) (fst (hierL β …))` with `δ ∈ α`.

Two unpaid rows sit between them.

1. **The carved set is not identified with the table.**
   `Carved.carved ≡ fst (hierL γ hγ oγ)` is not proved.
   `AtStage.imageIn` (`src/L/Axioms/Separation.lagda.md:225-229`)
   would connect membership in the carve to outer satisfaction of
   the relativized formula. That satisfaction is not paid. `SaysLevel`
   at `levelFo` remains unpaid (`Probe520.agda:183-188`).
   `Lset-defines` (`src/L/Hierarchy.lagda.md:646-653`) is the
   unbounded graph, not the relativized reading.
2. **The bounding stage is not shown to lie in `α`.**
   `fst (bound-of γ oγ hγ) ∈ α` is not proved. `mkBoundedFo` returns
   some ordinal that holds the constants. It does not return a proof
   that this ordinal is a member of the bridge's bound.

The successor step is not rebuilt. It is `AdjoinAt.adjoin∈`
(`Probe536.agda:278-280`). The limit formula may use the tables
below, which is `LimitDefinableIH` (`Probe579.agda:430-433`).

## WHAT THE TREE STILL OWES

The classical fact is Devlin 2.6(ii): the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`).

The remaining target beside this NO-GO is the pair of unpaid rows
above, or equivalently `LimitDefinableIH`
(`Probe579.agda:430-433`). Do not fund another census of
`LsetGraphAt`'s constants. Do not fund another `Δ₀` check of
`relativize`. Both are green here.

This file does not inhabit `ThroughDoor`. It does not inhabit
`HierInK`. It does not inhabit `HierBelow`. It does not postulate
a bound.

## WHAT I DID NOT DO

I did not inhabit `ApproxInK`. I did not rebuild `Graph.up`. I did
not rebuild `Pin.down`. I did not rebuild `AdjoinAt`. I did not
rebuild `adequacy-bnd`. I did not land anything in `src/`. I
postulated nothing.
