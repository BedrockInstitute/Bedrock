# review-of-bound-in-alpha: the bounding stage is not shown in alpha

**VERDICT: NO-GO.** `bound-in-alpha` is not delivered. The statement
`[LJ-1.698]` named as the second unpaid row is not shown false.
`mkBoundedFo` is total and its stage is the `bound2`-tree of the
stages of the formula's constants. Those constants are the ordinal,
the stage `Lset γ`, and numerals. The membership
`fst (bound-of γ oγ hγ) ∈ α` is not proved.

The brief's own stop condition names this case: **NO-GO** earns
whether the separation bound escapes the limit. It does not escape
by ω: `arityNumAtL` names `ωʟ`
(`src/L/Coding/CodeSet.lagda.md:187`), and `isCodeAt` uses
`keyArityAtL`, not `arityNumAtL`
(`src/L/Coding/Powerset.lagda.md:298`). The bound is not shown to
lie in `α` either. The `𝒟ₒ-intro` route still owes this row.

## THE STATEMENT THAT IS NOT INHABITED

`agents/tasks/LJ-1-698/lj-1.698-report.md:42`, restated as the type
of the missing term (`Probe705.agda`, `the-type`):

    (α : V ℓ) → IsLimit α
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → ⟨ γ ∈ α ⟩
  → ⟨ fst (bound-of γ oγ hγ) ∈ α ⟩

The obligation name `bound-in-alpha` is absent on purpose. No
postulate stands in for it.

`ApproxInK` is not taken. It is FALSE
(`agents/tasks/LJ-1-532/Probe532.agda:206-209`).
`ThroughDoor` is not inhabited. `[LJ-1.698]` remains NO-GO there.

## WHAT THE TREE ALREADY GIVES

`bound-of` (`Probe698.agda:97-101`) is `mkBoundedFo` of
`relativize (LsetS γ oγ) (recordedFo (γ , hγ))`. Total at
`src/L/Axioms/Separation.lagda.md:449`.

`mkBoundedTm (con c)` is `stage` of that constant
(`src/L/Axioms/Separation.lagda.md:432-433`). A branching node
merges by `bound2` (`src/L/Ordinal.lagda.md:185-187`), which is
`⋃ (sett (Lift Bool) (sucV ∘ f))`.

`empty-in-limit` (`Probe698.agda:184-185`) places `∅` in every
`IsLimit` bound. A numeral `# n` is reached from `∅` by `n`
successors, so it lies in every `IsLimit`.

`ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434-435`) places an
ordinal in `Lset (sucV γ)`. `Lset γ ∈ 𝒟ₒ (Lset γ)` by `𝒟ₒ-intro`
with `⊤̇` (`src/L/Axioms/Basic.lagda.md:157-158`), and
`Lset-suc` (`:195`) identifies that with `Lset (sucV γ)`. So both
`stage(γ)` and `stage(Lset γ)` sit at or below `sucV γ`.

## WHY THAT IS NOT bound-in-alpha

The recursion on the formula needs one lemma: a limit that contains
`σ₁` and `σ₂` contains `bound2 σ₁ σ₂`. That lemma did not close.

1. **The 698 cone plus the lemma heap-walled.** `runs/p-14.out`:
   EXIT=1, 77.56 s, 1,826,455,552 bytes, `time: command terminated
   abnormally`, peak footprint 2,012,579,856 bytes, against the
   2,147,483,648-byte wide cap. The shape was restructured in this
   dispatch (owner 2026-08-23).
2. **The trimmed frame did not convert.** `runs/p-21.out`:
   `⁅ sucV σ₁ , sucV σ₂ ⁆ ≡ sett (Lift Bool) g` is not `refl`
   (`UnequalTerms` at `Probe705.agda` of that run). `runs/p-26.out`:
   `bound2 σ₁ σ₂ o₁ o₂ .fst ≡ boundingOrd ... .fst` is not `refl`,
   because `L.Ordinal.f` is not the locally defined `f`.
3. **No term of the negation was built.** The D-10 killer (ω as a
   constant of this formula) did not fire.

The remaining cut is therefore two smaller rows, not a rebuilt
`Δ₀` check and not another `mkBoundedFo` totality check:

- `⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆ ∈ α` for `IsLimit α` and `σᵢ ∈ α`,
  by `pairing-ax` (`src/L/Constructible.lagda.md:113`).
- `bound2 σ₁ σ₂ o₁ o₂ .fst ≡ ⋃ ⁅ sucV σ₁ , sucV σ₂ ⁆`, which is
  the conversion this dispatch did not get.

## WHAT THE TREE STILL OWES

The classical fact is Devlin 2.6(ii): the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`). This file asks only
whether the bounding stage of the formula lies in `α`. That row
is still unpaid. `[LJ-1.704]`'s carved-set identification is
independent and is not this stop.

This file does not inhabit `bound-in-alpha`. It does not inhabit
`ThroughDoor`. It does not inhabit `HierInK`. It does not
postulate a bound.

## WHAT I DID NOT DO

I did not inhabit `ApproxInK`. I did not rebuild `Carved`. I did
not rebuild `Pin.down`. I did not rebuild `adequacy-bnd`. I did
not land anything in `src/`. I postulated nothing.
