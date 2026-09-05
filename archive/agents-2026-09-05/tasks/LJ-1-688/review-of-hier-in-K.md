# review-of-hier-in-K: DOWN does not reach the membership, and this file is the stop

**VERDICT: NO-GO.** `hier-in-K` is not delivered. The statement `[LJ-1.532]`
named is not false. DOWN at one environment does not inhabit it.

The brief's own stop condition names this case: **NO-GO** earns why
`HierInK` is not reachable at one environment, which re-prices the
bridge itself.

## THE STATEMENT THAT IS NOT INHABITED

`agents/tasks/LJ-1-532/Probe532.agda:274-277`, restated at
`agents/tasks/LJ-1-688/Probe688.agda:59-62`:

    HierInK = (α : V ℓ) → IsLimit α
            → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
            → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

The one-environment form is `HierInKAt`
(`agents/tasks/LJ-1-688/Probe688.agda:86-93`). It is `HierInK`
transported along `fst (lookup K γ) ≡ Lset α`. A BARE `∀K` form is
false if `K` may be empty
(`agents/tasks/LJ-1-684/Probe684.agda:67-72`). This file does not
quantify over every `K`.

`ApproxInK` is not taken. It is FALSE
(`agents/tasks/LJ-1-532/Probe532.agda:206-209`).

## WHY DOWN DOES NOT REACH IT

`Graph.up` (`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:218-222`) drops
the bound. The reverse is `Pin.down`
(`agents/tasks/LJ-1-688/Probe688.agda:156-159`). It is inhabited as
a composition. Its extra premise is the membership of the graph
witness in `K` (`Probe688.agda:151`).

- At an arbitrary witness that premise is `ApproxInK`, which is FALSE.
- At the canonical witness that premise is `HierInKAt`, which is
  `HierInK` along `qK` (`Probe688.agda:97-107`).

DOWN therefore CONSUMES `HierInK`. It does not construct it. The
inner frames `approx-up` / `step-up` and their reverses, and `powK`
(`ProbeLJ1162A.agda:140-141`, `:211-216`), agree the bounded rows
with the unbounded rows. They do not place `hierL β` in a named
stage.

## WHAT THE TREE STILL OWES

The classical fact is Devlin 2.6(ii): the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit `α > ω`
(`dev/literature/devlin-II5.md:221-222`). `[LJ-1.519]` reduced the
limit form to `StageHigh` and `StageLow`. `[LJ-1.536]` reduced
`StageHigh` to `HierBelow` and stopped at the door of `𝒟ₒ-intro`:
the only bridge `AtStage` requires `Δ₀`, and the characterizing
formula of the table is not `Δ₀`
(`agents/tasks/LJ-1-536/review-of-StageHigh.md:23-32`).

`hasReplacementL` builds `hierL` and discards the bound it computes
(`src/L/Axioms/Full.lagda.md:231`, `[LJ-1.233]`).

This file does not inhabit `HierInK`. It does not inhabit `StageHigh`.
It does not inhabit `HierBelow`. It does not postulate a bound.

## WHAT I DID NOT DO

I did not inhabit `ApproxInK`. I did not rebuild `Graph.up`. I did
not rebuild `AdjoinAt`. I did not land anything in `src/`. I
postulated nothing.
