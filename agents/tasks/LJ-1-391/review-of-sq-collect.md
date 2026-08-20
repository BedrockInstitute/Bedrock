# LJ-1.391 review of `sq-collect`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-391/Probe391.agda:226-230` states `sq-collect` exactly as
the brief writes it: a pointwise mere square law over the band becomes a
mere whole square law.

```agda
sq-collect : ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                         → ∥ sq δ ∥₁)
           → ∥ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                          → sq δ) ∥₁
```

The companion `sq-collect-suffices` (`Probe391.agda:75-85`) is green.

## THE VERDICT

**NO-GO, and the failure is at ONE step.**

- **`sq-collect-suffices` is YES.** Instantiating `L.StageCardinal` at the
  untruncated family and reading `Upper.stage-card-upper` under one `∣_∣₁`
  types (`Probe391.agda:75-85`).
- **Digest 2.7 is YES.** If the collection were paid, the truncated consumer
  would be served (`ac-composes`, `Probe391.agda:93-100`), because that
  consumer's goal is a proposition.
- **C-54 is measured, and it does not pay the residue.** `EndomapAt`
  (`Probe391.agda:153-156`) is equivalent to `PointwiseUntrunc` by two green
  terms (`:158-160`, `:162-165`). Paying the `2-Constant` endomap IS paying
  the collection.
- **`sq-collect` is NO.** The body is that reduction with the endomap as the
  hole (`Probe391.agda:230`). The file's ONLY error is the unsolved meta at
  that hole, exit 42, `[UnsolvedInteractionMetas]` at `:230.58-73`.

## WHICH STEP FAILS, AND WHAT WOULD CLOSE IT

**The failing step.** Produce a `2-Constant` endomap of `sq δ` at a generic
band member, or equivalently untruncate `∥ sq δ ∥₁` to `sq δ` pointwise.
That is HoTT Book 3.8.1, the axiom of choice, at this index type
(`dev/literature/truncation-and-selection.md:223-227`).

**Why `lem` does not close it.** `LEM (ℓ-suc ℓ)` decides propositions
(`src/L/StageCardinal.lagda.md:15`, spent as `extract` at `:419-420` with
`pA : isProp A`). `sq δ` is a `Σ` over a function type
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`) and is a set, not a proposition
(`agents/tasks/LJ-1-319/SqIsSet.agda:37-41`).

**Why the tree's one untruncation device does not close it.** `leastOf`
demands a payload in `A → hProp` (`src/L/WellOrder/Base.lagda.md:158-160`).
No delivered SWO in `src/` has the ambient pairing type as carrier. The
transfer device `pullOrder` (`src/L/Choice/Step.lagda.md:226-242`) would
need an injection of that function type into a coded carrier, which is the
door `[LJ-1.386]` measured.

**What WOULD close it, and the tree holds neither.**

1. A `2-Constant` endomap of `sq δ` as data, so `rec→Set` applies. This is
   Kraus et al. Theorem 16 and law C-54. It is not refuted here. It is
   unpaid.
2. A well-order on the pairing graphs, so `leastOf` applies. Classically
   this is `<_L`. Building it is the AC tower, not a step around the door.

A choice principle packaged as a module parameter would be admissible
under D2 (`archive/dev/DECISIONS-archived.md:30`). Whether to add one is
the owner's call. This file does not make it.

## THE SITE (C-42)

This NO-GO measures one site: the generic parameter `α₀` of
`L.StageCardinal`. It does not measure how far the shape extends. It does
not run `α₀ = ω`.
