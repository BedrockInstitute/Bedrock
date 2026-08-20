# LJ-1.408 review of `pair-cross`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch `no-go-stated`
asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-408/Probe408.agda:58-64` states `pair-cross` as the brief
wrote it:

```agda
pair-cross :
    (α : V ℓ) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (s₁ s₂ : sq α)
  → (m₁ c₁ m₂ c₂ : ⟪ α ⟫)
  → fst s₁ (m₁ , c₁) ≡ fst s₂ (m₂ , c₂)
  → (m₁ ≡ m₂) × (c₁ ≡ c₂)
```

This is `pair-inj` at TWO pairings. The consumer's `h-inj` reads `B.pair-inj`
at ONE pairing (`src/L/StageCardinal.lagda.md:382`).

## THE VERDICT

NO-GO, and it is a refutation, not a failed search. The statement is FALSE, and
the refutation is green in Agda.

`pair-cross-refuted` (`Probe408.agda:95-104`) builds a term of the negation of
the stated type, given any pairing `s : sq ω`. It instantiates at `α := ω`,
sets `s₂ := swap-sq ω s` (`:43-52`), and feeds the equation

    fst s (m0 , m1) ≡ fst (swap-sq ω s) (m1 , m0)

which holds by `refl`. The stated conclusion is then `m0 ≡ m1`. The two
numerals `# 0` and `# 1` are members of `ω` (`#∈ω`, `src/L/Ordinal.lagda.md:248`).
If they were equal, `# 0 ∈ˢ # 0`, and `∈-irrefl` kills it
(`src/V/Hierarchy.lagda.md:155-156`). The membership `# 0 ∈ˢ # 1` is
`self∈sucV (# 0)` (`src/V/Model.lagda.md:236`) along `sucV (# 0) ≡ # 1`,
which is `refl` (`Probe408.agda:92-93`).

So in `--safe` cubical, no term of the stated type exists once a pairing at
`ω` is given. The consumer already has that pairing as a module parameter
(`src/L/StageCardinal.lagda.md:17`). The tree also has `squareω : sq ω`
(`src/L/InjChain.lagda.md:184-185`). The probe does not import `InjChain`.

The obligation is left as a hole (`Probe408.agda:64`), red by design, exactly
as `[LJ-1.396]` left `kappa-is-limit` (`agents/tasks/LJ-1-396/Probe396.agda:110`)
and `[LJ-1.404]` left `kappa-infinite` (`agents/tasks/LJ-1-404/Probe404.agda:145`).

## WHY THE STATEMENT IS FALSE

A pairing composed with a swap of its two arguments is again a pairing.
`swap-sq` (`Probe408.agda:43-52`) is that term. At the swapped pairing the
cross-equation holds by `refl`, and `pair-cross` would then force any two
members of an infinite ordinal to be equal. They are not.

`h-inj` (`src/L/StageCardinal.lagda.md:353-382`) survives today because both
packages unpack `B.pair` from ONE `Bound` instance (`:283`), so `B.pair-inj`
(`:71-75`) applies. If the square law were carried inside `class-pred`'s
truncation (`:319-322`), the two packages would carry two pairings, and the
step at `:382` would be `pair-cross`. That step is false.

## THE TYPE THAT WOULD HAVE TO BE CANONICAL

For `h-inj` to survive a truncated pairing, the pairing itself would have to
be a proposition:

    isProp (sq α)

With that, the two packages' pairings would be equal, and `pair-inj` at one
pairing would apply. `sq α` is a Sigma of a function and its injectivity
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). It is not a proposition. The
swap is a second inhabitant whenever one exists.

A weaker type that still saves `h-inj` is the current one: the pairing is
data outside the truncation, so both packages share `B.pair`.

## THE SWEEP, BECAUSE A REFUTATION MEASURES ONE SITE (C-42)

This refutation measures ONE site: `α := ω`, with the swapped pairing.
COUNT of sites in live `src/` that compare two counts under two different
pairings: 0.

Every live `pair-inj` is at one pairing:

- `src/L/StageCardinal.lagda.md:71-72` and `:382`, one `Bound` instance.
- `src/L/BoundedSubset.lagda.md:1439` and the seven call sites that follow,
  one `Bound` instance.
- `src/L/Ordinal/SquareLaw.lagda.md:947-948`, one `pair`.
- `src/FOL/Count.lagda.md:59-60`, the one function `pair` on `ℕ`.

No cure is priced. The consumer needs the pairing as DATA at
`src/L/StageCardinal.lagda.md:283` and `:382`, because `h-inj` compares two
packages with `B.pair-inj` at that one pairing.
