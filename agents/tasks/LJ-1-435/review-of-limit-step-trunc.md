# LJ-1.435 review of `limit-step-trunc`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch `no-go-stated`
asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-435/Probe435.agda:149-153` states `limit-step-trunc` as the
brief wrote it:

```agda
limit-step-trunc :
    (α : S) → ⟨ α ∈ˢ sucV α₀ ⟩ → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
  → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
```

It is the chapter's `limit-step` (`src/L/StageCardinal.lagda.md:396-400`) with
the branch family truncated pointwise and the conclusion truncated once. The
pairing stays data at `sq α α∈suc infα` (`:283`).

## THE VERDICT

NO-GO, and it is a refutation of the counting step that injectivity needs, not
a failed search. The value half is GO. The injectivity half needs `CntCross`
(`Probe435.agda:166-175`), and that type is FALSE.

The chapter's `h-inj` closes with `cnt-inj` at ONE injection
(`src/L/StageCardinal.lagda.md:390`). With the branch witness carried in
`class-pred'`, the two opened witnesses carry `g₁` and `g₂`. After
`B.pair-inj` identifies the stage indices (`:382`), the remaining equation is

    fb β oβ infβ pairing g₁ φ ≡ fb β oβ infβ pairing g₂ ψ

and the conclusion that the chapter needs is `φ ≡ ψ`. That is `CntCross`.
The tree does not deliver it. `cnt-inj` is `snd (B.formula-bound g)` at one
`g` (`:292`).

`cnt-cross-refuted` (`Probe435.agda:347-353`) builds a term of the negation
of `CntCross`, given any pairing at `ω`. The site is `β := ω`. `K` is
`Lift {ℓ-zero} {ℓ} Bool`. `g₁` sends `lift false` to `m0` and `lift true`
to `m1`. `g₂` is the swap. `φ₀` is `var 0 ≐ con (lift false)` and `ψ₀` is
the same with `lift true`. `encTm` ignores the constant value
(`src/FOL/Count.lagda.md:284-285`), so the shapes match. `tuple-g g₁` of
the duplicated `lift false` equals `tuple-g g₂` of the duplicated
`lift true`, because `g₂ (lift true) ≡ m0 ≡ g₁ (lift false)`. `CntCross`
would then force `φ₀ ≡ ψ₀`, hence `lift false ≡ lift true`.
`false≢true` kills it.

The obligation is left as a hole (`Probe435.agda:153`), red by design,
exactly as `[LJ-1.408]` left `pair-cross`
(`agents/tasks/LJ-1-408/Probe408.agda:64`).

The value half does not need this step. `h-trunc` (`Probe435.agda:132-141`)
typechecks. `leastOf` over `class-pred'` still runs, because the predicate
is already an hProp by `squash₁`.

## WHY THE STATEMENT'S COUNTING FAILS

`formula-bound` encodes a formula's constants by `tuple-g g`
(`src/L/StageCardinal.lagda.md:100-103, 177-185`). Two injections that
agree on no element can still send two different constants to the same
packed value. The count then collides, and the formulas are not equal.

`h-inj` survives today because both packages unpack `cnt m` from ONE
family `ih` (`:289, :390`). If the branch witness moved inside
`class-pred`'s truncation (`:319-323`), the two packages would carry two
injections, and the step at `:390` would be `CntCross`. That step is
false.

This does not say that `limit-step-trunc` is false as a type. It says the
chapter's counting cannot inhabit it. No other inhabitant was built.

## THE TYPE THAT WOULD HAVE TO BE CANONICAL

For `h'-inj` to survive a pointwise truncated branch family along this
counting, the count would have to be injective across injections:

    CntCross

With that, the two packages' formulas would be equal after transport, and
`defset-stable` would close as it does today. `CntCross` is false. An
injection is a Sigma of a function and its injectivity. It is not a
proposition. A swap of two distinct members is a second inhabitant
whenever the domain has two members.

A weaker type that still saves `h-inj` is the current one: the branch
family is data outside the truncation, so both packages share `ih m` at
each index.

## THE SWEEP, BECAUSE A REFUTATION MEASURES ONE SITE (C-42)

This refutation measures ONE site: `β := ω`, with two injections of
`Lift Bool` and two atomic equalities. COUNT of sites in live `src/` that
compare `formula-bound` at two different injections: 0.

Every live spend of `formula-bound` is at one injection:

- `src/L/StageCardinal.lagda.md:289` and `:292`, one `ih m` per index.
- `src/L/StageCardinal.lagda.md:177-185`, the definition.

`[LJ-1.408]` measured the pairing's site. This measures the branch
injection's site. They are two sites. C-42 forbids transferring that
refutation here. Both are now measured.

No cure is priced. The consumer needs the branch family as DATA at
`src/L/StageCardinal.lagda.md:289` and `:390`, because `h-inj` compares
two packages with `cnt-inj` at one injection.
