# The skeleton's stage conjunct (retired 2026-09-06)

The `## A skeleton, said as one atom` section of
`src/L/Choice/Internal.lagda.md`, and the `InLimitAt s` conjunct it put
at the head of `NameAt`.  `ωAt` and `ωStage` were the two sealed
elements the graph was satisfied at, `limitGraph` discharged the tower
graph at a variable pair of slots through `Lset-defines`, `InLimitAt`
was the membership atom "the skeleton lies in the limit stage", said
through the sequence chapter's graph at the constant `ωʟ`, and
`InLimitAt-in` was its one introduction.

THE CONJUNCT WAS REDUNDANT, AND ITS ONLY READER SAID SO.  `NameAt-read`
in `src/L/Choice/Adequate.lagda.md` bound it as `hl` and never
mentioned it: the skeleton's membership in the limit stage already
follows from `FreeAt`, whose reading `codeFree-out` hands back a
parameter-free formula `χ` together with `fst (lookup s γ) ≡ fst
(limitCode χ)`, and `limitCode` carries `code∈limit χ` inside it.  So
dropping the conjunct leaves both directions of the adequacy intact:
`NameAt-fill` had one hypothesis fewer to supply, and `NameAt-read` had
nothing to lose.  It leaves `LeastNameAt` intact too, in both
directions: its universal quantifies over `NameAt`, so a weaker
`NameAt` makes `LeastAt-fill`'s obligation wider and `LeastAt-read`'s
instantiation easier, and both go through `NameAt-read` and
`NameAt-fill`, neither of which used the conjunct.

Retired with it: the `Lset-defines` import from `L.Hierarchy`, the
`LsetGraphAt` import from `L.Coding.Sequence`, `LsetS`, `ω-ord` and the
`code∈limit` import in `Adequate`.

```agda
opaque
  ωAt : S
  ωAt = ωʟ

  ωStage : S
  ωStage = LsetS ω ω-ord

  ωAt-fst : fst ωAt ≡ ω
  ωAt-fst = refl

  ωStage-fst : fst ωStage ≡ Lset ω
  ωStage-fst = refl

limitGraph : ∀ {n} (v o : Fin n) (γ : S ^ n)
           → fst (lookup o γ) ≡ ω → fst (lookup v γ) ≡ Lset ω
           → ⟨ γ ⊨ LsetGraphAt v o ⟩
limitGraph v o γ qo qv =
  Lset-defines v o γ (subst IsOrd (sym qo) ω-ord) (qv ∙ cong Lset (sym qo))

InLimitAt : ∀ {n} → Fin n → Formula S n
InLimitAt s = ∃̇ (∃̇ ( (var zero ≐ con ωʟ)
                    ∧̇ ( LsetGraphAt (suc zero) zero
                      ∧̇ (var (sh2 s) ∈̇ var (suc zero)) ) ))

module _ {n : ℕ} (s : Fin n) (γ : S ^ n) where
  InLimitAt-in : ⟨ fst (lookup s γ) ∈ Lset ω ⟩ → ⟨ γ ⊨ InLimitAt s ⟩
  InLimitAt-in h = ∣ ωStage , ∣ ωAt , (ωAt-fst , (gr , held)) ∣₁ ∣₁
    where
    gr : ⟨ (ωAt ∷ ωStage ∷ γ) ⊨ LsetGraphAt (suc zero) zero ⟩
    gr = limitGraph (suc zero) zero (ωAt ∷ ωStage ∷ γ) ωAt-fst ωStage-fst
    held : ⟨ fst (lookup s γ) ∈ fst ωStage ⟩
    held = subst (λ u → ⟨ fst (lookup s γ) ∈ u ⟩) (sym ωStage-fst) h
```

The head of `NameAt` before the cut, and the first hypothesis and the
first component of `NameAt-in`:

```agda
NameAt B C C₀ s a e d =
  InLimitAt s ∧̇ ( FreeAt C₀ s a
                ∧̇ ( (var a ∈̇ con ωʟ)
                  ∧̇ ( envOverAt e a B ∧̇ extAt d (DenoteBody B C s e) ) ) )

  NameAt-in : ⟨ fst (lookup s γ) ∈ Lset ω ⟩
            → ...
  NameAt-in hs hf ha he into back =
    InLimitAt-in s γ hs , (hf , ...)
```

And in `Adequate`, the hypothesis `NameAt-fill` supplied and the
component `NameAt-read` bound and never used:

```agda
      hs : ⟨ fst (lookup s γ) ∈ Lset ω ⟩
      hs = subst (λ u → ⟨ u ∈ Lset ω ⟩) (sym qs) (code∈limit (formula t))

    NameAt-read (hl , (hf , (ha , (he , hd)))) = ...
```

The perf marker the retired code carried: the limit stage's two elements
are sealed; unsealed, checking any term at a satisfaction of the tower
graph over them runs 77 s instead of 1.6 s.
