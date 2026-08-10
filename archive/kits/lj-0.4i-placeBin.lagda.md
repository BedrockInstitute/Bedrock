# LJ-0.4i kit: placeBin, refused on measurement

The `placeBin` helper was built for `src/FOL/Manipulation/Parameters.lagda.md`
and typechecked, then reverted. The measured net was plus 1 (179 to 180),
so the per-file staging rule reverted it alone. This file preserves the kit
as required by the kit-preservation rule.

The block replaces the three propositional clauses of `⊨-place`
(`src/FOL/Manipulation/Parameters.lagda.md:376-390` in today's tree):

```agda
    mutual
      placeBin : ∀ {n k} (φ ψ : Formula K n) (op : Ω → Ω → Ω)
               → (θ : Fin (countFo (φ ∧̇ ψ)) → Fin (n + k))
               → (γ : S ^ n) (σ : S ^ k)
               → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo (φ ∧̇ ψ))))
               → op (γ ⊨ φ) (γ ⊨ ψ)
                 ≡ op ((γ ++ σ) ⊨₀ placeFo φ (λ i → θ (padRight (countFo ψ) i)))
                      ((γ ++ σ) ⊨₀ placeFo ψ (λ j → θ (padLeft (countFo φ) j)))
      placeBin φ ψ op θ γ σ h = cong₂ op
        (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
          (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
        (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
          (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))

      ⊨-place (φ ∧̇ ψ) θ γ σ h = placeBin φ ψ _⊓_ θ γ σ h
      ⊨-place (φ ∨̇ ψ) θ γ σ h = placeBin φ ψ _⊔_ θ γ σ h
      ⊨-place (φ ⇒̇ ψ) θ γ σ h = placeBin φ ψ _⇒_ θ γ σ h
```

The kit cost 12 in-fence lines (the `mutual` line, a 7-line signature and a
4-line body). The three clauses it served were 5 lines each; after the fold
they were 1 line each. The measured saving was 12 against a kit of 12, and
the file net was plus 1. The break-even is 12 over 4, or 3.0, which equals
the site count, and the net is not negative.
