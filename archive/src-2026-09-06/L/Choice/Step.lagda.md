# End extension of the stage orders (retired 2026-09-06)

The `## End extension` section of `src/L/Choice/Step.lagda.md`.
`stepPath` was the chapter's one path induction: the step order at a
birth does not depend on which proof of ordinal-hood it was applied to,
transported over an equality of births.  The section's conclusion was
the anonymous module below it: at two stages `γ ∈ β`, the comparison of
two members of `Lset γ` is EQUAL, not merely equivalent, to their
comparison in `Lset β`, because the comparison mentions only the two
births (`sameBirth`, from `birth-proof`) and the step orders at those
births (`sameStep`, from `stepPath`), and never the stage it is read at.

THE MATERIAL COULD NEVER ACQUIRE A CONSUMER.  `stepPath` was `private`
at top level, and every declaration of the conclusion module was
`private` inside an ANONYMOUS module, so no importer could name any of
it, and nothing else in the file read it.  The recap called the result
`endExtension`; no definition of that name has ever existed in the tree.

```agda
private
  stepPath : (δ : S) (o : IsOrd δ) (δ' : S) (e : δ ≡ δ') (o' : IsOrd δ')
           → PathP (λ k → SWO (New (e k)))
               (stepAt δ (carry (Lset δ) (orderAt δ o)))
               (stepAt δ' (carry (Lset δ') (orderAt δ' o')))
  stepPath δ o δ' e o' = J Motive base e o'
    where
    Motive : (z : S) → δ ≡ z → Type (ℓ-suc (ℓ-suc ℓ))
    Motive z ez = (oz : IsOrd z) → PathP (λ k → SWO (New (ez k)))
      (stepAt δ (carry (Lset δ) (orderAt δ o)))
      (stepAt z (carry (Lset z) (orderAt z oz)))
    base : Motive δ refl
    base oz =
      cong (λ q → stepAt δ (carry (Lset δ) (orderAt δ q))) (isPropIsOrd δ o oz)

module _ (γ β : S) (oγ : IsOrd γ) (oβ : IsOrd β) (i : ⟨ γ ∈ˢ β ⟩) where
  private
    module Fγ = Family γ (λ δ _ → orderAt δ) oγ
    module Fβ = Family β (λ δ _ → orderAt δ) oβ
    open Fγ using () renaming ( _≺_ to _≺ᵍ_ ; bornAt to bornγ )
    open Fβ using () renaming ( _≺_ to _≺ᵇ_ ; bornAt to bornβ )

    up : Mem (Lset γ) → Mem (Lset β)
    up a = a .fst , Lset-mono {α = β} {β = γ} i {x = a .fst} (a .snd)

    sameBirth : (a : Mem (Lset γ)) → bornγ a .fst ≡ bornβ (up a) .fst
    sameBirth a = birth-proof (a .fst) _ _

    sameStep : (a : Mem (Lset γ))
             → PathP (λ k → SWO (New (sameBirth a k)))
                 (Fγ.stepIn (bornγ a)) (Fβ.stepIn (bornβ (up a)))
    sameStep a = stepPath (bornγ a .fst) _ (bornβ (up a) .fst) (sameBirth a) _

    agree : (a b : Mem (Lset γ)) → (a ≺ᵍ b) ≡ (up a ≺ᵇ up b)
    agree a b k = ⟨ sameBirth a k ∈ˢ sameBirth b k ⟩
                ⊎ ( (sameBirth b k ≡ sameBirth a k)
                  × Under (sameBirth a k) (sameStep a k) (a .fst) (b .fst) )
```
