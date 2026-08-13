{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.44] class probe, CONTROL: the two hottest definitions of
-- PropAgree (subB2T and subB2T-back) copied verbatim into a minimal
-- module, with the PropAgree telescope trimmed to what they need.
-- The types carry TWO built formulas (subValB and subValAt) at
-- concrete indices.  Untracked probe, thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ144D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; prAtL-adequate; subValAt
        ; prʟ; prʟ-fst )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The bounded subvalue lookup (copy of the master's subValB).
subValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValB T ar a y K =
  ∃̇∈ (var K) (prAtL zero (suc ar) (suc a)
            ∧̇ appAt (suc T) zero (suc y))

-- The trimmed PropAgree telescope: n, T, the environment and the
-- site fact the back direction needs.
module Mini {n : ℕ} (T : Fin n) (γ : S ^ suc n)
  (keyK : (ar a : S) → ⟨ fst (prʟ ar a) ∈ fst (lookup zero γ) ⟩) where

  keyK₀ : (ar a : S) → ⟨ pr (fst ar) (fst a) ∈ fst (lookup zero γ) ⟩
  keyK₀ ar a = subst (λ w → ⟨ w ∈ fst (lookup zero γ) ⟩) (prʟ-fst ar a) (keyK ar a)

  subB2T : (yb E ya yc b a ar c : S)
    → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValB (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                 (suc (suc (suc (suc (suc (suc zero))))))
                 (suc (suc (suc (suc zero))))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValAt {7 + suc n} (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩
  subB2T yb E ya yc b a ar c h = PT.rec squash₁
    (λ { (z , (zK , (p , a₁))) →
      let p' : ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   prAtL zero (suc (suc (suc (suc (suc (suc zero))))))
                            (suc (suc (suc (suc zero)))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            p
          a₁' : ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                         zero (suc zero) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc T))))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            a₁
      in ∣ z , (p' , a₁') ∣₁ })
    h

  subB2T-back : (yb E ya yc b a ar c : S)
    → ⟨ fst (prʟ ar b) ∈ fst (lookup zero γ) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValAt {7 + suc n} (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩
    → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValB (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                 (suc (suc (suc (suc (suc (suc zero))))))
                 (suc (suc (suc (suc zero))))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
  subB2T-back yb E ya yc b a ar c keyK₀ h = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let p' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero))))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            p
          zK : ⟨ fst z ∈ fst (lookup zero γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup zero γ) ⟩)
                 (prʟ-fst ar b
                  ∙ sym (subst ⟨_⟩ (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p))
                 keyK₀
          a₁' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc T))))))))))
                         zero (suc zero) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc T))))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            a₁
      in ∣ z , (zK , (p' , a₁')) ∣₁ })
    h
