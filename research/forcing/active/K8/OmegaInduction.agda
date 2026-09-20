{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaInduction
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed : ZFStructure.S 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∨̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; emptyPred; emptyAt; adjoinAt )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finiteFormula; finiteFormula-reading )
import K8.GroundSets
import CardinalBridge
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CB = CardinalBridge 𝒮

omega-induction : (w : S) → ⟨ CB.isOmega w ⟩ → (φ : Formula S 1)
  → ((e : S) → ⟨ e ∈ˢ w ⟩ → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ φ ⟩)
  → ((n s : S) → ⟨ n ∈ˢ w ⟩ → ⟨ (n ∷ []) ⊨ φ ⟩
      → ⟨ s ∈ˢ w ⟩ → ⟨ CB.isSuccOf s n ⟩ → ⟨ (s ∷ []) ⊨ φ ⟩)
  → (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ (n ∷ []) ⊨ φ ⟩
omega-induction w hw φ base step n hn =
  snd (subst ⟨_⟩ (part-spec n) (snd hw part closed n hn))
  where
  opaque
    part : S
    part = GS.separator w φ

    part-spec : (x : S) → (x ∈ˢ part) ≡ ((x ∈ˢ w) ⊓ ((x ∷ []) ⊨ φ))
    part-spec x = GS.separator-spec w φ x

  closed : ⟨ CB.isInductive part ⟩
  closed = PT.map (λ { (e , he , ee) →
      e , subst ⟨_⟩ (sym (part-spec e)) (he , base e he ee) , ee }) (fst (fst hw))
    , λ x hx → PT.map (λ { (s , hs , sx) →
        s , subst ⟨_⟩ (sym (part-spec s))
          (hs , step x s (fst (subst ⟨_⟩ (part-spec x) hx))
            (snd (subst ⟨_⟩ (part-spec x) hx)) hs sx) , sx })
      (snd (fst hw) x (fst (subst ⟨_⟩ (part-spec x) hx)))

omega-members-finite : (w : S) → ⟨ CB.isOmega w ⟩
  → (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ finiteIn w n ⟩
omega-members-finite w hw n hn = subst ⟨_⟩ (finiteFormula-reading w n)
  (omega-induction w hw (finiteFormula w)
    (λ e he ee → subst ⟨_⟩ (sym (finiteFormula-reading w e)) (finite-empty w e ee))
    (λ n s hn ih hs sn → subst ⟨_⟩ (sym (finiteFormula-reading w s))
      (finite-adjoin w s n n (subst ⟨_⟩ (finiteFormula-reading w n) ih) hn sn))
    n hn)

predecessorFormula : S → Formula S 1
predecessorFormula w = emptyAt zero ∨̇
  ∃̇∈ (con w) (adjoinAt (suc zero) zero zero)

predecessorPred : S → S → Ω
predecessorPred w n = emptyPred n ⊔ (⋁ S (λ m → (m ∈ˢ w) ⊓ CB.isSuccOf n m))

predecessor-reading : (w n : S) → ((n ∷ []) ⊨ predecessorFormula w) ≡ predecessorPred w n
predecessor-reading w n = refl

omega-predecessor : (w : S) → ⟨ CB.isOmega w ⟩
  → (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ predecessorPred w n ⟩
omega-predecessor w hw n hn = subst ⟨_⟩ (predecessor-reading w n)
  (omega-induction w hw (predecessorFormula w)
    (λ e he ee → subst ⟨_⟩ (sym (predecessor-reading w e)) ∣ inl ee ∣₁)
    (λ m s hm ih hs sm → subst ⟨_⟩ (sym (predecessor-reading w s))
      ∣ inr ∣ m , hm , sm ∣₁ ∣₁)
    n hn)

