{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CheckIndexedFamilies {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (choice : OrdinaryProfile.ChoiceSet 𝒮) (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term; var; con; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
import CodedVocabulary
import K7.DefinableFamilies

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )
module CV = CodedVocabulary 𝒮
module Families = K7.DefinableFamilies 𝒮 ext paths pair un pow sep coll find choice seed

module AtCuts (β κ c p : S) (chk : S → S)
  (chkFo : Formula S 2)
  (chk-reading : (u ξ : S) → ⟨ ξ ∈ˢ β ⟩
    → ((u ∷ ξ ∷ []) ⊨ chkFo) ≡ (u ≈ˢ chk ξ))
  (body : Formula S 4)
  (mk : S → Formula S 1 → S)
  (mk-in : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ b ⟩ → ⟨ (a ∷ []) ⊨ θ ⟩ → ⟨ a ∈ˢ mk b θ ⟩)
  (mk-bound : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ mk b θ ⟩ → ⟨ a ∈ˢ b ⟩)
  (mk-sat : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ mk b θ ⟩ → ⟨ (a ∷ []) ⊨ θ ⟩)
  where

  valuesFo : S → Formula S 1
  valuesFo ξ = CV.sepAt body (chk ξ ∷ c ∷ p ∷ [])

  values : S → S
  values ξ = mk κ (valuesFo ξ)

  checkSlots : Fin 2 → Term S 3
  checkSlots zero = var zero
  checkSlots (suc zero) = var (suc (suc zero))

  bodySlots : Fin 4 → Term S 3
  bodySlots zero = var (suc zero)
  bodySlots (suc zero) = var zero
  bodySlots (suc (suc zero)) = con c
  bodySlots (suc (suc (suc zero))) = con p

  memberFo : Formula S 2
  memberFo = var zero ∈̇ con κ ∧̇ ∃̇
    (CV.instFo checkSlots chkFo ∧̇ CV.instFo bodySlots body)

  check-fit : (u a ξ : S) → CV.Fits checkSlots (u ∷ a ∷ ξ ∷ []) (u ∷ ξ ∷ [])
  check-fit u a ξ zero = refl
  check-fit u a ξ (suc zero) = refl

  body-fit : (u a ξ : S)
    → CV.Fits bodySlots (u ∷ a ∷ ξ ∷ []) (a ∷ u ∷ c ∷ p ∷ [])
  body-fit u a ξ zero = refl
  body-fit u a ξ (suc zero) = refl
  body-fit u a ξ (suc (suc zero)) = refl
  body-fit u a ξ (suc (suc (suc zero))) = refl

  member-reading : (a ξ : S) → ⟨ ξ ∈ˢ β ⟩
    → ((a ∷ ξ ∷ []) ⊨ memberFo) ≡ (a ∈ˢ values ξ)
  member-reading a ξ hξ = ⇔toPath to from
    where
    to : ⟨ (a ∷ ξ ∷ []) ⊨ memberFo ⟩ → ⟨ a ∈ˢ values ξ ⟩
    to (ha , witness) = PT.rec (snd (a ∈ˢ values ξ))
      (λ { (u , hc , hb) → mk-in κ (valuesFo ξ) a ha
        (subst ⟨_⟩ (sym (CV.sepAt-reading body (chk ξ ∷ c ∷ p ∷ []) a))
          (subst (λ t → ⟨ (a ∷ t ∷ c ∷ p ∷ []) ⊨ body ⟩)
            (Families.GS.≈→≡ (subst ⟨_⟩
              (CV.⊨-inst checkSlots chkFo (u ∷ a ∷ ξ ∷ []) (u ∷ ξ ∷ [])
                (check-fit u a ξ) ∙ chk-reading u ξ hξ) hc))
            (subst ⟨_⟩ (CV.⊨-inst bodySlots body
              (u ∷ a ∷ ξ ∷ []) (a ∷ u ∷ c ∷ p ∷ []) (body-fit u a ξ)) hb))) }) witness

    from : ⟨ a ∈ˢ values ξ ⟩ → ⟨ (a ∷ ξ ∷ []) ⊨ memberFo ⟩
    from ha = mk-bound κ (valuesFo ξ) a ha , ∣ chk ξ
      , subst ⟨_⟩ (sym (CV.⊨-inst checkSlots chkFo
          (chk ξ ∷ a ∷ ξ ∷ []) (chk ξ ∷ ξ ∷ []) (check-fit (chk ξ) a ξ)
          ∙ chk-reading (chk ξ) ξ hξ))
          (subst ⟨_⟩ (sym (paths (chk ξ) (chk ξ))) refl)
      , subst ⟨_⟩ (sym (CV.⊨-inst bodySlots body
          (chk ξ ∷ a ∷ ξ ∷ []) (a ∷ chk ξ ∷ c ∷ p ∷ []) (body-fit (chk ξ) a ξ)))
          (subst ⟨_⟩ (CV.sepAt-reading body (chk ξ ∷ c ∷ p ∷ []) a)
            (mk-sat κ (valuesFo ξ) a ha)) ∣₁

  memberSlots : Fin 2 → Term S 3
  memberSlots = checkSlots

  setFo : Formula S 2
  setFo = ∀̇ ((var zero ∈̇ var (suc zero) ⇒̇ CV.instFo memberSlots memberFo)
    ∧̇ (CV.instFo memberSlots memberFo ⇒̇ var zero ∈̇ var (suc zero)))

  set-reading : (v ξ : S) → ⟨ ξ ∈ˢ β ⟩
    → ((v ∷ ξ ∷ []) ⊨ setFo) ≡ (v ≈ˢ values ξ)
  set-reading v ξ hξ = ⇔toPath
    (λ h → ext v (values ξ) (λ a →
      (λ ha → subst ⟨_⟩ (reading a) (h a .fst ha)) ,
      (λ ha → h a .snd (subst ⟨_⟩ (sym (reading a)) ha))))
    (λ eq a →
      (λ ha → subst ⟨_⟩ (sym (reading a))
        (subst (λ t → ⟨ a ∈ˢ t ⟩) (Families.GS.≈→≡ eq) ha)) ,
      (λ ha → subst (λ t → ⟨ a ∈ˢ t ⟩) (sym (Families.GS.≈→≡ eq))
        (subst ⟨_⟩ (reading a) ha)))
    where
    reading : (a : S)
      → ((a ∷ v ∷ ξ ∷ []) ⊨ CV.instFo memberSlots memberFo) ≡ (a ∈ˢ values ξ)
    reading a = CV.⊨-inst memberSlots memberFo (a ∷ v ∷ ξ ∷ []) (a ∷ ξ ∷ [])
      (check-fit a v ξ) ∙ member-reading a ξ hξ

  module Family = Families.AtFamily β κ values setFo set-reading
    (λ ξ _ a → mk-bound κ (valuesFo ξ) a)

  open Family public using ( family; family-spec; family-injection; family-witness )
