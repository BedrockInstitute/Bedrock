{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.Presentation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using
  ( Extensionality; Pairing; Union; PowerSet; Separation )
open import CodedVocabulary 𝒮 using
  ( isKPairΔ; refinesΔ; subsetΔ; subsetAtˢ; prAtˢ; sepAt; sepAt-reading )
import K8.GroundSets
import K8.PartialMaps
import CodedCompletion
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CohenPresentation
  (ext   : Extensionality)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (pair  : Pairing)
  (un    : Union)
  (pow   : PowerSet)
  (sep   : Separation)
  (seed  : S)
  (X Y   : S) where

  module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
  module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
  module CC = CodedCompletion 𝒮

  carrier : S
  carrier = PM.carrier

  private
    orderFormula : Formula S 1
    orderFormula = sepAt
      (∃̇∈ (con carrier) (∃̇∈ (con carrier)
        (prAtˢ (suc (suc zero)) (suc zero) zero
          ∧̇ subsetAtˢ zero (suc zero)))) []

  order : S
  order = GS.separator (GS.product carrier carrier) orderFormula

  order-in : (p q : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩
           → ⟨ subsetΔ q p ⟩ → ⟨ GS.ordered p q ∈ˢ order ⟩
  order-in p q hp hq sub = subst ⟨_⟩
    (sym (GS.separator-spec (GS.product carrier carrier) orderFormula (GS.ordered p q)))
    ( GS.product-in carrier carrier p q hp hq
    , ∣ p , hp , ∣ q , hq , GS.ordered-witness p q , sub ∣₁ ∣₁ )

  order-out : (z : S) → ⟨ z ∈ˢ order ⟩
            → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
                 (⟨ p ∈ˢ carrier ⟩ × ⟨ q ∈ˢ carrier ⟩
                   × ⟨ isKPairΔ z p q ⟩ × ⟨ subsetΔ q p ⟩) ∥₁
  order-out z hz = PT.rec PT.squash₁
    (λ { (p , hp , rest) → PT.rec PT.squash₁
      (λ { (q , hq , kp , sub) → ∣ p , q , hp , hq , kp , sub ∣₁ }) rest })
    (subst ⟨_⟩ (sepAt-reading
      (∃̇∈ (con carrier) (∃̇∈ (con carrier)
        (prAtˢ (suc (suc zero)) (suc zero) zero ∧̇ subsetAtˢ zero (suc zero))))
      [] z)
      (subst ⟨_⟩ (GS.separator-spec (GS.product carrier carrier) orderFormula z) hz .snd))

  order-typed :
    ⟨ ⋀ S (λ z → (z ∈ˢ order) ⇒ ⋁ S (λ p → ⋁ S (λ q →
        (p ∈ˢ carrier) ⊓ ((q ∈ˢ carrier) ⊓ isKPairΔ z p q)))) ⟩
  order-typed z hz = PT.map
    (λ { (p , q , hp , hq , kp , _) → p , ∣ q , hp , hq , kp ∣₁ })
    (order-out z hz)

  refines-spec : (p q : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩
               → refinesΔ order p q ≡ subsetΔ q p
  refines-spec p q hp hq = ⇔toPath forward backward
    where
    forward : ⟨ refinesΔ order p q ⟩ → ⟨ subsetΔ q p ⟩
    forward h = PT.rec (snd (subsetΔ q p)) atPair h
      where
      atPair : Σ[ z ∈ S ] (⟨ z ∈ˢ order ⟩ × ⟨ isKPairΔ z p q ⟩)
             → ⟨ subsetΔ q p ⟩
      atPair (z , hz , kp) = PT.rec (snd (subsetΔ q p))
        (λ { (p' , q' , hp' , hq' , kp' , sub) x hx →
          let c = GS.ordered-components z p q p' q' kp kp' in
          subst (λ t → ⟨ x ∈ˢ t ⟩) (sym (fst c))
            (sub x (subst (λ t → ⟨ x ∈ˢ t ⟩) (snd c) hx)) })
        (order-out z hz)
    backward : ⟨ subsetΔ q p ⟩ → ⟨ refinesΔ order p q ⟩
    backward sub = ∣ GS.ordered p q , order-in p q hp hq sub , GS.ordered-witness p q ∣₁

  presentation : CC.Presentation
  presentation = record
    { carrier = carrier
    ; order = order
    ; order-typed = order-typed
    ; inhabited = ∣ GS.empty , PM.empty-in-carrier ∣₁ }

  module C = CC.Coded presentation

  laws : C.ForcingLaws
  laws = record
    { ≼ᴵ-refl = λ p hp → subst ⟨_⟩ (sym (refines-spec p p hp hp)) (λ x h → h)
    ; ≼ᴵ-trans = λ r q p hr hq hp rq qp → subst ⟨_⟩
        (sym (refines-spec r p hr hp))
        (λ x hx →
          subst ⟨_⟩ (refines-spec r q hr hq) rq x
            (subst ⟨_⟩ (refines-spec q p hq hp) qp x hx)) }
