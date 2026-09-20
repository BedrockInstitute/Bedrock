{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.MapOperations {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import OrdinaryProfile 𝒮 using ( Extensionality; Pairing; Union; PowerSet; Separation )
open import CodedVocabulary 𝒮 using ( isKPairΔ; refinesΔ; subsetΔ; compatibleΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; adjoinPred )
open import K8.MapVocabulary 𝒮 using ( functional; agrees; domainPred )
import K8.GroundSets
import K8.FiniteOperations
import K8.FiniteSets
import K8.PartialMaps
import K8.Presentation
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.HLevels using ( isProp× )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Operations
  (ext   : Extensionality)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (pair  : Pairing) (un : Union) (pow : PowerSet) (sep : Separation)
  (seed X Y : S) where

  module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
  module FO = K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
  module FS = K8.FiniteSets 𝒮 ext paths pow sep
  module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
  module CP = K8.Presentation.CohenPresentation 𝒮 ext paths pair un pow sep seed X Y

  refines-mono : (f g x y : S) → ⟨ subsetΔ f g ⟩
               → ⟨ refinesΔ f x y ⟩ → ⟨ refinesΔ g x y ⟩
  refines-mono f g x y sub = PT.map λ { (z , hz , kp) → z , sub z hz , kp }

  functional-hereditary : (f g : S) → ⟨ subsetΔ f g ⟩
                         → ⟨ functional X Y g ⟩ → ⟨ functional X Y f ⟩
  functional-hereditary f g sub fun x hx y hy z hz h =
    fun x hx y hy z hz (refines-mono f g x y sub (h .fst) ,
                         refines-mono f g x z sub (h .snd))

  join-refines : (f g x y : S)
    → refinesΔ (GS.join f g) x y ≡ (refinesΔ f x y ⊔ refinesΔ g x y)
  join-refines f g x y = ⇔toPath forward backward
    where
    forward : ⟨ refinesΔ (GS.join f g) x y ⟩
            → ⟨ refinesΔ f x y ⊔ refinesΔ g x y ⟩
    forward = PT.rec (snd (refinesΔ f x y ⊔ refinesΔ g x y)) λ
      { (w , hw , kp) → PT.map
          (λ { (inl h) → inl ∣ w , h , kp ∣₁
             ; (inr h) → inr ∣ w , h , kp ∣₁ })
          (subst ⟨_⟩ (GS.join-spec f g w) hw) }
    backward : ⟨ refinesΔ f x y ⊔ refinesΔ g x y ⟩
             → ⟨ refinesΔ (GS.join f g) x y ⟩
    backward = PT.rec (snd (refinesΔ (GS.join f g) x y)) λ
      { (inl h) → refines-mono f (GS.join f g) x y
          (λ w hw → subst ⟨_⟩ (sym (GS.join-spec f g w)) ∣ inl hw ∣₁) h
      ; (inr h) → refines-mono g (GS.join f g) x y
          (λ w hw → subst ⟨_⟩ (sym (GS.join-spec f g w)) ∣ inr hw ∣₁) h }

  functional-join : (f g : S) → ⟨ functional X Y f ⟩ → ⟨ functional X Y g ⟩
                  → ⟨ agrees X Y f g ⟩ → ⟨ functional X Y (GS.join f g) ⟩
  functional-join f g ff fg agr x hx y hy z hz h =
    PT.rec (snd (y ≈ˢ z)) cases
      (PT.map2 _,_ (subst ⟨_⟩ (join-refines f g x y) (h .fst))
                    (subst ⟨_⟩ (join-refines f g x z) (h .snd)))
    where
    cases : (⟨ refinesΔ f x y ⟩ ⊎ ⟨ refinesΔ g x y ⟩)
          × (⟨ refinesΔ f x z ⟩ ⊎ ⟨ refinesΔ g x z ⟩) → ⟨ y ≈ˢ z ⟩
    cases (inl fy , inl fz) = ff x hx y hy z hz (fy , fz)
    cases (inl fy , inr gz) = agr x hx y hy z hz (fy , gz)
    cases (inr gy , inl fz) =
      subst ⟨_⟩ (sym (paths y z))
        (sym (subst ⟨_⟩ (paths z y) (agr x hx z hz y hy (fz , gy))))
    cases (inr gy , inr gz) = fg x hx y hy z hz (gy , gz)

  join-in-carrier : (f g : S) → ⟨ f ∈ˢ PM.carrier ⟩ → ⟨ g ∈ˢ PM.carrier ⟩
                  → ⟨ agrees X Y f g ⟩ → ⟨ GS.join f g ∈ˢ PM.carrier ⟩
  join-in-carrier f g hf hg agr = subst ⟨_⟩ (sym (PM.carrier-spec (GS.join f g)))
    ( FO.finite-join PM.W f g (fst (subst ⟨_⟩ (PM.carrier-spec f) hf))
                               (fst (subst ⟨_⟩ (PM.carrier-spec g) hg))
    , functional-join f g (snd (subst ⟨_⟩ (PM.carrier-spec f) hf))
                          (snd (subst ⟨_⟩ (PM.carrier-spec g) hg)) agr )

  compatible→agrees : (p q : S) → ⟨ p ∈ˢ PM.carrier ⟩ → ⟨ q ∈ˢ PM.carrier ⟩
                    → ⟨ compatibleΔ PM.carrier CP.order p q ⟩ → ⟨ agrees X Y p q ⟩
  compatible→agrees p q hp hq h x hx y hy z hz pq = PT.rec (snd (y ≈ˢ z)) step h
    where
    step : Σ[ r ∈ S ] (⟨ r ∈ˢ PM.carrier ⟩ ×
             (⟨ refinesΔ CP.order r p ⟩ × ⟨ refinesΔ CP.order r q ⟩)) → ⟨ y ≈ˢ z ⟩
    step (r , hr , rp , rq) =
      snd (subst ⟨_⟩ (PM.carrier-spec r) hr) x hx y hy z hz
        ( refines-mono p r x y (subst ⟨_⟩ (CP.refines-spec r p hr hp) rp) (pq .fst)
        , refines-mono q r x z (subst ⟨_⟩ (CP.refines-spec r q hr hq) rq) (pq .snd))

  agrees→compatible : (p q : S) → ⟨ p ∈ˢ PM.carrier ⟩ → ⟨ q ∈ˢ PM.carrier ⟩
                    → ⟨ agrees X Y p q ⟩ → ⟨ compatibleΔ PM.carrier CP.order p q ⟩
  agrees→compatible p q hp hq agr =
    ∣ GS.join p q , join-in-carrier p q hp hq agr
    , subst ⟨_⟩ (sym (CP.refines-spec (GS.join p q) p
        (join-in-carrier p q hp hq agr) hp))
        (λ z hz → subst ⟨_⟩ (sym (GS.join-spec p q z)) ∣ inl hz ∣₁)
    , subst ⟨_⟩ (sym (CP.refines-spec (GS.join p q) q
        (join-in-carrier p q hp hq agr) hq))
        (λ z hz → subst ⟨_⟩ (sym (GS.join-spec p q z)) ∣ inr hz ∣₁) ∣₁

  compatible-iff-agrees : (p q : S) → ⟨ p ∈ˢ PM.carrier ⟩ → ⟨ q ∈ˢ PM.carrier ⟩
    → compatibleΔ PM.carrier CP.order p q ≡ agrees X Y p q
  compatible-iff-agrees p q hp hq =
    ⇔toPath (compatible→agrees p q hp hq) (agrees→compatible p q hp hq)

  opaque
    point : S → S → S
    point x y = GS.singleton (GS.ordered x y)

    point-eq : (x y : S) → point x y ≡ GS.singleton (GS.ordered x y)
    point-eq x y = refl

    point-spec : (x y z : S)
      → (z ∈ˢ point x y) ≡ (z ≈ˢ GS.ordered x y)
    point-spec x y z = ⇔toPath
      (GS.singleton-witness (GS.ordered x y) .snd z)
      (λ e → subst (λ w → ⟨ w ∈ˢ point x y ⟩)
        (sym (GS.≈→≡ e))
        (GS.pairOf-inˡ (GS.ordered x y) (GS.ordered x y)))

  point-refines : (x y : S) → ⟨ refinesΔ (point x y) x y ⟩
  point-refines x y =
    ∣ GS.ordered x y , subst ⟨_⟩ (sym (point-spec x y (GS.ordered x y)))
        (subst ⟨_⟩ (sym (paths (GS.ordered x y) (GS.ordered x y))) refl)
    , GS.ordered-witness x y ∣₁

  opaque
   ordered-components-cut : (p a b a' b' : S)
     → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ p a' b' ⟩
     → (a ≡ a') × (b ≡ b')
   ordered-components-cut = GS.ordered-components

  opaque
   point-components : (x y u v : S) → ⟨ refinesΔ (point x y) u v ⟩
                   → (u ≡ x) × (v ≡ y)
   point-components x y u v h = PT.rec
    (isProp× (isSetS u x) (isSetS v y)) step h
    where
    step : Σ[ z ∈ S ] (⟨ z ∈ˢ point x y ⟩ × ⟨ isKPairΔ z u v ⟩)
         → (u ≡ x) × (v ≡ y)
    step (z , hz , kp) = ordered-components-cut (GS.ordered x y) u v x y
      (subst (λ w → ⟨ isKPairΔ w u v ⟩)
        (GS.≈→≡ (subst ⟨_⟩ (point-spec x y z) hz)) kp)
      (GS.ordered-witness x y)

  opaque
   point-functional : (x y : S) → ⟨ functional X Y (point x y) ⟩
   point-functional x y u hu v hv w hw h =
    subst ⟨_⟩ (sym (paths v w))
      (snd (point-components x y u v (h .fst))
       ∙ sym (snd (point-components x y u w (h .snd))))

  opaque
   point-finite : (x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
               → ⟨ finiteIn PM.W (point x y) ⟩
   point-finite x y hx hy =
    FS.finite-adjoin PM.W (point x y) GS.empty (GS.ordered x y)
      (FS.finite-empty PM.W GS.empty (λ z hz → GS.empty-out z hz))
      (GS.product-in X Y x y hx hy) witness
    where
    witness : ⟨ adjoinPred (point x y) GS.empty (GS.ordered x y) ⟩
    witness =
        subst ⟨_⟩ (sym (point-spec x y (GS.ordered x y)))
          (subst ⟨_⟩ (sym (paths (GS.ordered x y) (GS.ordered x y))) refl)
      , (λ z hz → Empty.rec* (GS.empty-out z hz))
      , (λ z hz → ∣ inr (subst ⟨_⟩ (point-spec x y z) hz) ∣₁)

  opaque
   point-in-carrier : (x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
                   → ⟨ point x y ∈ˢ PM.carrier ⟩
   point-in-carrier x y hx hy = subst ⟨_⟩ (sym (PM.carrier-spec (point x y)))
    (point-finite x y hx hy , point-functional x y)

  fresh-agrees : (p x y : S) → ⟨ p ∈ˢ PM.carrier ⟩
               → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
               → (⟨ x ∈ˢ PM.domain p ⟩ → ⟨ ⊥ ⟩)
               → ⟨ agrees X Y p (point x y) ⟩
  fresh-agrees p x y hp hx hy fresh u hu v hv w hw h =
    Empty.rec* (fresh domainMember)
    where
    c : (u ≡ x) × (w ≡ y)
    c = point-components x y u w (h .snd)
    atX : ⟨ refinesΔ p x v ⟩
    atX = subst (λ t → ⟨ refinesΔ p t v ⟩) (c .fst) (h .fst)
    domainMember : ⟨ x ∈ˢ PM.domain p ⟩
    domainMember = PM.domain-in p x v hx hv atX

  insert : S → S → S → S
  insert p x y = GS.join p (point x y)

  insert-in-carrier : (p x y : S) → ⟨ p ∈ˢ PM.carrier ⟩
                    → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
                    → (⟨ x ∈ˢ PM.domain p ⟩ → ⟨ ⊥ ⟩)
                    → ⟨ insert p x y ∈ˢ PM.carrier ⟩
  insert-in-carrier p x y hp hx hy fresh =
    join-in-carrier p (point x y) hp (point-in-carrier x y hx hy)
      (fresh-agrees p x y hp hx hy fresh)

  insert-extends : (p x y : S) → ⟨ subsetΔ p (insert p x y) ⟩
  insert-extends p x y z hz =
    subst ⟨_⟩ (sym (GS.join-spec p (point x y) z)) ∣ inl hz ∣₁

  insert-evaluates : (p x y : S) → ⟨ refinesΔ (insert p x y) x y ⟩
  insert-evaluates p x y = subst ⟨_⟩
    (sym (join-refines p (point x y) x y)) ∣ inr (point-refines x y) ∣₁
