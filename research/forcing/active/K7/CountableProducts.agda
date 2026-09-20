{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CountableProducts
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ )
import CardinalBridge
import K8.FinitePigeonhole
import K8.DiagonalOrder
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module FP = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module CU = FP.CU
module GS = FP.GS
module CO = FP.CO
open CU using ( Ref; refAt; refAt-reading; ref-single; ref-injective; ref-range )

pattern i0 = zero
pattern i1 = suc i0
pattern i2 = suc i1
pattern i3 = suc i2
pattern i4 = suc i3
pattern i5 = suc i4

module ProductMap (A B C D f g : S)
  (hf : ⟨ CB.isInjection f A C ⟩)
  (hg : ⟨ CB.isInjection g B D ⟩)
  where

  Body : S → S → S → S → S → S → Ω
  Body q p a b c d = isKPairΔ p a b ⊓
    (isKPairΔ q c d ⊓ (Ref f a c ⊓ Ref g b d))

  bodyFormula : Formula S 6
  bodyFormula = prAtˢ i5 i3 i2 ∧̇
    (prAtˢ i4 i1 i0 ∧̇
      (refAt (con f) (var i3) (var i1) ∧̇ refAt (con g) (var i2) (var i0)))

  body-reading : (q p a b c d : S)
    → ((d ∷ c ∷ b ∷ a ∷ q ∷ p ∷ []) ⊨ bodyFormula) ≡ Body q p a b c d
  body-reading q p a b c d = cong (isKPairΔ p a b ⊓_)
    (cong (isKPairΔ q c d ⊓_) (cong₂ _⊓_
      (refAt-reading (con f) (var i3) (var i1) (d ∷ c ∷ b ∷ a ∷ q ∷ p ∷ []))
      (refAt-reading (con g) (var i2) (var i0) (d ∷ c ∷ b ∷ a ∷ q ∷ p ∷ []))))

  Coordinate : S → S → Ω
  Coordinate q p = ⋁ S (λ a → (a ∈ˢ A) ⊓
    ⋁ S (λ b → (b ∈ˢ B) ⊓
    ⋁ S (λ c → (c ∈ˢ C) ⊓
    ⋁ S (λ d → (d ∈ˢ D) ⊓ Body q p a b c d))))

  coordinateFormula : Formula S 2
  coordinateFormula = ∃̇∈ (con A) (∃̇∈ (con B)
    (∃̇∈ (con C) (∃̇∈ (con D) bodyFormula)))

  coordinate-reading : (q p : S)
    → ((q ∷ p ∷ []) ⊨ coordinateFormula) ≡ Coordinate q p
  coordinate-reading q p = cong (⋁ S) (funExt (λ a → cong ((a ∈ˢ A) ⊓_)
    (cong (⋁ S) (funExt (λ b → cong ((b ∈ˢ B) ⊓_)
    (cong (⋁ S) (funExt (λ c → cong ((c ∈ˢ C) ⊓_)
    (cong (⋁ S) (funExt (λ d → cong ((d ∈ˢ D) ⊓_)
      (body-reading q p a b c d))))))))))))

  use-coordinate : (q p : S) (P : Ω)
    → ((a b c d : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ C ⟩ → ⟨ d ∈ˢ D ⟩
      → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c d ⟩
      → ⟨ Ref f a c ⟩ → ⟨ Ref g b d ⟩ → ⟨ P ⟩)
    → ⟨ Coordinate q p ⟩ → ⟨ P ⟩
  use-coordinate q p P k = PT.rec (snd P) (λ { (a , ha , h) →
    PT.rec (snd P) (λ { (b , hb , h) →
    PT.rec (snd P) (λ { (c , hc , h) →
    PT.rec (snd P) (λ { (d , hd , kp , kq , rf , rg) →
      k a b c d ha hb hc hd kp kq rf rg }) h }) h }) h })

  total : (p : S) → ⟨ p ∈ˢ GS.product A B ⟩
    → ⟨ ⋁ S (λ q → (q ∈ˢ GS.product C D) ⊓ Coordinate q p) ⟩
  total p hp = PT.rec (snd target)
    (λ { (a , b , ha , hb , kp) → PT.rec (snd target)
      (λ { (c , rf) → PT.map (λ { (d , rg) → GS.ordered c d
        , GS.product-in C D c d (ref-range f A C a c hf rf) (ref-range g B D b d hg rg)
        , ∣ a , ha , ∣ b , hb , ∣ c , ref-range f A C a c hf rf ,
          ∣ d , ref-range g B D b d hg rg , kp , GS.ordered-witness c d , rf , rg ∣₁ ∣₁ ∣₁ ∣₁ })
        (hg .snd .fst b hb) }) (hf .snd .fst a ha) }) (GS.product-out A B p hp)
    where
    target : Ω
    target = ⋁ S (λ q → (q ∈ˢ GS.product C D) ⊓ Coordinate q p)

  single : (p q r : S) → ⟨ Coordinate q p ⟩ → ⟨ Coordinate r p ⟩ → ⟨ q ≈ˢ r ⟩
  single p q r h k = use-coordinate q p (q ≈ˢ r) first h
    where
    first : (a b c d : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ C ⟩ → ⟨ d ∈ˢ D ⟩
      → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c d ⟩
      → ⟨ Ref f a c ⟩ → ⟨ Ref g b d ⟩ → ⟨ q ≈ˢ r ⟩
    first a b c d ha hb hc hd kp kq rf rg = use-coordinate r p (q ≈ˢ r) second k
      where
      second : (a' b' c' d' : S) → ⟨ a' ∈ˢ A ⟩ → ⟨ b' ∈ˢ B ⟩ → ⟨ c' ∈ˢ C ⟩ → ⟨ d' ∈ˢ D ⟩
        → ⟨ isKPairΔ p a' b' ⟩ → ⟨ isKPairΔ r c' d' ⟩
        → ⟨ Ref f a' c' ⟩ → ⟨ Ref g b' d' ⟩ → ⟨ q ≈ˢ r ⟩
      second a' b' c' d' ha' hb' hc' hd' kp' kr rf' rg' = subst ⟨_⟩ (sym (paths q r))
        (GS.ordered-unique q c d kq ∙ cong₂ GS.ordered ec ed ∙ sym (GS.ordered-unique r c' d' kr))
        where
        ab : (a ≡ a') × (b ≡ b')
        ab = GS.ordered-components p a b a' b' kp kp'
        ec : c ≡ c'
        ec = GS.≈→≡ (ref-single f a c c' (hf .fst) rf
          (subst (λ t → ⟨ Ref f t c' ⟩) (sym (ab .fst)) rf'))
        ed : d ≡ d'
        ed = GS.≈→≡ (ref-single g b d d' (hg .fst) rg
          (subst (λ t → ⟨ Ref g t d' ⟩) (sym (ab .snd)) rg'))

  injective : (p q r : S) → ⟨ Coordinate q p ⟩ → ⟨ Coordinate q r ⟩ → ⟨ p ≈ˢ r ⟩
  injective p q r h k = use-coordinate q p (p ≈ˢ r) first h
    where
    first : (a b c d : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ C ⟩ → ⟨ d ∈ˢ D ⟩
      → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c d ⟩
      → ⟨ Ref f a c ⟩ → ⟨ Ref g b d ⟩ → ⟨ p ≈ˢ r ⟩
    first a b c d ha hb hc hd kp kq rf rg = use-coordinate q r (p ≈ˢ r) second k
      where
      second : (a' b' c' d' : S) → ⟨ a' ∈ˢ A ⟩ → ⟨ b' ∈ˢ B ⟩ → ⟨ c' ∈ˢ C ⟩ → ⟨ d' ∈ˢ D ⟩
        → ⟨ isKPairΔ r a' b' ⟩ → ⟨ isKPairΔ q c' d' ⟩
        → ⟨ Ref f a' c' ⟩ → ⟨ Ref g b' d' ⟩ → ⟨ p ≈ˢ r ⟩
      second a' b' c' d' ha' hb' hc' hd' kr kq' rf' rg' = subst ⟨_⟩ (sym (paths p r))
        (GS.ordered-unique p a b kp ∙ cong₂ GS.ordered ea eb ∙ sym (GS.ordered-unique r a' b' kr))
        where
        cd : (c ≡ c') × (d ≡ d')
        cd = GS.ordered-components q c d c' d' kq kq'
        ea : a ≡ a'
        ea = GS.≈→≡ (ref-injective f A C a c a' hf rf
          (subst (λ t → ⟨ Ref f a' t ⟩) (sym (cd .fst)) rf'))
        eb : b ≡ b'
        eb = GS.≈→≡ (ref-injective g B D b d b' hg rg
          (subst (λ t → ⟨ Ref g b' t ⟩) (sym (cd .snd)) rg'))

  module Graph = FP.Graph (GS.product A B) (GS.product C D) coordinateFormula

  product-injection : ⟨ CB.isInjection Graph.graph (GS.product A B) (GS.product C D) ⟩
  product-injection = Graph.injection
    (λ p hp → PT.map (λ { (q , hq , h) → q , hq ,
      subst ⟨_⟩ (sym (coordinate-reading q p)) h }) (total p hp))
    (λ p q r h k → single p q r
      (subst ⟨_⟩ (coordinate-reading q p) h) (subst ⟨_⟩ (coordinate-reading r p) k))
    (λ p q r h k → injective p q r
      (subst ⟨_⟩ (coordinate-reading q p) h) (subst ⟨_⟩ (coordinate-reading q r) k))

injectable-products : (A B C D : S) → ⟨ CB.injectable A C ⟩ → ⟨ CB.injectable B D ⟩
  → ⟨ CB.injectable (GS.product A B) (GS.product C D) ⟩
injectable-products A B C D = PT.rec (isPropΠ (λ _ → snd target))
  (λ { (f , hf) → PT.map (λ { (g , hg) →
    ProductMap.Graph.graph A B C D f g hf hg , ProductMap.product-injection A B C D f g hf hg }) })
  where
  target : Ω
  target = CB.injectable (GS.product A B) (GS.product C D)

module AtOmega (lem : LEM ℓ) (w : S) (hw : ⟨ CB.isOmega w ⟩) where
  module Diagonal = K8.DiagonalOrder.AtOmega 𝒮 ext paths pair un pow sep coll find seed lem w hw

  countable-product : (A B : S) → ⟨ CB.injectable A w ⟩ → ⟨ CB.injectable B w ⟩
    → ⟨ CB.injectable (GS.product A B) w ⟩
  countable-product A B ha hb = CO.injectable-trans sep coll pair
    (GS.product A B) (GS.product w w) w (injectable-products A B w w ha hb)
    Diagonal.omega-square-injection
