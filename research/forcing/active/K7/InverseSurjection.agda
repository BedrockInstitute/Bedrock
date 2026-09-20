{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.InverseSurjection
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (mem-congˡ : (x y z : ZFStructure.S 𝒮) → ⟨ ZFStructure._≈ˢ_ 𝒮 x y ⟩
    → ZFStructure._∈ˢ_ 𝒮 x z ≡ ZFStructure._∈ˢ_ 𝒮 y z)
  (mem-congʳ : (x y z : ZFStructure.S 𝒮) → ⟨ ZFStructure._≈ˢ_ 𝒮 y z ⟩
    → ZFStructure._∈ˢ_ 𝒮 x y ≡ ZFStructure._∈ˢ_ 𝒮 x z)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import OrdinaryProfile 𝒮 using ( Pairing; Separation; Collection )
open import Base.Classical using ( LEM )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K7.CardinalOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder 𝒮
module Order = CO.Order ext mem-congˡ mem-congʳ
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open Order using ( ≈-refl; ≈-sym; ≈-trans; mem-inˡ; kpair-subst )

-- All equalities in this construction are structure equalities. In particular,
-- the carrier can be the names of an extension, whose equal denotations need
-- not be equal names. Collection and Separation supply the graph as a set.

pairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairAt p x y = renameFo emb CB.PairφK
  where
  emb : Fin 3 → _
  emb zero = p
  emb (suc zero) = x
  emb (suc (suc zero)) = y

pair-reading : ∀ {n} (p x y : Fin n) (γ : S ^ n)
  → (γ ⊨ pairAt p x y) ≡ CB.isKPair (lookup p γ) (lookup x γ) (lookup y γ)
pair-reading p x y γ = Ren.⊨-rename emb CB.PairφK γ
  (lookup p γ ∷ lookup x γ ∷ lookup y γ ∷ []) agrees
  ∙ CB.PairφK-bridge (lookup p γ) (lookup x γ) (lookup y γ)
  where
  emb : Fin 3 → _
  emb zero = p
  emb (suc zero) = x
  emb (suc (suc zero)) = y
  agrees : Ren.Agrees emb γ (lookup p γ ∷ lookup x γ ∷ lookup y γ ∷ [])
  agrees zero = refl
  agrees (suc zero) = refl
  agrees (suc (suc zero)) = refl

Ref : S → S → S → Ω
Ref f x y = ⋁ S (λ p → (p ∈ˢ f) ⊓ CB.isKPair p x y)

refAt : ∀ {n} → S → Fin n → Fin n → Formula S n
refAt f x y = ∃̇∈ (con f) (pairAt zero (suc x) (suc y))

ref-reading : ∀ {n} (f : S) (x y : Fin n) (γ : S ^ n)
  → (γ ⊨ refAt f x y) ≡ Ref f (lookup x γ) (lookup y γ)
ref-reading f x y γ = cong (⋁ S) (funExt (λ p → cong ((p ∈ˢ f) ⊓_)
  (pair-reading zero (suc x) (suc y) (p ∷ γ))))

ref-cong : (f x x' y y' : S) → ⟨ x ≈ˢ x' ⟩ → ⟨ y ≈ˢ y' ⟩
  → ⟨ Ref f x y ⟩ → ⟨ Ref f x' y' ⟩
ref-cong f x x' y y' ex ey = PT.map
  (λ { (p , hp , kp) → p , hp , kpair-subst p x x' y y' ex ey kp })

module AtInjection
  (lem : LEM ℓ) (pair : Pairing) (sep : Separation) (coll : Collection)
  (A B u f : S) (hu : ⟨ u ∈ˢ A ⟩) (hf : ⟨ CB.isInjection f A B ⟩)
  where

  -- Only the image of A is inverted. The injection definition permits extra
  -- graph entries, which must not suppress the default branch on B \ f[A].

  Image : S → Ω
  Image x = ⋁ S (λ y → (y ∈ˢ A) ⊓ Ref f y x)

  imageAt : ∀ {n} → Fin n → Formula S n
  imageAt x = ∃̇∈ (con A) (refAt f zero (suc x))

  image-reading : ∀ {n} (x : Fin n) (γ : S ^ n)
    → (γ ⊨ imageAt x) ≡ Image (lookup x γ)
  image-reading x γ = cong (⋁ S) (funExt (λ y → cong ((y ∈ˢ A) ⊓_)
    (ref-reading f zero (suc x) (y ∷ γ))))

  Inverse : S → S → Ω
  Inverse x y = (y ∈ˢ A) ⊓ (Ref f y x ⊔ ((Image x ⇒ ⊥) ⊓ (y ≈ˢ u)))

  inverseAt : ∀ {n} → Fin n → Fin n → Formula S n
  inverseAt x y = (var y ∈̇ con A) ∧̇
    (refAt f y x ∨̇ ((¬̇ imageAt x) ∧̇ (var y ≐ con u)))

  inverse-reading : ∀ {n} (x y : Fin n) (γ : S ^ n)
    → (γ ⊨ inverseAt x y) ≡ Inverse (lookup x γ) (lookup y γ)
  inverse-reading x y γ = cong ((lookup y γ ∈ˢ A) ⊓_)
    (cong₂ _⊔_ (ref-reading f y x γ)
      (cong (_⊓ (lookup y γ ≈ˢ u)) (cong (_⇒ ⊥) (image-reading x γ))))

  inverse-cong : (x x' y y' : S) → ⟨ x ≈ˢ x' ⟩ → ⟨ y ≈ˢ y' ⟩
    → ⟨ Inverse x y ⟩ → ⟨ Inverse x' y' ⟩
  inverse-cong x x' y y' ex ey (hy , h) = mem-inˡ y y' A ey hy
    , PT.map
      (λ { (inl r) → inl (ref-cong f y y' x x' ey ex r)
         ; (inr (n , e)) → inr
             ((λ im → n (PT.map
               (λ { (z , hz , r) → z , hz
                 , ref-cong f z z x' x (≈-refl z) (≈-sym x x' ex) r }) im))
             , ≈-trans y' y u (≈-sym y y' ey) e) }) h

  inverse-total : (x : S) → ⟨ ⋁ S (Inverse x) ⟩
  inverse-total x with lem (Image x)
  ... | inl h = PT.map (λ { (y , hy , r) → y , hy , ∣ inl r ∣₁ }) h
  ... | inr n = ∣ u , hu , ∣ inr ((λ h → Empty.rec (n h)) , ≈-refl u) ∣₁ ∣₁

  inverse-single : (x y z : S) → ⟨ Inverse x y ⟩ → ⟨ Inverse x z ⟩
    → ⟨ y ≈ˢ z ⟩
  inverse-single x y z (hy , h) (hz , k) = PT.rec (snd (y ≈ˢ z))
    (λ { (inl r) → PT.rec (snd (y ≈ˢ z))
         (λ { (inl s) → PT.rec (snd (y ≈ˢ z))
              (λ { (p , hp , kp) → PT.rec (snd (y ≈ˢ z))
                (λ { (q , hq , kq) → hf .snd .snd .snd p hp q hq y x z (kp , kq) }) s }) r
            ; (inr (n , _)) → Empty.rec* (n ∣ y , hy , r ∣₁) }) k
       ; (inr (n , e)) → PT.rec (snd (y ≈ˢ z))
         (λ { (inl s) → Empty.rec* (n ∣ z , hz , s ∣₁)
            ; (inr (_ , d)) → ≈-trans y u z e (≈-sym z u d) }) k }) h

  graphFormula : Formula S 2
  graphFormula = ∃̇ (pairAt (suc zero) (suc (suc zero)) zero
    ∧̇ inverseAt (suc (suc zero)) zero)

  graph-reading : (w x : S) → ((w ∷ x ∷ []) ⊨ graphFormula)
    ≡ ⋁ S (λ y → CB.isKPair w x y ⊓ Inverse x y)
  graph-reading w x = cong (⋁ S) (funExt (λ y → cong₂ _⊓_
    (pair-reading (suc zero) (suc (suc zero)) zero (y ∷ w ∷ x ∷ []))
    (inverse-reading (suc (suc zero)) zero (y ∷ w ∷ x ∷ []))))

  graph-total : (x : S) → ⟨ x ∈ˢ B ⟩
    → ⟨ ⋁ S (λ w → (w ∷ x ∷ []) ⊨ graphFormula) ⟩
  graph-total x _ = PT.rec (snd (⋁ S (λ w → (w ∷ x ∷ []) ⊨ graphFormula)))
    (λ { (y , h) → PT.map
      (λ { (w , kp) → w , subst ⟨_⟩ (sym (graph-reading w x)) ∣ y , kp , h ∣₁ })
      (Order.kpairOf pair x y) }) (inverse-total x)

  module AtGraph (g : S) (hg : ⟨ Order.GraphSpec B graphFormula g ⟩) where

    entry : (w x y : S) → ⟨ w ∈ˢ g ⟩ → ⟨ CB.isKPair w x y ⟩
      → ⟨ Inverse x y ⟩
    entry w x y hw kp = PT.rec (snd (Inverse x y))
      (λ { (b , hb , sat) → PT.rec (snd (Inverse x y))
        (λ { (v , kq , h) → inverse-cong b x v y
          (Order.kpair-components pair w b v x y kq kp .fst)
          (Order.kpair-components pair w b v x y kq kp .snd) h })
        (subst ⟨_⟩ (graph-reading w b) sat) }) (hg .fst w hw)

    relation : ⟨ CB.isRelation g ⟩
    relation w hw = PT.rec (snd (⋁ S (λ x → ⋁ S (λ y → CB.isKPair w x y))))
      (λ { (x , _ , sat) → PT.map (λ { (y , kp , _) → x , ∣ y , kp ∣₁ })
        (subst ⟨_⟩ (graph-reading w x) sat) }) (hg .fst w hw)

    function : ⟨ CB.isFunction g ⟩
    function = relation , λ p hp q hq x y z (kp , kq) →
      inverse-single x y z (entry p x y hp kp) (entry q x z hq kq)

    domain : ⟨ Order.DomClause g B ⟩
    domain x hx = PT.rec (snd (⋁ S (λ y → Ref g x y)))
      (λ { (w , hw , sat) → PT.map (λ { (y , kp , _) → y , ∣ w , hw , kp ∣₁ })
        (subst ⟨_⟩ (graph-reading w x) sat) }) (hg .snd x hx)

    onto : (y : S) → ⟨ y ∈ˢ A ⟩
      → ⟨ ⋁ S (λ x → ⋁ S (λ w → (x ∈ˢ B) ⊓ ((w ∈ˢ g) ⊓ CB.isKPair w x y))) ⟩
    onto y hy = PT.rec (snd tgt)
      (λ { (x , r) → PT.rec (snd tgt)
        (λ { (p , hp , kp) → PT.rec (snd tgt)
          (λ { (w , hw , sat) → PT.rec (snd tgt)
            (λ { (z , kq , h) → ∣ x , ∣ w
              , hf .snd .snd .fst p hp y x kp , hw
              , kpair-subst w x x z y (≈-refl x)
                  (inverse-single x z y h (hy , ∣ inl r ∣₁)) kq ∣₁ ∣₁ })
            (subst ⟨_⟩ (graph-reading w x) sat) })
          (hg .snd x (hf .snd .snd .fst p hp y x kp)) }) r })
      (hf .snd .fst y hy)
      where
      tgt : Ω
      tgt = ⋁ S (λ x → ⋁ S (λ w → (x ∈ˢ B) ⊓ ((w ∈ˢ g) ⊓ CB.isKPair w x y)))

    surjection : ⟨ CO.isSurjection g B A ⟩
    surjection = function , domain , (λ w hw x y kp → entry w x y hw kp .fst) , onto

  inverse-surjection : ⟨ CO.surjectable B A ⟩
  inverse-surjection = PT.map
    (λ { (g , hg) → g , AtGraph.surjection g hg })
    (Order.graphOf sep coll B graphFormula graph-total)

injectable-surjectable : LEM ℓ → Pairing → Separation → Collection
  → (A B u : S) → ⟨ u ∈ˢ A ⟩ → ⟨ CB.injectable A B ⟩ → ⟨ CO.surjectable B A ⟩
injectable-surjectable lem pair sep coll A B u hu = PT.rec (snd (CO.surjectable B A))
  (λ { (f , hf) → AtInjection.inverse-surjection lem pair sep coll A B u f hu hf })
