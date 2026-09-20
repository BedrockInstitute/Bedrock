{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaPairing
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
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( sepAt; sepAt-reading; subsetΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import OrdinaryProfile 𝒮 using ( iff; foundation→minimal )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import K8.GroundSets
import K8.FiniteEnumeration
import K8.FinitePigeonhole
import K8.OmegaInduction
import K8.OmegaFinite
import K7.CardinalOrder
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module GD = GroundDescription 𝒮 ext paths
module FE = K8.FiniteEnumeration 𝒮 ext paths pair un pow sep find seed
module FP = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module OF = K8.OmegaFinite 𝒮 ext paths pair un pow sep find seed
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z h → cong (_∈ˢ z) (GS.≈→≡ h))
  (λ x y z h → cong (x ∈ˢ_) (GS.≈→≡ h))
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open CB using ( _↔̇_ )
open FP using ( MinimumBound )

injectableAt : ∀ {n} → Fin n → Fin n → Formula S n
injectableAt a b = renameFo emb CB.Injectableφ
  where
  emb : Fin 2 → _
  emb zero = a
  emb (suc zero) = b

injectableAt-reading : ∀ {n} (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ injectableAt a b) ≡ CB.injectable (lookup a γ) (lookup b γ)
injectableAt-reading a b γ = Ren.⊨-rename emb CB.Injectableφ γ
  (lookup a γ ∷ lookup b γ ∷ []) agrees ∙ CB.Injectable-bridge (lookup a γ) (lookup b γ)
  where
  emb : Fin 2 → _
  emb zero = a
  emb (suc zero) = b
  agrees : Ren.Agrees emb γ (lookup a γ ∷ lookup b γ ∷ [])
  agrees zero = refl
  agrees (suc zero) = refl

minimumFormula : Formula S 2
minimumFormula = injectableAt (suc zero) zero ∧̇
  ∀̇∈ (var zero) (¬̇ (injectableAt (suc (suc zero)) zero))

minimum-reading : (A n : S) → ((n ∷ A ∷ []) ⊨ minimumFormula) ≡ MinimumBound A n
minimum-reading A n = cong₂ _⊓_ (injectableAt-reading (suc zero) zero (n ∷ A ∷ []))
  (cong (⋀ S) (funExt (λ m → cong ((m ∈ˢ n) ⇒_)
    (cong (_⇒ ⊥) (injectableAt-reading (suc (suc zero)) zero (m ∷ n ∷ A ∷ []))))))

module AtOmega (lem : LEM ℓ) (w : S) (hw : ⟨ CB.isOmega w ⟩) where

  boundFormula : S → Formula S 1
  boundFormula A = sepAt (injectableAt (suc zero) zero) (A ∷ [])

  opaque
    bounds : S → S
    bounds A = GS.separator w (boundFormula A)

    bounds-spec : (A n : S) → (n ∈ˢ bounds A) ≡ ((n ∈ˢ w) ⊓ CB.injectable A n)
    bounds-spec A n = GS.separator-spec w (boundFormula A) n
      ∙ cong ((n ∈ˢ w) ⊓_)
        (sepAt-reading (injectableAt (suc zero) zero) (A ∷ []) n
          ∙ injectableAt-reading (suc zero) zero (n ∷ A ∷ []))

  minimum-exists : (X A : S) → ⟨ finiteIn X A ⟩
    → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ MinimumBound A n) ⟩
  minimum-exists X A fin = PT.map finish
    (foundation→minimal find lem (bounds A)
      (PT.map (λ { (n , hn , inj) → n , subst ⟨_⟩ (sym (bounds-spec A n)) (hn , inj) })
        (FE.finite-size-bound lem w hw X A fin)))
    where
    finish : Σ[ n ∈ S ] ⟨ (n ∈ˢ bounds A) ⊓
      (⋀ S (λ m → ((m ∈ˢ n) ⊓ (m ∈ˢ bounds A)) ⇒ ⊥)) ⟩
      → Σ[ n ∈ S ] ⟨ (n ∈ˢ w) ⊓ MinimumBound A n ⟩
    finish (n , hn , least) = n , nw , inj , λ m mn im → least m
      (mn , subst ⟨_⟩ (sym (bounds-spec A m))
        (OI.omega-members-finite w hw n nw .fst m mn , im))
      where
      nw : ⟨ n ∈ˢ w ⟩
      nw = subst ⟨_⟩ (bounds-spec A n) hn .fst
      inj : ⟨ CB.injectable A n ⟩
      inj = subst ⟨_⟩ (bounds-spec A n) hn .snd

  minimum-unique : (A n m : S) → ⟨ n ∈ˢ w ⟩ → ⟨ m ∈ˢ w ⟩
    → ⟨ MinimumBound A n ⟩ → ⟨ MinimumBound A m ⟩ → ⟨ n ≈ˢ m ⟩
  minimum-unique A n m hn hm hmin hmin' = PT.rec (snd (n ≈ˢ m))
    (λ { (inl nm) → Empty.rec* (hmin' .snd n nm (hmin .fst))
       ; (inr rest) → PT.rec (snd (n ≈ˢ m))
           (λ { (inl eq) → eq ; (inr mn) → Empty.rec* (hmin .snd m mn (hmin' .fst)) }) rest })
    (CO.ord-compare find sep lem n m (OF.omega-members-ordinal w hw n hn)
      (OF.omega-members-ordinal w hw m hm))

  module FiniteInitialOrder
    (P : S) (lt : S → S → Ω) (ltFormula : Formula S 2)
    (lt-reading : (p q : S) → ((p ∷ q ∷ []) ⊨ ltFormula) ≡ lt p q)
    (initial : S → S)
    (initial-spec : (p z : S) → (z ∈ˢ initial p) ≡ ((z ∈ˢ P) ⊓ lt z p))
    (initial-finite : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ finiteIn P (initial p) ⟩)
    (trichotomy : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩
      → ⟨ lt p q ⊔ ((p ≈ˢ q) ⊔ lt q p) ⟩)
    (transitive : (p q r : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ r ∈ˢ P ⟩
      → ⟨ lt p q ⟩ → ⟨ lt q r ⟩ → ⟨ lt p r ⟩)
    (irreflexive : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ lt p p ⟩ → Empty.⊥)
    where

    liftIndex : Fin 2 → Fin 3
    liftIndex zero = zero
    liftIndex (suc zero) = suc (suc zero)

    initialFormula : Formula S 2
    initialFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
      ((var zero ∈̇ con P) ∧̇ renameFo liftIndex ltFormula))

    IsInitial : S → S → Ω
    IsInitial d p = ⋀ S (λ z → iff (z ∈ˢ d) ((z ∈ˢ P) ⊓ lt z p))

    initial-reading : (d p : S) → ((d ∷ p ∷ []) ⊨ initialFormula) ≡ IsInitial d p
    initial-reading d p = cong (⋀ S) (funExt (λ z → cong (iff (z ∈ˢ d))
      (cong ((z ∈ˢ P) ⊓_)
        (Ren.⊨-rename liftIndex ltFormula (z ∷ d ∷ p ∷ []) (z ∷ p ∷ []) (agrees z)
          ∙ lt-reading z p))))
      where
      agrees : (z : S) → Ren.Agrees liftIndex (z ∷ d ∷ p ∷ []) (z ∷ p ∷ [])
      agrees z zero = refl
      agrees z (suc zero) = refl

    initial-witness : (p : S) → ⟨ IsInitial (initial p) p ⟩
    initial-witness p z = subst ⟨_⟩ (initial-spec p z) , subst ⟨_⟩ (sym (initial-spec p z))

    initial-unique : (d p : S) → ⟨ IsInitial d p ⟩ → d ≡ initial p
    initial-unique d p h = GD.ext-path
      (λ z → ⇔toPath (h z .fst) (h z .snd) ∙ sym (initial-spec p z))

    minimumEmb : Fin 2 → Fin 3
    minimumEmb zero = suc zero
    minimumEmb (suc zero) = zero

    rankFormula : Formula S 2
    rankFormula = (var (suc zero) ∈̇ con P) ∧̇ ((var zero ∈̇ con w) ∧̇
      ∃̇∈ (con (GS.power P))
        (renameFo liftIndex initialFormula ∧̇ renameFo minimumEmb minimumFormula))

    Rank : S → S → Ω
    Rank n p = (p ∈ˢ P) ⊓ ((n ∈ˢ w) ⊓
      (⋁ S (λ d → (d ∈ˢ GS.power P) ⊓ (IsInitial d p ⊓ MinimumBound d n))))

    rank-reading : (n p : S) → ((n ∷ p ∷ []) ⊨ rankFormula) ≡ Rank n p
    rank-reading n p = cong ((p ∈ˢ P) ⊓_) (cong ((n ∈ˢ w) ⊓_)
      (cong (⋁ S) (funExt (λ d → cong ((d ∈ˢ GS.power P) ⊓_)
        (cong₂ _⊓_
          (Ren.⊨-rename liftIndex initialFormula (d ∷ n ∷ p ∷ []) (d ∷ p ∷ []) (initialAgrees d)
            ∙ initial-reading d p)
          (Ren.⊨-rename minimumEmb minimumFormula (d ∷ n ∷ p ∷ []) (n ∷ d ∷ []) (minimumAgrees d)
            ∙ minimum-reading d n))))))
      where
      initialAgrees : (d : S) → Ren.Agrees liftIndex (d ∷ n ∷ p ∷ []) (d ∷ p ∷ [])
      initialAgrees d zero = refl
      initialAgrees d (suc zero) = refl
      minimumAgrees : (d : S) → Ren.Agrees minimumEmb (d ∷ n ∷ p ∷ []) (n ∷ d ∷ [])
      minimumAgrees d zero = refl
      minimumAgrees d (suc zero) = refl

    rank-minimum : (n p : S) → ⟨ Rank n p ⟩ → ⟨ MinimumBound (initial p) n ⟩
    rank-minimum n p h = PT.rec (snd (MinimumBound (initial p) n))
      (λ { (d , hd , hi , hm) → subst (λ z → ⟨ MinimumBound z n ⟩) (initial-unique d p hi) hm })
      (h .snd .snd)

    rank-total : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ Rank n p) ⟩
    rank-total p hp = PT.map (λ { (n , hn , hm) → n , hn , hp , hn ,
      ∣ initial p , subst ⟨_⟩ (sym (GS.power-spec P (initial p)))
        (λ z hz → subst ⟨_⟩ (initial-spec p z) hz .fst) , initial-witness p , hm ∣₁ })
      (minimum-exists P (initial p) (initial-finite p hp))

    rank-single : (p n m : S) → ⟨ Rank n p ⟩ → ⟨ Rank m p ⟩ → ⟨ n ≈ˢ m ⟩
    rank-single p n m hn hm = minimum-unique (initial p) n m
      (hn .snd .fst) (hm .snd .fst) (rank-minimum n p hn) (rank-minimum m p hm)

    rank-injective : (p n q : S) → ⟨ Rank n p ⟩ → ⟨ Rank n q ⟩ → ⟨ p ≈ˢ q ⟩
    rank-injective p n q hp hq = PT.rec (snd (p ≈ˢ q))
      (λ { (inl pq) → Empty.rec (strict p q hp hq pq)
         ; (inr rest) → PT.rec (snd (p ≈ˢ q))
             (λ { (inl eq) → eq ; (inr qp) → Empty.rec (strict q p hq hp qp) }) rest })
      (trichotomy p q (hp .fst) (hq .fst))
      where
      strict : (a b : S) → ⟨ Rank n a ⟩ → ⟨ Rank n b ⟩ → ⟨ lt a b ⟩ → Empty.⊥
      strict a b ha hb ab = FP.strict-bound lem w hw (initial a) (initial b) n a
        (ha .snd .fst) (rank-minimum n a ha) (rank-minimum n b hb .fst)
        (λ z hz → subst ⟨_⟩ (sym (initial-spec b z))
          (subst ⟨_⟩ (initial-spec a z) hz .fst ,
            transitive z a b (subst ⟨_⟩ (initial-spec a z) hz .fst) (ha .fst) (hb .fst)
              (subst ⟨_⟩ (initial-spec a z) hz .snd) ab))
        (subst ⟨_⟩ (sym (initial-spec b a)) (ha .fst , ab))
        (λ h → irreflexive a (ha .fst) (subst ⟨_⟩ (initial-spec a a) h .snd))

    module G = FP.Graph P w rankFormula

    opaque
      order-injection : ⟨ CB.injectable P w ⟩
      order-injection = ∣ G.graph , G.injection
        (λ p hp → PT.map (λ { (n , hn , h) → n , hn ,
          subst ⟨_⟩ (sym (rank-reading n p)) h }) (rank-total p hp))
        (λ p n m h h' → rank-single p n m (subst ⟨_⟩ (rank-reading n p) h)
          (subst ⟨_⟩ (rank-reading m p) h'))
        (λ p n q h h' → rank-injective p n q (subst ⟨_⟩ (rank-reading n p) h)
          (subst ⟨_⟩ (rank-reading n q) h')) ∣₁
