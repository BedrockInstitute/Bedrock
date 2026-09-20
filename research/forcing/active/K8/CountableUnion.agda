{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CountableUnion
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
  using ( Formula; Term; var; con; _∈̇_; _∧̇_; ∀̇_; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( isKPairΔ; sepAt; sepAt-reading; subsetΔ )
open import OrdinaryProfile 𝒮 using ( iff; ChoiceSet; module Swap )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import K8.GroundSets
import K8.FiniteEnumeration
import K7.CardinalOrder
import CardinalBridge
import CodedVocabulary

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_; ⟦_⟧ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module GD = GroundDescription 𝒮 ext paths
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))
module FE = K8.FiniteEnumeration 𝒮 ext paths pair un pow sep find seed
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
module CV = CodedVocabulary 𝒮
open CB using ( _↔̇_ )
open FE using ( pairAt; pairAt-reading )

kpair-delta : (p x y : S) → ⟨ CB.isKPair p x y ⟩ → ⟨ isKPairΔ p x y ⟩
kpair-delta p x y kp =
  (∣ GS.singleton x , kp (GS.singleton x) .snd ∣ inl (GS.singleton-witness x) ∣₁
     , GS.singleton-witness x ∣₁)
  , (∣ GS.pairOf x y , kp (GS.pairOf x y) .snd ∣ inr (GS.pair-witness x y) ∣₁
     , GS.pair-witness x y ∣₁)
  , λ z hz → kp z .fst hz

ordered-kpair : (x y : S) → ⟨ CB.isKPair (GS.ordered x y) x y ⟩
ordered-kpair x y = PT.rec (snd (CB.isKPair (GS.ordered x y) x y))
  (λ { (p , kp) → subst (λ z → ⟨ CB.isKPair z x y ⟩)
    (GS.ordered-unique p x y (kpair-delta p x y kp)) kp }) (CO.kpairOf pair x y)

kpair-product : (X Y p x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
  → ⟨ CB.isKPair p x y ⟩ → ⟨ p ∈ˢ GS.product X Y ⟩
kpair-product X Y p x y hx hy kp = subst (λ z → ⟨ z ∈ˢ GS.product X Y ⟩)
  (sym (GS.ordered-unique p x y (kpair-delta p x y kp))) (GS.product-in X Y x y hx hy)

Selection : (X Y : S) → Formula S 2 → S → Ω
Selection X Y φ g = CB.isFunction g ⊓
  ((⋀ S (λ x → (x ∈ˢ X) ⇒ ⋁ S (λ y → ⋁ S (λ p →
    (p ∈ˢ g) ⊓ CB.isKPair p x y))))
  ⊓ (⋀ S (λ p → (p ∈ˢ g) ⇒ ⋀ S (λ x → ⋀ S (λ y →
    CB.isKPair p x y ⇒ ((x ∈ˢ X) ⊓ ((y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ))))))))

module BoundedChoice (choice : ChoiceSet) (X Y : S) (φ : Formula S 2)
  (total : (x : S) → ⟨ x ∈ˢ X ⟩
    → ⟨ ⋁ S (λ y → (y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
  where

  liftR : Fin 2 → Fin 3
  liftR zero = zero
  liftR (suc zero) = suc (suc zero)

  R : S → S → Ω
  R y x = (y ∷ x ∷ []) ⊨ φ

  lifted-reading : (y p x : S) → ((y ∷ p ∷ x ∷ []) ⊨ renameFo liftR φ) ≡ R y x
  lifted-reading y p x = Ren.⊨-rename liftR φ
    (y ∷ p ∷ x ∷ []) (y ∷ x ∷ []) agrees
    where
    agrees : Ren.Agrees liftR (y ∷ p ∷ x ∷ []) (y ∷ x ∷ [])
    agrees zero = refl
    agrees (suc zero) = refl

  tagFormula : Formula S 2
  tagFormula = ∃̇∈ (con Y)
    (pairAt (suc zero) (suc (suc zero)) zero ∧̇ renameFo liftR φ)

  Tag : S → S → Ω
  Tag p x = ⋁ S (λ y → (y ∈ˢ Y) ⊓ (CB.isKPair p x y ⊓ R y x))

  tag-reading : (p x : S) → ((p ∷ x ∷ []) ⊨ tagFormula) ≡ Tag p x
  tag-reading p x = cong (⋁ S) (funExt (λ y → cong ((y ∈ˢ Y) ⊓_)
    (cong₂ _⊓_ (pairAt-reading (suc zero) (suc (suc zero)) zero (y ∷ p ∷ x ∷ []))
      (lifted-reading y p x))))

  B : S
  B = GS.product X Y

  fiber : S → S
  fiber x = GS.separator B (sepAt tagFormula (x ∷ []))

  fiber-spec : (x p : S) → (p ∈ˢ fiber x) ≡ ((p ∈ˢ B) ⊓ Tag p x)
  fiber-spec x p = GS.separator-spec B (sepAt tagFormula (x ∷ [])) p
    ∙ cong ((p ∈ˢ B) ⊓_) (sepAt-reading tagFormula (x ∷ []) p ∙ tag-reading p x)

  fiber-in : (x : S) → ⟨ x ∈ˢ X ⟩ → (p : S) → ⟨ Tag p x ⟩ → ⟨ p ∈ˢ fiber x ⟩
  fiber-in x hx p tag = subst ⟨_⟩ (sym (fiber-spec x p))
    (PT.rec (snd (p ∈ˢ B))
      (λ { (y , hy , kp , _) → kpair-product X Y p x y hx hy kp }) tag , tag)

  Fiber : S → S → Ω
  Fiber d x = ⋀ S (λ p → iff (p ∈ˢ d) ((p ∈ˢ B) ⊓ Tag p x))

  fiberFormula : Formula S 2
  fiberFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    ((var zero ∈̇ con B) ∧̇ renameFo liftR tagFormula))

  fiber-reading : (d x : S) → ((d ∷ x ∷ []) ⊨ fiberFormula) ≡ Fiber d x
  fiber-reading d x = cong (⋀ S) (funExt (λ p → cong (iff (p ∈ˢ d))
    (cong ((p ∈ˢ B) ⊓_)
      (Ren.⊨-rename liftR tagFormula (p ∷ d ∷ x ∷ []) (p ∷ x ∷ []) (agrees p)
        ∙ tag-reading p x))))
    where
    agrees : (p : S) → Ren.Agrees liftR (p ∷ d ∷ x ∷ []) (p ∷ x ∷ [])
    agrees p zero = refl
    agrees p (suc zero) = refl

  fiber-proof : (x : S) → ⟨ Fiber (fiber x) x ⟩
  fiber-proof x p = subst ⟨_⟩ (fiber-spec x p) , subst ⟨_⟩ (sym (fiber-spec x p))

  fiber-unique : (d x : S) → ⟨ Fiber d x ⟩ → d ≡ fiber x
  fiber-unique d x hd = GD.ext-path (λ p → ⇔toPath (hd p .fst) (hd p .snd) ∙ sym (fiber-spec x p))

  fiber-contr : (x : S) → isContr (Σ[ d ∈ S ] ⟨ (d ∷ x ∷ []) ⊨ fiberFormula ⟩)
  fiber-contr x = (fiber x , subst ⟨_⟩ (sym (fiber-reading (fiber x) x)) (fiber-proof x))
    , λ { (d , hd) → Σ≡Prop (λ z → snd ((z ∷ x ∷ []) ⊨ fiberFormula))
        (sym (fiber-unique d x (subst ⟨_⟩ (fiber-reading d x) hd))) }

  Family : S → Ω
  Family F = ⋀ S (λ d → iff (d ∈ˢ F)
    (⋁ S (λ x → (x ∈ˢ X) ⊓ Fiber d x)))

  family-exists : ⟨ ⋁ S Family ⟩
  family-exists = PT.map
    (λ { (F , hF) → F , λ d →
      (λ hd → PT.map (λ { (x , hx , h) → x , hx , subst ⟨_⟩ (fiber-reading d x) h })
        (hF d .fst hd))
      , λ h → hF d .snd (PT.map
          (λ { (x , hx , hdx) → x , hx , subst ⟨_⟩ (sym (fiber-reading d x)) hdx }) h) })
    (GD.hasImage′ sep coll X fiberFormula (λ x _ → fiber-contr x))

  module AtFamily (F : S) (hF : ⟨ Family F ⟩) where

    fiber-member : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ fiber x ∈ˢ F ⟩
    fiber-member x hx = hF (fiber x) .snd ∣ x , hx , fiber-proof x ∣₁

    inhabited : (d : S) → ⟨ d ∈ˢ F ⟩ → ⟨ ⋁ S (λ p → p ∈ˢ d) ⟩
    inhabited d hd = PT.rec (snd (⋁ S (λ p → p ∈ˢ d)))
      (λ { (x , hx , hdx) → PT.map
        (λ { (y , hy , hR) → GS.ordered x y , hdx (GS.ordered x y) .snd
          (GS.product-in X Y x y hx hy , ∣ y , hy , ordered-kpair x y , hR ∣₁) })
        (total x hx) }) (hF d .fst hd)

    disjoint : (d e : S) → ⟨ d ∈ˢ F ⟩ → ⟨ e ∈ˢ F ⟩
      → ⟨ ⋁ S (λ p → (p ∈ˢ d) ⊓ (p ∈ˢ e)) ⟩ → d ≡ e
    disjoint d e hd he common = PT.rec (isSetS d e)
      (λ { (x , hx , hdx) → PT.rec (isSetS d e)
        (λ { (z , hz , hez) → PT.rec (isSetS d e)
          (λ { (p , pd , pe) → PT.rec (isSetS d e)
            (λ { (y , hy , kp , _) → PT.rec (isSetS d e)
              (λ { (v , hv , kq , _) → fiber-unique d x hdx
                ∙ cong fiber (GS.≈→≡ (CO.kpair-components pair p x y z v kp kq .fst))
                ∙ sym (fiber-unique e z hez) }) (hez p .fst pe .snd) })
            (hdx p .fst pd .snd) }) common }) (hF e .fst he) }) (hF d .fst hd)

    ChoiceOn : S → Ω
    ChoiceOn c = ⋀ S (λ d → (d ∈ˢ F) ⇒
      ((⋁ S (λ p → (p ∈ˢ c) ⊓ (p ∈ˢ d)))
      ⊓ (⋀ S (λ p → ⋀ S (λ q →
        (((p ∈ˢ c) ⊓ (p ∈ˢ d)) ⊓ ((q ∈ˢ c) ⊓ (q ∈ˢ d))) ⇒ (p ≈ˢ q))))))

    module AtChoice (c : S) (hc : ⟨ ChoiceOn c ⟩) where

      graphFormula : Formula S 1
      graphFormula = ∃̇∈ (con X) (Swap.swapFo tagFormula)

      graph : S
      graph = GS.separator c graphFormula

      graph-spec : (p : S) → (p ∈ˢ graph) ≡
        ((p ∈ˢ c) ⊓ (⋁ S (λ x → (x ∈ˢ X) ⊓ Tag p x)))
      graph-spec p = GS.separator-spec c graphFormula p
        ∙ cong ((p ∈ˢ c) ⊓_) (cong (⋁ S) (funExt (λ x → cong ((x ∈ˢ X) ⊓_)
          (Swap.⊨-swap tagFormula x p ∙ tag-reading p x))))

      graph-entry : (p : S) → ⟨ p ∈ˢ graph ⟩ → (u v : S) → ⟨ CB.isKPair p u v ⟩
        → ⟨ (u ∈ˢ X) ⊓ ((v ∈ˢ Y) ⊓ R v u) ⟩
      graph-entry p hp u v kp = PT.rec (snd ((u ∈ˢ X) ⊓ ((v ∈ˢ Y) ⊓ R v u)))
        (λ { (x , hx , tag) → PT.rec (snd ((u ∈ˢ X) ⊓ ((v ∈ˢ Y) ⊓ R v u)))
          (λ { (y , hy , kq , hR) →
            subst (λ z → ⟨ z ∈ˢ X ⟩) (sym (fst (eqs x y kq))) hx
            , subst (λ z → ⟨ z ∈ˢ Y ⟩) (sym (snd (eqs x y kq))) hy
            , subst (λ z → ⟨ R z u ⟩) (sym (snd (eqs x y kq)))
                (subst (λ z → ⟨ R y z ⟩) (sym (fst (eqs x y kq))) hR) }) tag })
        (subst ⟨_⟩ (graph-spec p) hp .snd)
        where
        eqs : (x y : S) → ⟨ CB.isKPair p x y ⟩ → (u ≡ x) × (v ≡ y)
        eqs x y kq = GS.≈→≡ (CO.kpair-components pair p u v x y kp kq .fst)
          , GS.≈→≡ (CO.kpair-components pair p u v x y kp kq .snd)

      graph-relation : ⟨ CB.isRelation graph ⟩
      graph-relation p hp = PT.rec (snd (⋁ S (λ x → ⋁ S (λ y → CB.isKPair p x y))))
        (λ { (x , _ , tag) → PT.map (λ { (y , _ , kp , _) → x , ∣ y , kp ∣₁ }) tag })
        (subst ⟨_⟩ (graph-spec p) hp .snd)

      graph-function : ⟨ CB.isFunction graph ⟩
      graph-function = graph-relation , single
        where
        single : (p : S) → ⟨ p ∈ˢ graph ⟩ → (q : S) → ⟨ q ∈ˢ graph ⟩
          → (u v z : S) → ⟨ CB.isKPair p u v ⊓ CB.isKPair q u z ⟩ → ⟨ v ≈ˢ z ⟩
        single p hp q hq u v z (kp , kq) =
          CO.kpair-components pair p u v u z kp
            (subst (λ t → ⟨ CB.isKPair t u z ⟩) (sym (GS.≈→≡ equal)) kq) .snd
          where
          ep = graph-entry p hp u v kp
          eq = graph-entry q hq u z kq
          equal : ⟨ p ≈ˢ q ⟩
          equal = hc (fiber u) (fiber-member u (ep .fst)) .snd p q
            ((subst ⟨_⟩ (graph-spec p) hp .fst , fiber-in u (ep .fst) p
                ∣ v , ep .snd .fst , kp , ep .snd .snd ∣₁)
            , (subst ⟨_⟩ (graph-spec q) hq .fst , fiber-in u (eq .fst) q
                ∣ z , eq .snd .fst , kq , eq .snd .snd ∣₁))

      graph-total : (x : S) → ⟨ x ∈ˢ X ⟩
        → ⟨ ⋁ S (λ y → ⋁ S (λ p → (p ∈ˢ graph) ⊓ CB.isKPair p x y)) ⟩
      graph-total x hx = PT.rec (snd (⋁ S (λ y → ⋁ S (λ p →
        (p ∈ˢ graph) ⊓ CB.isKPair p x y))))
        (λ { (p , pc , pf) → PT.map
          (λ { (y , hy , kp , hR) → y , ∣ p , subst ⟨_⟩ (sym (graph-spec p))
            (pc , ∣ x , hx , ∣ y , hy , kp , hR ∣₁ ∣₁) , kp ∣₁ })
          (subst ⟨_⟩ (fiber-spec x p) pf .snd) })
        (hc (fiber x) (fiber-member x hx) .fst)

      graph-selection : ⟨ Selection X Y φ graph ⟩
      graph-selection = graph-function , graph-total , graph-entry

    selected : ⟨ ⋁ S (Selection X Y φ) ⟩
    selected = PT.map (λ { (c , hc) → AtChoice.graph c hc , AtChoice.graph-selection c hc })
      (choice F inhabited disjoint)

  selected : ⟨ ⋁ S (Selection X Y φ) ⟩
  selected = PT.rec (snd (⋁ S (Selection X Y φ)))
    (λ { (F , hF) → AtFamily.selected F hF }) family-exists

opaque
  bounded-choice : ChoiceSet → (X Y : S) → (φ : Formula S 2)
    → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ ⋁ S (λ y → (y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
    → ⟨ ⋁ S (Selection X Y φ) ⟩
  bounded-choice = BoundedChoice.selected

choice-injection : ChoiceSet → (X Y : S) → (φ : Formula S 2)
  → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ ⋁ S (λ y → (y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
  → ((x x' y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x' ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
      → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → ⟨ (y ∷ x' ∷ []) ⊨ φ ⟩ → ⟨ x ≈ˢ x' ⟩)
  → ⟨ CB.injectable X Y ⟩
choice-injection choice X Y φ total unique = PT.map build (bounded-choice choice X Y φ total)
  where
  build : Σ[ g ∈ S ] ⟨ Selection X Y φ g ⟩ → Σ[ g ∈ S ] ⟨ CB.isInjection g X Y ⟩
  build (g , hg) = g , hg .fst , hg .snd .fst
    , (λ p hp x y kp → hg .snd .snd p hp x y kp .snd .fst)
    , λ p hp q hq x y z (kp , kq) → unique x z y
        (hg .snd .snd p hp x y kp .fst) (hg .snd .snd q hq z y kq .fst)
        (hg .snd .snd p hp x y kp .snd .fst)
        (hg .snd .snd p hp x y kp .snd .snd) (hg .snd .snd q hq z y kq .snd .snd)

Ref : S → S → S → Ω
Ref f x y = ⋁ S (λ p → (p ∈ˢ f) ⊓ CB.isKPair p x y)

refFormula : Formula S 3
refFormula = ∃̇∈ (var zero) (pairAt zero (suc (suc zero)) (suc (suc (suc zero))))

ref-reading : (f x y : S) → ((f ∷ x ∷ y ∷ []) ⊨ refFormula) ≡ Ref f x y
ref-reading f x y = cong (⋁ S) (funExt (λ p → cong ((p ∈ˢ f) ⊓_)
  (pairAt-reading zero (suc (suc zero)) (suc (suc (suc zero))) (p ∷ f ∷ x ∷ y ∷ []))))

refAt : ∀ {n} → Term S n → Term S n → Term S n → Formula S n
refAt f x y = CV.instFo emb refFormula
  where
  emb : Fin 3 → _
  emb zero = f
  emb (suc zero) = x
  emb (suc (suc zero)) = y

refAt-reading : ∀ {n} (f x y : Term S n) (γ : S ^ n)
  → (γ ⊨ refAt f x y) ≡ Ref (⟦ f ⟧ γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)
refAt-reading f x y γ = CV.⊨-inst emb refFormula γ
  (⟦ f ⟧ γ ∷ ⟦ x ⟧ γ ∷ ⟦ y ⟧ γ ∷ []) fits
  ∙ ref-reading (⟦ f ⟧ γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)
  where
  emb : Fin 3 → _
  emb zero = f
  emb (suc zero) = x
  emb (suc (suc zero)) = y
  fits : CV.Fits emb γ (⟦ f ⟧ γ ∷ ⟦ x ⟧ γ ∷ ⟦ y ⟧ γ ∷ [])
  fits zero = refl
  fits (suc zero) = refl
  fits (suc (suc zero)) = refl

ref-single : (f x y z : S) → ⟨ CB.isFunction f ⟩
  → ⟨ Ref f x y ⟩ → ⟨ Ref f x z ⟩ → ⟨ y ≈ˢ z ⟩
ref-single f x y z hf = PT.rec (isPropΠ (λ _ → snd (y ≈ˢ z)))
  (λ { (p , hp , kp) → PT.rec (snd (y ≈ˢ z))
    (λ { (q , hq , kq) → hf .snd p hp q hq x y z (kp , kq) }) })

ref-injective : (f X Y x y z : S) → ⟨ CB.isInjection f X Y ⟩
  → ⟨ Ref f x y ⟩ → ⟨ Ref f z y ⟩ → ⟨ x ≈ˢ z ⟩
ref-injective f X Y x y z hf = PT.rec (isPropΠ (λ _ → snd (x ≈ˢ z)))
  (λ { (p , hp , kp) → PT.rec (snd (x ≈ˢ z))
    (λ { (q , hq , kq) → hf .snd .snd .snd p hp q hq x y z (kp , kq) }) })

ref-range : (f X Y x y : S) → ⟨ CB.isInjection f X Y ⟩ → ⟨ Ref f x y ⟩ → ⟨ y ∈ˢ Y ⟩
ref-range f X Y x y hf = PT.rec (snd (y ∈ˢ Y))
  (λ { (p , hp , kp) → hf .snd .snd .fst p hp x y kp })

selection-value : (X Y : S) (φ : Formula S 2) (g x y : S)
  → ⟨ Selection X Y φ g ⟩ → ⟨ Ref g x y ⟩
  → ⟨ (x ∈ˢ X) ⊓ ((y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩
selection-value X Y φ g x y hg = PT.rec (snd ((x ∈ˢ X) ⊓ ((y ∈ˢ Y) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
  (λ { (p , hp , kp) → hg .snd .snd p hp x y kp })

injectionFormula : S → Formula S 2
injectionFormula w = CV.instFo emb CB.IsInjectionφ
  where
  emb : Fin 3 → Term S 2
  emb zero = var zero
  emb (suc zero) = var (suc zero)
  emb (suc (suc zero)) = con w

injection-reading : (w f a : S)
  → ((f ∷ a ∷ []) ⊨ injectionFormula w) ≡ CB.isInjection f a w
injection-reading w f a = CV.⊨-inst emb CB.IsInjectionφ (f ∷ a ∷ []) (f ∷ a ∷ w ∷ []) fits
  ∙ CB.IsInjection-bridge f a w
  where
  emb : Fin 3 → Term S 2
  emb zero = var zero
  emb (suc zero) = var (suc zero)
  emb (suc (suc zero)) = con w
  fits : CV.Fits emb (f ∷ a ∷ []) (f ∷ a ∷ w ∷ [])
  fits zero = refl
  fits (suc zero) = refl
  fits (suc (suc zero)) = refl

bounded-injection : (U a w : S) → ⟨ subsetΔ a U ⟩ → ⟨ CB.injectable a w ⟩
  → ⟨ ⋁ S (λ f → (f ∈ˢ GS.power (GS.product U w)) ⊓ CB.isInjection f a w) ⟩
bounded-injection U a w sub = PT.map trim
  where
  trim : Σ[ f ∈ S ] ⟨ CB.isInjection f a w ⟩
    → Σ[ g ∈ S ] ⟨ (g ∈ˢ GS.power (GS.product U w)) ⊓ CB.isInjection g a w ⟩
  trim (f , hf) = g , subst ⟨_⟩ (sym (GS.power-spec (GS.product U w) g)) (λ p hp → out p hp .fst)
    , ( (λ p hp → hf .fst .fst p (out p hp .snd))
      , (λ p hp q hq x y z ks → hf .fst .snd p (out p hp .snd) q (out q hq .snd) x y z ks) )
    , (λ x hx → PT.map (λ { (y , some) → y , PT.map
        (λ { (p , hp , kp) → p , into p
          (kpair-product U w p x y (sub x hx) (hf .snd .snd .fst p hp x y kp) kp , hp) , kp }) some })
        (hf .snd .fst x hx))
    , (λ p hp x y kp → hf .snd .snd .fst p (out p hp .snd) x y kp)
    , (λ p hp q hq x y z ks → hf .snd .snd .snd p (out p hp .snd) q (out q hq .snd) x y z ks)
    where
    g : S
    g = GS.separator (GS.product U w) (var zero ∈̇ con f)
    out : (p : S) → ⟨ p ∈ˢ g ⟩ → ⟨ (p ∈ˢ GS.product U w) ⊓ (p ∈ˢ f) ⟩
    out p = subst ⟨_⟩ (GS.separator-spec (GS.product U w) (var zero ∈̇ con f) p)
    into : (p : S) → ⟨ (p ∈ˢ GS.product U w) ⊓ (p ∈ˢ f) ⟩ → ⟨ p ∈ˢ g ⟩
    into p = subst ⟨_⟩ (sym (GS.separator-spec (GS.product U w) (var zero ∈̇ con f) p))

choose-injections : ChoiceSet → (F U w : S)
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
  → ⟨ ⋁ S (Selection F (GS.power (GS.product U w)) (injectionFormula w)) ⟩
choose-injections choice F U w sub countable =
  bounded-choice choice F (GS.power (GS.product U w)) (injectionFormula w)
    (λ a ha → PT.map (λ { (f , hf , inj) → f , hf ,
      subst ⟨_⟩ (sym (injection-reading w f a)) inj })
      (bounded-injection U a w (sub a ha) (countable a ha)))

module UnionCoordinates (choice : ChoiceSet) (F U w index selected : S)
  (index-injection : ⟨ CB.isInjection index F w ⟩)
  (selection : ⟨ Selection F (GS.power (GS.product U w)) (injectionFormula w) selected ⟩)
  (cover : (u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
  where

  E : S
  E = GS.power (GS.product U w)

  value : (a f : S) → ⟨ Ref selected a f ⟩ → ⟨ (f ∈ˢ E) ⊓ CB.isInjection f a w ⟩
  value a f h = v .snd .fst , subst ⟨_⟩ (injection-reading w f a) (v .snd .snd)
    where
    v = selection-value F E (injectionFormula w) selected a f selection h

  private
    jv iv fv av zv uv : Fin 6
    jv = zero
    iv = suc zero
    fv = suc (suc zero)
    av = suc (suc (suc zero))
    zv = suc (suc (suc (suc zero)))
    uv = suc (suc (suc (suc (suc zero))))

    bodyFormula : Formula S 6
    bodyFormula = pairAt zv iv jv ∧̇
      (refAt (con index) (var av) (var iv) ∧̇
      (refAt (con selected) (var av) (var fv) ∧̇ refAt (var fv) (var uv) (var jv)))

    Body : S → S → S → S → S → S → Ω
    Body a f i j z u = CB.isKPair z i j ⊓
      (Ref index a i ⊓ (Ref selected a f ⊓ Ref f u j))

    body-reading : (a f i j z u : S)
      → ((j ∷ i ∷ f ∷ a ∷ z ∷ u ∷ []) ⊨ bodyFormula) ≡ Body a f i j z u
    body-reading a f i j z u = cong₂ _⊓_ (pairAt-reading zv iv jv γ)
      (cong₂ _⊓_ (refAt-reading (con index) (var av) (var iv) γ)
        (cong₂ _⊓_ (refAt-reading (con selected) (var av) (var fv) γ)
          (refAt-reading (var fv) (var uv) (var jv) γ)))
      where
      γ = j ∷ i ∷ f ∷ a ∷ z ∷ u ∷ []

  coordinateFormula : Formula S 2
  coordinateFormula = ∃̇∈ (con F) (∃̇∈ (con E) (∃̇∈ (con w) (∃̇∈ (con w) bodyFormula)))

  Coordinate : S → S → Ω
  Coordinate z u = ⋁ S (λ a → (a ∈ˢ F) ⊓
    ⋁ S (λ f → (f ∈ˢ E) ⊓
    ⋁ S (λ i → (i ∈ˢ w) ⊓
    ⋁ S (λ j → (j ∈ˢ w) ⊓ Body a f i j z u))))

  coordinate-reading : (z u : S)
    → ((z ∷ u ∷ []) ⊨ coordinateFormula) ≡ Coordinate z u
  coordinate-reading z u = cong (⋁ S) (funExt (λ a → cong ((a ∈ˢ F) ⊓_)
    (cong (⋁ S) (funExt (λ f → cong ((f ∈ˢ E) ⊓_)
    (cong (⋁ S) (funExt (λ i → cong ((i ∈ˢ w) ⊓_)
    (cong (⋁ S) (funExt (λ j → cong ((j ∈ˢ w) ⊓_) (body-reading a f i j z u))))))))))))

  use-coordinate : (z u : S) (P : Ω)
    → ((a f i j : S) → ⟨ a ∈ˢ F ⟩ → ⟨ f ∈ˢ E ⟩ → ⟨ i ∈ˢ w ⟩ → ⟨ j ∈ˢ w ⟩
        → ⟨ CB.isKPair z i j ⟩ → ⟨ Ref index a i ⟩ → ⟨ Ref selected a f ⟩
        → ⟨ Ref f u j ⟩ → ⟨ P ⟩)
    → ⟨ Coordinate z u ⟩ → ⟨ P ⟩
  use-coordinate z u P k = PT.rec (snd P)
    (λ { (a , ha , fs) → PT.rec (snd P)
      (λ { (f , hf , is) → PT.rec (snd P)
        (λ { (i , hi , js) → PT.rec (snd P)
          (λ { (j , hj , kp , ri , rs , rf) → k a f i j ha hf hi hj kp ri rs rf }) js }) is }) fs })

  coordinate-total : (u : S) → ⟨ u ∈ˢ U ⟩
    → ⟨ ⋁ S (λ z → (z ∈ˢ GS.product w w) ⊓ Coordinate z u) ⟩
  coordinate-total u hu = PT.rec (snd target) atLayer (cover u hu)
    where
    target : Ω
    target = ⋁ S (λ z → (z ∈ˢ GS.product w w) ⊓ Coordinate z u)

    atLayer : Σ[ a ∈ S ] ⟨ (a ∈ˢ F) ⊓ (u ∈ˢ a) ⟩ → ⟨ target ⟩
    atLayer (a , ha , ua) = PT.rec (snd target)
      (λ { (i , ri) → PT.rec (snd target)
        (λ { (f , rs) → PT.map
          (λ { (j , rf) → GS.ordered i j ,
            GS.product-in w w i j (ref-range index F w a i index-injection ri)
              (ref-range f a w u j (value a f rs .snd) rf)
            , ∣ a , ha , ∣ f , value a f rs .fst ,
              ∣ i , ref-range index F w a i index-injection ri ,
              ∣ j , ref-range f a w u j (value a f rs .snd) rf ,
              ordered-kpair i j , ri , rs , rf ∣₁ ∣₁ ∣₁ ∣₁ })
          (value a f rs .snd .snd .fst u ua) }) (selection .snd .fst a ha) })
      (index-injection .snd .fst a ha)

  coordinate-unique : (u v z : S) → ⟨ Coordinate z u ⟩ → ⟨ Coordinate z v ⟩ → ⟨ u ≈ˢ v ⟩
  coordinate-unique u v z h h' = use-coordinate z u (u ≈ˢ v) first h
    where
    first : (a f i j : S) → ⟨ a ∈ˢ F ⟩ → ⟨ f ∈ˢ E ⟩ → ⟨ i ∈ˢ w ⟩ → ⟨ j ∈ˢ w ⟩
      → ⟨ CB.isKPair z i j ⟩ → ⟨ Ref index a i ⟩ → ⟨ Ref selected a f ⟩
      → ⟨ Ref f u j ⟩ → ⟨ u ≈ˢ v ⟩
    first a f i j ha hf hi hj kp ri rs rf = use-coordinate z v (u ≈ˢ v) second h'
      where
      second : (a' f' i' j' : S) → ⟨ a' ∈ˢ F ⟩ → ⟨ f' ∈ˢ E ⟩
        → ⟨ i' ∈ˢ w ⟩ → ⟨ j' ∈ˢ w ⟩ → ⟨ CB.isKPair z i' j' ⟩
        → ⟨ Ref index a' i' ⟩ → ⟨ Ref selected a' f' ⟩ → ⟨ Ref f' v j' ⟩ → ⟨ u ≈ˢ v ⟩
      second a' f' i' j' ha' hf' hi' hj' kq ri' rs' rf' =
        ref-injective f a w u j v (value a f rs .snd) rf same-ref
        where
        ij : (i ≡ i') × (j ≡ j')
        ij = GS.≈→≡ (CO.kpair-components pair z i j i' j' kp kq .fst)
          , GS.≈→≡ (CO.kpair-components pair z i j i' j' kp kq .snd)

        aa : a ≡ a'
        aa = GS.≈→≡ (ref-injective index F w a i a' index-injection ri
          (subst (λ t → ⟨ Ref index a' t ⟩) (sym (ij .fst)) ri'))

        ff : f ≡ f'
        ff = GS.≈→≡ (ref-single selected a f f' (selection .fst) rs
          (subst (λ t → ⟨ Ref selected t f' ⟩) (sym aa) rs'))

        same-ref : ⟨ Ref f v j ⟩
        same-ref = subst (λ t → ⟨ Ref t v j ⟩) (sym ff)
          (subst (λ t → ⟨ Ref f' v t ⟩) (sym (ij .snd)) rf')

  into-square : ⟨ CB.injectable U (GS.product w w) ⟩
  into-square = choice-injection choice U (GS.product w w) coordinateFormula
    (λ u hu → PT.map (λ { (z , hz , h) → z , hz ,
      subst ⟨_⟩ (sym (coordinate-reading z u)) h }) (coordinate-total u hu))
    (λ u v z _ _ _ h h' → coordinate-unique u v z
      (subst ⟨_⟩ (coordinate-reading z u) h) (subst ⟨_⟩ (coordinate-reading z v) h'))

opaque
  countable-union-into-square : ChoiceSet → (F U w : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
    → ((u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
    → ⟨ CB.injectable F w ⟩
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
    → ⟨ CB.injectable U (GS.product w w) ⟩
  countable-union-into-square choice F U w sub cover countF countA =
    PT.rec (snd (CB.injectable U (GS.product w w)))
      (λ { (index , hi) → PT.rec (snd (CB.injectable U (GS.product w w)))
        (λ { (selected , hs) → UnionCoordinates.into-square choice F U w index selected hi hs cover })
        (choose-injections choice F U w sub countA) }) countF

countable-union : ChoiceSet → (F U w : S)
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
  → ((u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
  → ⟨ CB.injectable F w ⟩
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
  → ⟨ CB.injectable (GS.product w w) w ⟩
  → ⟨ CB.injectable U w ⟩
countable-union choice F U w sub cover countF countA square =
  CO.injectable-trans sep coll pair U (GS.product w w) w
    (countable-union-into-square choice F U w sub cover countF countA) square
