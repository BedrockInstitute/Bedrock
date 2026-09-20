{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DeleteFamilies
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
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ¬̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( iff; module Swap )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
import CardinalBridge
import K8.GroundSets
import K8.FinitePigeonhole
import K8.FamilyImages
import K8.Uncountability
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FP = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
open CB using ( _↔̇_ )
open GS using ( ≈→≡ )

cut : S → S → S
cut a x = GS.separator a (¬̇ (var zero ≐ con x))

cut-spec : (a x z : S)
  → (z ∈ˢ cut a x) ≡ ((z ∈ˢ a) ⊓ ((z ≈ˢ x) ⇒ ⊥))
cut-spec a x z = GS.separator-spec a (¬̇ (var zero ≐ con x)) z

Cut : S → S → S → Ω
Cut d a x = ⋀ S (λ z → iff (z ∈ˢ d) ((z ∈ˢ a) ⊓ ((z ≈ˢ x) ⇒ ⊥)))

cutFormula : S → Formula S 2
cutFormula x = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ var (suc (suc zero))) ∧̇ ¬̇ (var zero ≐ con x)))

cut-reading : (d a x : S) → ((d ∷ a ∷ []) ⊨ cutFormula x) ≡ Cut d a x
cut-reading d a x = refl

cut-witness : (a x : S) → ⟨ Cut (cut a x) a x ⟩
cut-witness a x z = subst ⟨_⟩ (cut-spec a x z) , subst ⟨_⟩ (sym (cut-spec a x z))

cut-unique : (d a x : S) → ⟨ Cut d a x ⟩ → d ≡ cut a x
cut-unique d a x h = ≈→≡ (ext d (cut a x) λ z →
  (λ hz → cut-witness a x z .snd (h z .fst hz)) ,
  (λ hz → h z .snd (cut-witness a x z .fst hz)))

cut-sub : (a x : S) → ⟨ subsetΔ (cut a x) a ⟩
cut-sub a x z hz = cut-witness a x z .fst hz .fst

cut-omits : (a x : S) → ⟨ x ∈ˢ cut a x ⟩ → Empty.⊥
cut-omits a x hx = Empty.rec* (cut-witness a x x .fst hx .snd (FP.CO.≈-refl x))

cut-finite : (X a x : S) → ⟨ finiteIn X a ⟩ → ⟨ finiteIn X (cut a x) ⟩
cut-finite X a x ha = finite-subset lem X a (cut a x) ha (cut-sub a x)

cut-recover : (d a x z : S) → ⟨ Cut d a x ⟩ → ⟨ x ∈ˢ a ⟩
  → ⟨ z ∈ˢ a ⟩ → ⟨ (z ∈ˢ d) ⊔ (z ≈ˢ x) ⟩
cut-recover d a x z h hx hz with lem (z ≈ˢ x)
... | inl eq = ∣ inr eq ∣₁
... | inr neq = ∣ inl (h z .snd (hz , λ eq → Empty.rec (neq eq))) ∣₁

cut-restore : (d a x : S) → ⟨ Cut d a x ⟩ → ⟨ x ∈ˢ a ⟩
  → a ≡ GS.join d (GS.singleton x)
cut-restore d a x h hx = ≈→≡ (ext a (GS.join d (GS.singleton x)) λ z →
  (λ hz → subst ⟨_⟩ (sym (GS.join-spec d (GS.singleton x) z))
    (PT.map (λ { (inl zd) → inl zd
               ; (inr eq) → inr (subst (λ t → ⟨ t ∈ˢ GS.singleton x ⟩)
                   (sym (≈→≡ eq)) (GS.singleton-witness x .fst)) })
      (cut-recover d a x z h hx hz))) ,
  (λ hz → PT.rec (snd (z ∈ˢ a)) (λ
    { (inl zd) → h z .fst zd .fst
    ; (inr zx) → subst (λ t → ⟨ t ∈ˢ a ⟩)
        (sym (≈→≡ (GS.singleton-witness x .snd z zx))) hx })
    (subst ⟨_⟩ (GS.join-spec d (GS.singleton x) z) hz)))

cut-injective : (a b x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ b ⟩
  → cut a x ≡ cut b x → a ≡ b
cut-injective a b x ha hb eq = cut-restore (cut a x) a x (cut-witness a x) ha
  ∙ cong (λ d → GS.join d (GS.singleton x)) eq
  ∙ sym (cut-restore (cut b x) b x (cut-witness b x) hb)

delete-bound : (a x n s : S) → ⟨ CB.isSuccOf s n ⟩
  → ⟨ CB.injectable a s ⟩ → ⟨ x ∈ˢ a ⟩ → ⟨ CB.injectable (cut a x) n ⟩
delete-bound a x n s ns bound hx = FP.proper-subset-bound lem (cut a x) a n s x
  ns bound (cut-sub a x) hx (cut-omits a x)

Delete : S → S → S → Ω
Delete d a x = (x ∈ˢ a) ⊓ Cut d a x

deleteFormula : S → Formula S 2
deleteFormula x = (con x ∈̇ var (suc zero)) ∧̇ cutFormula x

delete-reading : (d a x : S) → ((d ∷ a ∷ []) ⊨ deleteFormula x) ≡ Delete d a x
delete-reading d a x = refl

delete-single : (a d e x : S) → ⟨ Delete d a x ⟩ → ⟨ Delete e a x ⟩ → ⟨ d ≈ˢ e ⟩
delete-single a d e x hd he = subst ⟨_⟩ (sym (paths d e))
  (cut-unique d a x (hd .snd) ∙ sym (cut-unique e a x (he .snd)))

delete-injective : (a d b x : S) → ⟨ Delete d a x ⟩ → ⟨ Delete d b x ⟩ → ⟨ a ≈ˢ b ⟩
delete-injective a d b x ha hb = subst ⟨_⟩ (sym (paths a b))
  (cut-restore d a x (ha .snd) (ha .fst) ∙ sym (cut-restore d b x (hb .snd) (hb .fst)))

Intersection : S → S → S → Ω
Intersection a b r = ⋀ S (λ z → iff ((z ∈ˢ a) ⊓ (z ∈ˢ b)) (z ∈ˢ r))

cut-intersection-root : (a b d e x r : S)
  → ⟨ Delete d a x ⟩ → ⟨ Delete e b x ⟩ → ⟨ Intersection d e r ⟩
  → ⟨ Intersection a b (GS.join r (GS.singleton x)) ⟩
cut-intersection-root a b d e x r hd he root z = forward , backward
  where
  forward : ⟨ (z ∈ˢ a) ⊓ (z ∈ˢ b) ⟩ → ⟨ z ∈ˢ GS.join r (GS.singleton x) ⟩
  forward (za , zb) = choose (lem (z ≈ˢ x))
    where
    choose : ⟨ z ≈ˢ x ⟩ ⊎ (⟨ z ≈ˢ x ⟩ → Empty.⊥)
      → ⟨ z ∈ˢ GS.join r (GS.singleton x) ⟩
    choose (inl eq) = subst ⟨_⟩ (sym (GS.join-spec r (GS.singleton x) z))
      ∣ inr (subst (λ t → ⟨ t ∈ˢ GS.singleton x ⟩)
        (sym (≈→≡ eq)) (GS.singleton-witness x .fst)) ∣₁
    choose (inr neq) = subst ⟨_⟩ (sym (GS.join-spec r (GS.singleton x) z))
      ∣ inl (root z .fst (hd .snd z .snd (za , λ eq → Empty.rec (neq eq))
        , he .snd z .snd (zb , λ eq → Empty.rec (neq eq)))) ∣₁

  backward : ⟨ z ∈ˢ GS.join r (GS.singleton x) ⟩ → ⟨ (z ∈ˢ a) ⊓ (z ∈ˢ b) ⟩
  backward hz = PT.rec (snd ((z ∈ˢ a) ⊓ (z ∈ˢ b))) (λ
    { (inl zr) → hd .snd z .fst (root z .snd zr .fst) .fst
        , he .snd z .fst (root z .snd zr .snd) .fst
    ; (inr zx) → subst (λ t → ⟨ (t ∈ˢ a) ⊓ (t ∈ˢ b) ⟩)
        (sym (≈→≡ (GS.singleton-witness x .snd z zx))) (hd .fst , he .fst) })
    (subst ⟨_⟩ (GS.join-spec r (GS.singleton x) z) hz)

module Family (X F x : S)
  (sub : ⟨ subsetΔ F (GS.power X) ⟩)
  (contains : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ x ∈ˢ a ⟩)
  where

  D : S
  D = FI.imageIn F (GS.power X) (deleteFormula x)

  D-sub : ⟨ subsetΔ D (GS.power X) ⟩
  D-sub = FI.image-sub F (GS.power X) (deleteFormula x)

  D-in : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ cut a x ∈ˢ D ⟩
  D-in a ha = FI.image-in F (GS.power X) (deleteFormula x) a (cut a x) ha
    (subst ⟨_⟩ (sym (GS.power-spec X (cut a x)))
      (λ z hz → subst ⟨_⟩ (GS.power-spec X a) (sub a ha) z (cut-sub a x z hz)))
    (contains a ha , cut-witness a x)

  D-out : (d : S) → ⟨ d ∈ˢ D ⟩
    → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ Delete d a x) ⟩
  D-out d = FI.image-out F (GS.power X) (deleteFormula x) d

  module Graph = FP.Graph F D (deleteFormula x)

  deletion-injection : ⟨ CB.injectable F D ⟩
  deletion-injection = ∣ Graph.graph , Graph.injection
    (λ a ha → ∣ cut a x , D-in a ha , contains a ha , cut-witness a x ∣₁)
    (λ a d e → delete-single a d e x)
    (λ a d b → delete-injective a d b x) ∣₁

  D-uncountable : (w : S) → ⟨ UC.uncountable w F ⟩ → ⟨ UC.uncountable w D ⟩
  D-uncountable w unF countD = unF
    (FP.CO.injectable-trans sep coll pair F D w deletion-injection countD)

  D-finite : ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
    → (d : S) → ⟨ d ∈ˢ D ⟩ → ⟨ finiteIn X d ⟩
  D-finite each d hd = PT.rec (snd (finiteIn X d))
    (λ { (a , ha , _ , hcut) → subst (λ z → ⟨ finiteIn X z ⟩)
      (sym (cut-unique d a x hcut)) (cut-finite X a x (each a ha)) }) (D-out d hd)

  D-bound : (n s : S) → ⟨ CB.isSuccOf s n ⟩
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a s ⟩)
    → (d : S) → ⟨ d ∈ˢ D ⟩ → ⟨ CB.injectable d n ⟩
  D-bound n s ns each d hd = PT.rec (snd (CB.injectable d n))
    (λ { (a , ha , hx , hcut) → subst (λ z → ⟨ CB.injectable z n ⟩)
      (sym (cut-unique d a x hcut)) (delete-bound a x n s ns (each a ha) hx) }) (D-out d hd)

  module Pullback (E : S) (Esub : ⟨ subsetΔ E D ⟩) where

    reverseFormula : Formula S 2
    reverseFormula = Swap.swapFo (deleteFormula x)

    reverse-reading : (a d : S) → ((a ∷ d ∷ []) ⊨ reverseFormula) ≡ Delete d a x
    reverse-reading a d = Swap.⊨-swap (deleteFormula x) a d

    B : S
    B = FI.imageIn E F reverseFormula

    B-sub : ⟨ subsetΔ B F ⟩
    B-sub = FI.image-sub E F reverseFormula

    B-in : (d a : S) → ⟨ d ∈ˢ E ⟩ → ⟨ a ∈ˢ F ⟩ → ⟨ Delete d a x ⟩ → ⟨ a ∈ˢ B ⟩
    B-in d a hd ha h = FI.image-in E F reverseFormula d a hd ha
      (subst ⟨_⟩ (sym (reverse-reading a d)) h)

    B-out : (a : S) → ⟨ a ∈ˢ B ⟩ → ⟨ cut a x ∈ˢ E ⟩
    B-out a ha = PT.rec (snd (cut a x ∈ˢ E))
      (λ { (d , hd , sat) → subst (λ t → ⟨ t ∈ˢ E ⟩)
        (cut-unique d a x (subst ⟨_⟩ (reverse-reading a d) sat .snd)) hd })
      (FI.image-out E F reverseFormula a ha)

    module ReverseGraph = FP.Graph E B reverseFormula

    pullback-injection : ⟨ CB.injectable E B ⟩
    pullback-injection = ∣ ReverseGraph.graph , ReverseGraph.injection
      (λ d hd → PT.map (λ { (a , ha , h) → a , B-in d a hd ha h
        , subst ⟨_⟩ (sym (reverse-reading a d)) h }) (D-out d (Esub d hd)))
      (λ d a b sa sb → delete-injective a d b x
        (subst ⟨_⟩ (reverse-reading a d) sa) (subst ⟨_⟩ (reverse-reading b d) sb))
      (λ d a e sd se → delete-single a d e x
        (subst ⟨_⟩ (reverse-reading a d) sd) (subst ⟨_⟩ (reverse-reading a e) se)) ∣₁

    B-uncountable : (w : S) → ⟨ UC.uncountable w E ⟩ → ⟨ UC.uncountable w B ⟩
    B-uncountable w unE countB = unE
      (FP.CO.injectable-trans sep coll pair E B w pullback-injection countB)

    root-pullback : (r : S)
      → ((d e : S) → ⟨ d ∈ˢ E ⟩ → ⟨ e ∈ˢ E ⟩
          → (⟨ d ≈ˢ e ⟩ → ⟨ ⊥ ⟩) → ⟨ Intersection d e r ⟩)
      → (a b : S) → ⟨ a ∈ˢ B ⟩ → ⟨ b ∈ˢ B ⟩
      → (⟨ a ≈ˢ b ⟩ → ⟨ ⊥ ⟩) → ⟨ Intersection a b (GS.join r (GS.singleton x)) ⟩
    root-pullback r root a b ha hb neq = cut-intersection-root a b (cut a x) (cut b x) x r
      (contains a (B-sub a ha) , cut-witness a x)
      (contains b (B-sub b hb) , cut-witness b x)
      (root (cut a x) (cut b x) (B-out a ha) (B-out b hb)
        (λ eq → neq (subst ⟨_⟩ (sym (paths a b))
          (cut-injective a b x (contains a (B-sub a ha)) (contains b (B-sub b hb)) (≈→≡ eq)))))
