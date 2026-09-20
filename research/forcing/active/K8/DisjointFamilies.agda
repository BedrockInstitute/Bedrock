{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DisjointFamilies
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
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∀̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ )
import K8.GroundSets
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed

disjoint : S → S → Ω
disjoint a b = ⋀ S (λ z → (z ∈ˢ a) ⇒ ((z ∈ˢ b) ⇒ ⊥))

disjointAt : ∀ {n} → Fin n → Fin n → Formula S n
disjointAt a b = ∀̇∈ (var a)
  ((var zero ∈̇ var (suc b)) ⇒̇ ⊥̇)

disjointAt-reading : ∀ {n} (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ disjointAt a b) ≡ disjoint (lookup a γ) (lookup b γ)
disjointAt-reading a b γ = refl

pairwiseDisjoint : S → Ω
pairwiseDisjoint B = ⋀ S (λ a → (a ∈ˢ B) ⇒
  ⋀ S (λ b → (b ∈ˢ B) ⇒ (((a ≈ˢ b) ⇒ ⊥) ⇒ disjoint a b)))

pairwiseDisjointAt : ∀ {n} → Fin n → Formula S n
pairwiseDisjointAt B =
  ∀̇∈ (var B) (∀̇∈ (var (suc B))
    (((var (suc zero) ≐ var zero) ⇒̇ ⊥̇)
      ⇒̇ disjointAt (suc zero) zero))

pairwiseDisjointAt-reading : ∀ {n} (B : Fin n) (γ : S ^ n)
  → (γ ⊨ pairwiseDisjointAt B) ≡ pairwiseDisjoint (lookup B γ)
pairwiseDisjointAt-reading B γ = refl

maximalDisjoint : S → S → Ω
maximalDisjoint F B =
    subsetΔ B F
  ⊓ (pairwiseDisjoint B
  ⊓ ⋀ S (λ C → (subsetΔ B C) ⇒ ((subsetΔ C F) ⇒
       (pairwiseDisjoint C ⇒ subsetΔ C B))))

maximalDisjointAt : ∀ {n} → Fin n → Fin n → Formula S n
maximalDisjointAt F B =
    subsetAtˢ B F
  ∧̇ (pairwiseDisjointAt B
  ∧̇ ∀̇ (subsetAtˢ (suc B) zero
      ⇒̇ (subsetAtˢ zero (suc F)
      ⇒̇ (pairwiseDisjointAt zero ⇒̇ subsetAtˢ zero (suc B)))))

maximalDisjointAt-reading : ∀ {n} (F B : Fin n) (γ : S ^ n)
  → (γ ⊨ maximalDisjointAt F B)
    ≡ maximalDisjoint (lookup F γ) (lookup B γ)
maximalDisjointAt-reading F B γ = refl

empty-pairwise : ⟨ pairwiseDisjoint GS.empty ⟩
empty-pairwise a ha = Empty.rec* (GS.empty-out a ha)

pairwise-subfamily : (B C : S) → ⟨ subsetΔ C B ⟩
  → ⟨ pairwiseDisjoint B ⟩ → ⟨ pairwiseDisjoint C ⟩
pairwise-subfamily B C sub h a ha b hb = h a (sub a ha) b (sub b hb)

disjoint-sym : (a b : S) → ⟨ disjoint a b ⟩ → ⟨ disjoint b a ⟩
disjoint-sym a b h z hzB hzA = h z hzA hzB

adjoin-pairwise : (B a : S) → ⟨ pairwiseDisjoint B ⟩
  → ((b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ disjoint a b ⟩)
  → ⟨ pairwiseDisjoint (GS.join B (GS.singleton a)) ⟩
adjoin-pairwise B a hB apart x hx y hy neq =
  PT.rec (snd (disjoint x y)) first
    (subst ⟨_⟩ (GS.join-spec B (GS.singleton a) x) hx)
  where
  split : (z : S) → ⟨ z ∈ˢ GS.singleton a ⟩ → ⟨ z ≈ˢ a ⟩
  split z hz = GS.singleton-witness a .snd z hz

  first : (⟨ x ∈ˢ B ⟩ ⊎ ⟨ x ∈ˢ GS.singleton a ⟩) → ⟨ disjoint x y ⟩
  first (inl⊎ xB) = PT.rec (snd (disjoint x y)) (second xB)
    (subst ⟨_⟩ (GS.join-spec B (GS.singleton a) y) hy)
    where
    second : ⟨ x ∈ˢ B ⟩
      → (⟨ y ∈ˢ B ⟩ ⊎ ⟨ y ∈ˢ GS.singleton a ⟩) → ⟨ disjoint x y ⟩
    second xB (inl⊎ yB) = hB x xB y yB neq
    second xB (inr⊎ ya) z zx zy =
      apart x xB z
        (subst (λ t → ⟨ z ∈ˢ t ⟩) (GS.≈→≡ (split y ya)) zy) zx
  first (inr⊎ xa) = PT.rec (snd (disjoint x y)) second
    (subst ⟨_⟩ (GS.join-spec B (GS.singleton a) y) hy)
    where
    second : (⟨ y ∈ˢ B ⟩ ⊎ ⟨ y ∈ˢ GS.singleton a ⟩) → ⟨ disjoint x y ⟩
    second (inl⊎ yB) z zx zy = apart y yB z
      (subst (λ t → ⟨ z ∈ˢ t ⟩) (GS.≈→≡ (split x xa)) zx) zy
    second (inr⊎ ya) = Empty.rec* (neq
      (subst ⟨_⟩ (sym (paths x y))
        (GS.≈→≡ (split x xa) ∙ sym (GS.≈→≡ (split y ya)))))

maximal→hitting : LEM ℓ → (F B a : S) → ⟨ maximalDisjoint F B ⟩
  → ((c : S) → ⟨ c ∈ˢ F ⟩ → ⟨ ⋁ S (λ z → z ∈ˢ c) ⟩)
  → ⟨ a ∈ˢ F ⟩
  → ⟨ ⋁ S (λ b → (b ∈ˢ B) ⊓ ⋁ S (λ z → (z ∈ˢ a) ⊓ (z ∈ˢ b))) ⟩
maximal→hitting lem F B a maximal nonempty ha = decide (lem goal)
  where
  goal : Ω
  goal = ⋁ S (λ b → (b ∈ˢ B) ⊓ ⋁ S (λ z → (z ∈ˢ a) ⊓ (z ∈ˢ b)))

  decide : ⟨ goal ⟩ ⊎ (⟨ goal ⟩ → Empty.⊥) → ⟨ goal ⟩
  decide (inl⊎ hit) = hit
  decide (inr⊎ miss) = Empty.rec* contradiction
    where
    apart : (b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ disjoint a b ⟩
    apart b hb z hza hzb = Empty.rec (miss ∣ b , hb , ∣ z , hza , hzb ∣₁ ∣₁)

    C : S
    C = GS.join B (GS.singleton a)

    BsubC : ⟨ subsetΔ B C ⟩
    BsubC b hb = subst ⟨_⟩ (sym (GS.join-spec B (GS.singleton a) b)) ∣ inl⊎ hb ∣₁

    CsubF : ⟨ subsetΔ C F ⟩
    CsubF c hc = PT.rec (snd (c ∈ˢ F))
      (λ { (inl⊎ hb) → maximal .fst c hb
         ; (inr⊎ ca) → subst (λ t → ⟨ t ∈ˢ F ⟩)
             (sym (GS.≈→≡ (GS.singleton-witness a .snd c ca))) ha })
      (subst ⟨_⟩ (GS.join-spec B (GS.singleton a) c) hc)

    CsubB : ⟨ subsetΔ C B ⟩
    CsubB = maximal .snd .snd C BsubC CsubF
      (adjoin-pairwise B a (maximal .snd .fst) apart)

    aInC : ⟨ a ∈ˢ C ⟩
    aInC = subst ⟨_⟩ (sym (GS.join-spec B (GS.singleton a) a))
      ∣ inr⊎ (GS.singleton-witness a .fst) ∣₁

    aInB : ⟨ a ∈ˢ B ⟩
    aInB = CsubB a aInC

    contradiction : ⟨ ⊥ ⟩
    contradiction = PT.rec (snd ⊥)
      (λ { (z , hza) → apart a aInB z hza hza }) (nonempty a ha)
