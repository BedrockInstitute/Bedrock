{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.103] probe A: attack the restated absorbs-subset.
--
-- The corrected statement (src/L/BoundedSubset.lagda.md:1364-1366):
--   (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
--   → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
--   → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
--
-- ATTACK 1: the old counterexample (α = ∅, x = ∅) is OUTSIDE the new
-- statement's domain.  The new premise at α = ∅ is itself refuted,
-- because ∅ ∈ ω, so `Absorbs` cannot be instantiated there.
--
-- ATTACK 2: the consumer site α = ω, x = ∅
-- (src/ProbeLJ194A.agda:1202-1215).  The old attack built a witness in
-- the union and pushed it into an empty stage; here Lset ω is NOT empty
-- (∅ ∈ Lset ω), and the conclusion is INHABITED: the injection exists.
-- So the attack has nothing to refute at the site, and the site supplies
-- the premise the corrected statement demands (α∉ω = ∈-irrefl ω).
--
-- Untracked probe; ONE agda process at the C-12 cap
-- (GHCRTS="-A64m -I0 -M8g"); never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1103A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.BoundedSubset {ℓ} lem as BS
open BS using ( _↪_ )

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; extensionalV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; _∪_
        ; SetPackage; SingletonPackage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open hPropStructure 𝒮ᵥ
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Transport using ( transport⁻Transport )
open import Cubical.Functions.Logic using ( ⇔toPath )

-- The corrected hypothesis, stated as a type so the attacks name it.
Absorbs : Type (ℓ-suc ℓ)
Absorbs = (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
        → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
        → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫

-- =====================================================================
-- ATTACK 1: the old counterexample (α = ∅, x = ∅) is outside the new
-- statement's domain.  The new premise at α = ∅ is itself refuted,
-- because ∅ ∈ ω, so `Absorbs` cannot be instantiated there.
-- =====================================================================
module Attack1OldSite where

  ∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
  ∅∈ω = #∈ω 0

  premise-refuted : (⟨ ∅ ∈ˢ ω ⟩ → Empty.⊥) → Empty.⊥
  premise-refuted p = p ∅∈ω

-- =====================================================================
-- ATTACK 2: the consumer site α = ω, x = ∅
-- (src/ProbeLJ194A.agda:1202-1215).  The conclusion is INHABITED at
-- the site, so the old attack shape has no witness to refute with, and
-- the site supplies the premise (α∉ω = ∈-irrefl ω).
-- =====================================================================
module Attack2Site where

  α∉ω : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
  α∉ω = ∈-irrefl ω

  x : S
  x = ∅

  x⊆Lω : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset ω ⟩
  x⊆Lω z z∈∅ = Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))

  ∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
  ∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

  ∅∈Lω : ⟨ ∅ ∈ˢ Lset ω ⟩
  ∅∈Lω = Lset-mono {α = ω} {β = sucV ∅} (#∈ω 1) ∅∈Lset1

  X : S
  X = Lset ω ∪ ⁅ ∅ ⁆s

  ∅∈ₛ⁅∅⁆ : ⟨ ∅ ∈ₛ ⁅ ∅ ⁆s ⟩
  ∅∈ₛ⁅∅⁆ = subst (λ w → ⟨ ∅ ∈ₛ w ⟩) (pair-singleton ∅)
    (pairing-ax ∅ ∅ ∅ .snd ∣ inl refl ∣₁)

  ∅∈ₛX : ⟨ ∅ ∈ₛ X ⟩
  ∅∈ₛX = union-ax ⁅ Lset ω , ⁅ ∅ ⁆s ⁆ ∅ .snd
    ∣ ⁅ ∅ ⁆s , (pairing-ax (Lset ω) (⁅ ∅ ⁆s) (⁅ ∅ ⁆s) .snd ∣ inr refl ∣₁ , ∅∈ₛ⁅∅⁆) ∣₁

  ∅∈X : ⟨ ∅ ∈ˢ X ⟩
  ∅∈X = ∈∈ₛ {a = ∅} {b = X} .snd ∅∈ₛX

  Lω∈X : (z : S) → ⟨ z ∈ˢ Lset ω ⟩ → ⟨ z ∈ˢ X ⟩
  Lω∈X z z∈Lω = ∈∈ₛ {a = z} {b = X} .snd
    (union-ax ⁅ Lset ω , ⁅ ∅ ⁆s ⁆ z .snd
      ∣ Lset ω , (pairing-ax (Lset ω) (⁅ ∅ ⁆s) (Lset ω) .snd ∣ inl refl ∣₁
                , ∈∈ₛ {a = z} {b = Lset ω} .fst z∈Lω) ∣₁)

  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset ω) ⊔ (z ∈ˢ ⁅ ∅ ⁆s) ⟩
  X-mem z z∈X = PT.rec (snd ((z ∈ˢ Lset ω) ⊔ (z ∈ˢ ⁅ ∅ ⁆s))) go
    (union-ax ⁅ Lset ω , ⁅ ∅ ⁆s ⁆ z .fst (∈∈ₛ {a = z} {b = X} .fst z∈X))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ ⁅ Lset ω , ⁅ ∅ ⁆s ⁆ ⟩ × ⟨ z ∈ₛ w ⟩)
       → ⟨ (z ∈ˢ Lset ω) ⊔ (z ∈ˢ ⁅ ∅ ⁆s) ⟩
    go (w , w∈ₛpair , z∈ₛw) = PT.rec
      (snd ((z ∈ˢ Lset ω) ⊔ (z ∈ˢ ⁅ ∅ ⁆s))) go₂
      (pairing-ax (Lset ω) (⁅ ∅ ⁆s) w .fst w∈ₛpair)
      where
      go₂ : (w ≡ Lset ω) ⊎ (w ≡ ⁅ ∅ ⁆s)
          → ⟨ (z ∈ˢ Lset ω) ⊔ (z ∈ˢ ⁅ ∅ ⁆s) ⟩
      go₂ (inl e) = ∣ inl (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁
      go₂ (inr e) = ∣ inr (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ ∅ ⁆s ⟩ → z ≡ ∅
  sgl≡ z z∈sgl = SetPackage.classification (SingletonPackage ∅) z .fst
    (∈∈ₛ {a = z} {b = ⁅ ∅ ⁆s} .fst z∈sgl)

  X⊆Lω : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset ω ⟩
  X⊆Lω z z∈X = PT.rec (snd (z ∈ˢ Lset ω)) go (X-mem z z∈X)
    where
    go : (⟨ z ∈ˢ Lset ω ⟩ ⊎ ⟨ z ∈ˢ ⁅ ∅ ⁆s ⟩) → ⟨ z ∈ˢ Lset ω ⟩
    go (inl z∈Lω) = z∈Lω
    go (inr z∈sgl) = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (sgl≡ z z∈sgl)) ∅∈Lω

  X≡Lω : X ≡ Lset ω
  X≡Lω = extensionalV (λ z → ⇔toPath (X⊆Lω z) (Lω∈X z))

  -- the injection on the union presentation: transport along the set
  -- equality, with transport⁻Transport for injectivity
  abs-site : _↪_ ⟪ X ⟫ ⟪ Lset ω ⟫
  abs-site = (λ m → transport (cong ⟪_⟫ X≡Lω) m)
    , λ m n h →
        sym (transport⁻Transport (cong ⟪_⟫ X≡Lω) m)
        ∙ cong (transport (sym (cong ⟪_⟫ X≡Lω))) h
        ∙ transport⁻Transport (cong ⟪_⟫ X≡Lω) n
