{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.118] probe A: supply absorbs-subset at the site, measure the
-- module parameter.
--
-- The master's hypothesis (src/L/BoundedSubset.lagda.md:1363-1365):
--   (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
--   → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
--   → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
--
-- The SITE INSTANCE (α = ω, x = ∅) is supplied: ∅ ∈ Lset ω, so the
-- union absorbs and the injection is transport along the extensional
-- equality (the [LJ-1.101] section 2.3 price, MEASURED here).  The
-- absorption is generic: module AbsorbsIn closes at any (α, x) with
-- x ∈ Lset α, and Site instantiates it at the consumer's own site.
--
-- The MODULE PARAMETER is a total function.  Its x ∉ Lset α branch is
-- the term this dispatch could not write: it needs (a) an injection
-- out of the union presentation ⟪ Lset α ∪ ⁅ x ⁆s ⟫ (the R-35 class,
-- the [LJ-1.101] widest unmeasured term) and (b) a shift of the stage
-- presentation, which reduces to stage-card-upper at α, i.e. honest
-- sq at every infinite ordinal, the [LJ-1.107]/[LJ-1.114] wall.
-- AbsorbsTotal below is the whole parameter modulo exactly that one
-- branch, and OutVia states the branch's reduction shape.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1118A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.BoundedSubset {ℓ} lem as BS
open BS using ( _↪_ )

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; extensionalV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; _∪_
        ; SetPackage; SingletonPackage; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open hPropStructure 𝒮ᵥ
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit; tt )
open import Cubical.Foundations.Transport using ( transport⁻Transport )
open import Cubical.Functions.Logic using ( ⇔toPath )

-- The master's hypothesis, read from src/L/BoundedSubset.lagda.md:1363-1365.
Absorbs : Type (ℓ-suc ℓ)
Absorbs = (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
        → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
        → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫

-- =====================================================================
-- THE SUPPLIED HALF: the generic absorption.  When x ∈ Lset α, the
-- union Lset α ∪ ⁅ x ⁆s is extensionally the stage, and the injection
-- is transport along that equality, injective by transport⁻Transport.
-- This is the [LJ-1.101] section 2.3 site instance, written generic
-- in (α, x, x⊆Lα, x∈Lα) (DD4).
-- =====================================================================
module AbsorbsIn (α : S) (x : S)
  (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (x∈Lα : ⟨ x ∈ˢ Lset α ⟩) where

  X : S
  X = Lset α ∪ ⁅ x ⁆s

  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = ∈∈ₛ {a = x} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ x .snd
      ∣ ⁅ x ⁆s , (pairing-ax (Lset α) (⁅ x ⁆s) (⁅ x ⁆s) .snd ∣ inr refl ∣₁ , x∈sgl) ∣₁)

  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩
  Lα∈X z z∈Lα = ∈∈ₛ {a = z} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .snd
      ∣ Lset α , (pairing-ax (Lset α) (⁅ x ⁆s) (Lset α) .snd ∣ inl refl ∣₁
                , ∈∈ₛ {a = z} {b = Lset α} .fst z∈Lα) ∣₁)

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ z z∈sgl = SetPackage.classification (SingletonPackage x) z .fst
    (∈∈ₛ {a = z} {b = ⁅ x ⁆s} .fst z∈sgl)

  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
  X-mem z z∈X = PT.rec (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .fst
      (∈∈ₛ {a = z} {b = X} .fst z∈X))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ ⁅ Lset α , ⁅ x ⁆s ⁆ ⟩ × ⟨ z ∈ₛ w ⟩)
       → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
    go (w , w∈ₛpair , z∈ₛw) = PT.rec
      (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go₂
      (pairing-ax (Lset α) (⁅ x ⁆s) w .fst w∈ₛpair)
      where
      go₂ : (w ≡ Lset α) ⊎ (w ≡ ⁅ x ⁆s)
          → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
      go₂ (inl e) = ∣ inl (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁
      go₂ (inr e) = ∣ inr (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁

  X⊆Lα : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset α ⟩
  X⊆Lα z z∈X = PT.rec (snd (z ∈ˢ Lset α)) go (X-mem z z∈X)
    where
    go : (⟨ z ∈ˢ Lset α ⟩ ⊎ ⟨ z ∈ˢ ⁅ x ⁆s ⟩) → ⟨ z ∈ˢ Lset α ⟩
    go (inl z∈Lα) = z∈Lα
    go (inr z∈sgl) = subst (λ w → ⟨ w ∈ˢ Lset α ⟩) (sym (sgl≡ z z∈sgl)) x∈Lα

  X≡Lα : X ≡ Lset α
  X≡Lα = extensionalV (λ z → ⇔toPath (X⊆Lα z) (Lα∈X z))

  inj : _↪_ ⟪ X ⟫ ⟪ Lset α ⟫
  inj = (λ m → transport (cong ⟪_⟫ X≡Lα) m)
      , λ m n h →
          sym (transport⁻Transport (cong ⟪_⟫ X≡Lα) m)
          ∙ cong (transport (sym (cong ⟪_⟫ X≡Lα))) h
          ∙ transport⁻Transport (cong ⟪_⟫ X≡Lα) n

-- =====================================================================
-- THE SITE: the [LJ-1.94] site values α = ω, x = ∅.  The site
-- supplies x∈Lα (∅ ∈ Lset ω, via ∅∈𝒟ₒ climbed by Lset-mono), so the
-- site instance of absorbs-subset is AbsorbsIn.inj at (ω, ∅).
-- =====================================================================
module Site where

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

  site-inj : _↪_ ⟪ Lset ω ∪ ⁅ ∅ ⁆s ⟫ ⟪ Lset ω ⟫
  site-inj = AbsorbsIn.inj ω ∅ x⊆Lω ∅∈Lω

-- =====================================================================
-- THE SPLIT: with LEM (lem (x ∈ˢ Lset α), a proposition), the module
-- parameter is the pair of branches (x ∈ Lset α) ⊎ (x ∉ Lset α).  The
-- in-branch is AbsorbsIn (supplied).  The out-branch is the term this
-- dispatch could not write; AbsorbsTotal states the whole parameter
-- modulo exactly that branch.
-- =====================================================================
module Split (α : S) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) (x : S)
  (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (out-branch : (⟨ x ∈ˢ Lset α ⟩ → Empty.⊥) → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫) where

  branch : (⟨ x ∈ˢ Lset α ⟩ ⊎ (⟨ x ∈ˢ Lset α ⟩ → Empty.⊥))
         → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫
  branch (inl x∈Lα) = AbsorbsIn.inj α x x⊆Lα x∈Lα
  branch (inr x∉Lα) = out-branch x∉Lα

-- The module parameter modulo the one un-writable branch.  `out` is the
-- term that cannot be written from the delivered tree (section 2 of the
-- report); everything else closes.
module AbsorbsTotal
  (out : (α : S) → (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) → (x : S)
       → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
       → (⟨ x ∈ˢ Lset α ⟩ → Empty.⊥) → _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫) where

  absorbs : Absorbs
  absorbs α α∉ω x x⊆Lα = Split.branch α α∉ω x x⊆Lα (out α α∉ω x x⊆Lα)
    (lem (x ∈ˢ Lset α))

-- =====================================================================
-- THE OUT-BRANCH'S REDUCTION SHAPE: it closes IF the tree supplied an
-- injection out of the union presentation (decomp, the R-35 class) and
-- a shift of the stage presentation (stage-shift, which reduces to
-- stage-card-upper at α, i.e. honest sq at every infinite ordinal, the
-- [LJ-1.107]/[LJ-1.114] wall).  Neither is delivered; this module only
-- states the composition that would close it.
-- =====================================================================
module OutVia (α : S) (oα : IsOrd α) (x : S)
  (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (decomp : _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ (⟪ Lset α ⟫ ⊎ Lift {ℓ-zero} {ℓ} Unit))
  (stage-shift : _↪_ (⟪ Lset α ⟫ ⊎ Lift {ℓ-zero} {ℓ} Unit) ⟪ Lset α ⟫) where

  comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
  comp-inj (f , injf) (g , injg) =
    (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

  out : _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫
  out = comp-inj decomp stage-shift
