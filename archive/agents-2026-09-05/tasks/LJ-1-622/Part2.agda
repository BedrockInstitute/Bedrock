{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.622]  PART 2 of 4: the separation module.  Probe section 3.
-- The ambient cardinal, built by separating out of the successor of a
-- non-injecting ordinal the members that inject into the bound.
-- The header is the same eleven-module set as Part 1, and Part 1 is
-- imported so that this process holds what a single fresh master holds
-- at this point: Part 1's data, warm.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-622.Part2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset; Lset→isL; isTransV
        ; isPropIsTransV )
open import L.Ordinal {ℓ} using ( ∅-ord; ω-ord; mem-ord; suc-ord; setUnion-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55 )
open import L.CantorBernstein {ℓ} lem using ( readL )

open Devlin55 using ( comp-inj; ord-emb )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _∈ₛ_; _⊆_; extensionality; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; module SeparationSet; ⋃_; union-ax )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp×; isPropΣ )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )
open import Cubical.Functions.Embedding
  using ( isEmbedding; injEmbedding; isEmbedding→hasPropFibers
        ; Embedding-into-isSet→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )

import LJ-1-622.Part1 {ℓ} lem as P1
-- =====================================================================
-- SECTION 3.  THE AMBIENT CARDINAL, BY SEPARATION.
--
--   Fix an ordinal `a` and an ordinal `β`.  Separate out of β the
--   members that inject into a.  THE PREDICATE IS ALREADY SMALL:
--   `⟪ x ⟫` and `⟪ a ⟫` both live in `Type ℓ`, so the cubical
--   library's `SeparationSet` takes it with no resizing and no
--   impredicativity parameter.
-- =====================================================================

module Sep (a : SV.S) (β : SV.S) (oβ : IsOrd β) where

  ϕ : SV.S → hProp ℓ
  ϕ x = ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ , squash₁

  open SeparationSet β ϕ using ( SEPAREE; separation-ax )

  θ : SV.S
  θ = SEPAREE

  θ-in : (x : SV.S) → ⟨ x ∈ˢ β ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ → ⟨ x ∈ˢ θ ⟩
  θ-in x x∈β h =
    ∈∈ₛ {a = x} {b = θ} .snd
      (separation-ax x .snd (∈∈ₛ {a = x} {b = β} .fst x∈β , h))

  θ⊆β : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ⟨ x ∈ˢ β ⟩
  θ⊆β x x∈θ =
    ∈∈ₛ {a = x} {b = β} .snd
      (separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .fst)

  θ-inj : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁
  θ-inj x x∈θ = separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .snd

  -- θ IS AN ORDINAL.  Its members are members of β, so they are
  -- transitive; and it is transitive itself because a member of a
  -- member of θ embeds into that member (`ord-emb`) and so into a
  -- (`comp-inj`), both delivered at src/L/BoundedSubset.lagda.md.
  θ-ord : IsOrd θ
  θ-ord = trans , (λ x x∈θ → oβ .snd x (θ⊆β x x∈θ))
    where
    trans : isTransV θ
    trans {x} {y} y∈x x∈θ =
      θ-in y (oβ .fst y∈x (θ⊆β x x∈θ))
        (PT.map
          (comp-inj (ord-emb y x (mem-ord {A = β} oβ x (θ⊆β x x∈θ)) y∈x))
          (θ-inj x x∈θ))

  -- a ∈ θ, as soon as a is inside the ambient bound.
  a∈θ : ⟨ a ∈ˢ β ⟩ → ⟨ a ∈ˢ θ ⟩
  a∈θ a∈β = θ-in a a∈β ∣ (λ m → m) , (λ m n e → e) ∣₁

  -- THE CARDINAL CLAUSE, and it is the one place the bound is spent.
  -- If θ is itself a member of β, then an injection of θ into one of
  -- its own members would put θ into θ.
  θ-card : ⟨ θ ∈ˢ β ⟩ → IsCardinal θ
  θ-card θ∈β δ δ∈θ f =
    ∈-irrefl θ (θ-in θ θ∈β (PT.map (comp-inj f) (θ-inj δ δ∈θ)))

  -- AND THE BOUND IS SPENT BY ONE WITNESS: any member of β that does
  -- NOT inject into a forces θ ∈ β through trichotomy.
  θ∈β : (γ : SV.S) → ⟨ γ ∈ˢ β ⟩ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ θ ∈ˢ β ⟩
  θ∈β γ γ∈β noinj = go (ord-tri θ θ-ord β oβ)
    where
    go : Tri θ β → ⟨ θ ∈ˢ β ⟩
    go (inl θ∈β')      = θ∈β'
    go (inr (inl e))   =
      Empty.rec (PT.rec Empty.isProp⊥ noinj
        (θ-inj γ (subst (λ v → ⟨ γ ∈ˢ v ⟩) (sym e) γ∈β)))
    go (inr (inr β∈θ)) = Empty.rec (∈-irrefl β (θ⊆β β β∈θ))
