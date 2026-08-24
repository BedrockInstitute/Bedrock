{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.622]  PART 3 of 4: the reduction.  Probe section 4.
-- From the weakest Hartogs fact to the obligation: one ambient
-- statement at one ordinal, untruncated, and its truncation map.
-- The header is the same eleven-module set as Part 1; Parts 1 and 2
-- are imported, warm, as a single fresh master holds them here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-622.Part3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

open import LJ-1-622.Part1 {ℓ} lem using ( CardAboveLᵀ; ordL; ambient→internal )
open import LJ-1-622.Part2 {ℓ} lem using ( module Sep )
-- =====================================================================
-- SECTION 4.  THE REDUCTION.  `CardAboveL` FROM ONE AMBIENT STATEMENT.
--
--   `NoInjOrd` carries NO constructibility, NO code, NO cardinal
--   predicate and NO leastness: for every ordinal, some ordinal does
--   not inject into it.  That is the Hartogs fact in its weakest form.
-- =====================================================================

NoInjOrd : Type (ℓ-suc ℓ)
NoInjOrd = (x : SV.S) → IsOrd x
         → ∥ Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ x ⟫ → Empty.⊥)) ∥₁

-- An ordinal that does not inject into `a` is automatically ABOVE `a`:
-- the other two legs of trichotomy each hand back an injection.
above : (a γ : SV.S) → IsOrd a → IsOrd γ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ a ∈ˢ γ ⟩
above a γ oa oγ noinj = go (ord-tri γ oγ a oa)
  where
  idInj : ⟪ γ ⟫ ↪ ⟪ γ ⟫
  idInj = (λ m → m) , (λ m n e → e)
  go : Tri γ a → ⟨ a ∈ˢ γ ⟩
  go (inl γ∈a)      = Empty.rec (noinj (ord-emb γ a oa γ∈a))
  go (inr (inl e))  =
    Empty.rec (noinj (subst (λ v → ⟪ γ ⟫ ↪ ⟪ v ⟫) e idInj))
  go (inr (inr a∈γ)) = a∈γ

-- THE AMBIENT HALF AT ONE ORDINAL, UNTRUNCATED.  This is the whole
-- construction; everything after it is plumbing.
cardAboveAt : (a : SV.S) → IsOrd a
  → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))
  → Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
cardAboveAt a oa (γ , oγ , noinj) =
  S.θ , S.θ-ord , S.θ-card θ∈sγ , S.a∈θ a∈sγ
  where
  module S = Sep a (sucV γ) (suc-ord oγ)
  γ∈sγ : ⟨ γ ∈ˢ sucV γ ⟩
  γ∈sγ = self∈sucV γ
  a∈sγ : ⟨ a ∈ˢ sucV γ ⟩
  a∈sγ = suc-ord oγ .fst (above a γ oa oγ noinj) γ∈sγ
  θ∈sγ : ⟨ S.θ ∈ˢ sucV γ ⟩
  θ∈sγ = S.θ∈β γ γ∈sγ noinj

ambientCardAbove : NoInjOrd → (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁
ambientCardAbove ni a oa = PT.map (cardAboveAt a oa) (ni a oa)

-- THE WHOLE OBLIGATION, GIVEN `NoInjOrd`.  GREEN, NO HOLES.
--
-- NEITHER `IsCardinalL κ` NOR `κ ∉ ω` IS CONSUMED.  Both hypotheses of
-- `CardAboveL` are dead on this route, and the report says so.
noInjOrd→CardAboveLᵀ : NoInjOrd → CardAboveLᵀ
noInjOrd→CardAboveLᵀ ni κ oκ cκ κ∉ω =
  PT.map build (ambientCardAbove ni (fst κ) oκ)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩)
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , κ∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , κ∈θ

