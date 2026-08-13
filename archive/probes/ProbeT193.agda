{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T193] D22 gate: the carve's own landing, without the
-- identification.  The landing produces ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩ at
-- a limit γ from the carried-sequence machinery alone: the segments'
-- memberships, the story's carve clause (Sset γ carved as a definable
-- subset of Lset γ), and the definable-power step 𝒟ₒ⊆Lsuc.  No
-- Sset γ ≡ Lset γ, no HF import, no Finite import.  Untracked probe;
-- no git; no master; Everything untouched.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT193 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-layer; layer-trans; isTransV; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.TowerKit {ℓ} lem ∅ using ( 𝒟ₒ⊆Lsuc )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Sset; step; Sset-suc; Sset-out; limit-succ-mem )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit )
open import L.Ordinal {ℓ} using ( ∅-ord )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The first limit where the below-lim story has content: a₀ = +ω ∅
-- (the tree's first limit ordinal, ProbeT128's carrier setup).
a₀ : S
a₀ = +ω ∅

a₀-ord : IsOrd a₀
a₀-ord = isLimit-ord a₀ (+ω-limit ∅ ∅-ord)

firstLimit : ⟨ isLimit a₀ ⟩
firstLimit = +ω-limit ∅ ∅-ord

-- The carve's own landing, generic at a limit γ.  The delivered inputs
-- are the below-lim master's own content ([T191]): the segments'
-- memberships seg∈L, the story's formula ψ over Lset γ, and the story's
-- carve clause: the extension of ψ is the target set Sset γ itself.
-- The landing is built here: the carve enters the definable power by
-- its formula (𝒟ₒ-intro), and the definable-power step (𝒟ₒ⊆Lsuc) lands
-- it one stage up.  Nothing here is the identification Sset γ ≡ Lset γ,
-- and nothing here is the membership Sset γ ∈ˢ Lset γ.
module CarveLanding
  (γ : S) (oγ : IsOrd γ) (limγ : ⟨ isLimit γ ⟩)
  (seg∈L : (ξ : S) → ⟨ ξ ∈ˢ γ ⟩ → ⟨ Sset ξ ∈ˢ Lset γ ⟩)
  (ψ : Formula ⟪ Lset γ ⟫ 1)
  (carve : DefOf.defSet (Lset γ) ψ ≡ Sset γ)
  where

  -- The truth check (D-10): every element of the target set belongs at
  -- the carve level, so the carve is grounded where it is carved.  From
  -- the segments' memberships and the limit's successor closure, with
  -- no identification.
  elem∈Lset : (x : S) → ⟨ x ∈ˢ Sset γ ⟩ → ⟨ x ∈ˢ Lset γ ⟩
  elem∈Lset x x∈S = PT.rec (snd (x ∈ˢ Lset γ)) go (Sset-out γ x x∈S)
    where
    Atr : isTransV (Lset γ)
    Atr = layer-trans (Lset-layer γ)
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ Lset γ ⟩
    go (δ , δ∈γ , x∈step) = Atr {x = Sset (sucV δ)} {y = x} x∈Suc
      (seg∈L (sucV δ) (limit-succ-mem γ δ limγ δ∈γ))
      where
      x∈Suc : ⟨ x ∈ˢ Sset (sucV δ) ⟩
      x∈Suc = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) x∈step

  -- The carve enters the definable power by its formula.
  carve∈𝒟ₒ : ⟨ Sset γ ∈ˢ 𝒟ₒ (Lset γ) ⟩
  carve∈𝒟ₒ = 𝒟ₒ-intro (Lset γ) (Sset γ) ∣ ψ , carve ∣₁

  -- The landing: the definable-power step takes the carve one stage up.
  landing : ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩
  landing = 𝒟ₒ⊆Lsuc γ (Sset γ) carve∈𝒟ₒ

-- The concrete first limit: the same landing at γ = a₀, given the
-- below-lim master's clauses at the first limit.
module FirstLimit
  (ψ₀ : Formula ⟪ Lset a₀ ⟫ 1)
  (carve₀ : DefOf.defSet (Lset a₀) ψ₀ ≡ Sset a₀)
  (seg∈L₀ : (ξ : S) → ⟨ ξ ∈ˢ a₀ ⟩ → ⟨ Sset ξ ∈ˢ Lset a₀ ⟩)
  where
  open CarveLanding a₀ a₀-ord firstLimit seg∈L₀ ψ₀ carve₀ public
