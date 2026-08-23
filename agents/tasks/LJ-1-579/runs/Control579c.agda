{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] CONTROL c.  WHAT THE ONE OPEN STATEMENT ACTUALLY NEEDS.
-- Reduce `HierBelowLimitH` to "the limit stage defines its own table",
-- through the door [LJ-1.565] measured FREE.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-579.runs.Control579c {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset; 𝒟ₒ; Lset-mono )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; Door; door; IsLimit )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ h o = ⟨ fst (hierL γ h o) ∈ Lset (step 3 γ) ⟩

------------------------------------------------------------------------
-- THE TARGET, NAMED AT THE STAGE THE LIMIT CASE ACTUALLY CARVES AT.
-- Not `step 3 γ`.  `γ` itself.
------------------------------------------------------------------------

LimitDefinable : Type (ℓ-suc ℓ)
LimitDefinable = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
               → Door (Lset γ) (fst (hierL γ h o))

------------------------------------------------------------------------
-- AND IT PAYS THE WHOLE LIMIT CASE, WITH TWO STAGES TO SPARE.
------------------------------------------------------------------------

suc∈step3 : (γ : V ℓ) → ⟨ sucV γ ∈ step 3 γ ⟩
suc∈step3 γ = ∈sucV-inl {A = sucV (sucV γ)} {x = sucV γ}
                (self∈sucV (sucV γ))

definable→limit : LimitDefinable
                → (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ)
                → IsLimit γ → HierBelowH γ h o
definable→limit d γ h o lim = Lset-mono (suc∈step3 γ) in-suc
  where
  x : V ℓ
  x = fst (hierL γ h o)
  in-𝒟 : ⟨ x ∈ 𝒟ₒ (Lset γ) ⟩
  in-𝒟 = door (Lset γ) x (d γ h o lim)
  in-suc : ⟨ x ∈ Lset (sucV γ) ⟩
  in-suc = subst (λ w → ⟨ x ∈ w ⟩) (sym (Lset-suc γ)) in-𝒟
