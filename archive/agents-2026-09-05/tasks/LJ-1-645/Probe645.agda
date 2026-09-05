{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.645]  CAN THE CHAPTER TAKE THE CODED CARDINAL?
--
-- The chapter's `β∈κ` (src/L/BoundedSubset.lagda.md:1710-1719) refutes the
-- AMBIENT composite injection `⟪ κ ⟫ ↪ ⟪ α ⟫` with `cardκ : IsCardinal κ`:
--   branch `β ≡ κ`:  `cardκ α α∈κ (comp-inj (transported id) β↪α)`
--   branch `κ ∈ β`:  `cardκ α α∈κ (comp-inj (ord-emb κ β)   β↪α)`
-- This probe restates the SAME site with the AMBIENT hypothesis replaced by
-- the CODED `IsCardinalL` at the same `κ`, every other site hypothesis
-- unchanged.  The coded refutant is a CODED injection
--   InjL κL αL = ∥ Σ[ F ∈ S ] InjCode F κL αL ∥₁
-- at the L-carrier.  So each branch must PRODUCE a coded injection from the
-- AMBIENT composite it is handed.  That production is the measured W3.
--
-- VERDICT (W3): `ord-emb` CARRIES a code -- its element function is the
-- ordinal inclusion x ↦ x (BoundedSubset:1371-1375), a definable relation.
-- `β↪α` DOES NOT CARRY a code: its `πX↪α` leg is `λ p → CSel.h (IC.inv p)`
-- (BoundedSubset:1691), and `CSel.h` is a `leastOf` choice (BoundedSubset:1115)
-- over the host-language code type, which the model `L` cannot express as a
-- set.  Both composites share the `β↪α` leg, so BOTH branches are blocked by
-- the SAME obstruction.  The chapter CANNOT take `IsCardinalL` in place of
-- `IsCardinal`.  NO-GO.
--
-- The uninhabitable full term `beta-in-kappa-coded` (the two coded refutations
-- as unsolved holes) is measured in runs/floor-1.agda.txt.  THIS file
-- typechecks: it prices the frame and names the obstruction.
--
-- CALIBER: the program set `GHCRTS=-A64m -I0 -M2g` on this pane.  One Agda
-- process at a time.  Nothing lands in `src/`.  No commit, no push.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-645.Probe645 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import V.Model {ℓ} using ( self∈sucV )
  open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL )
  open import L.Ordinal {ℓ} using ( suc-ord )
  open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
  open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
  open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )

  open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
  open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
  open import Cubical.HITs.CumulativeHierarchy.Constructions
    using ( module InfinitySet; _∪_ ; ⁅_⁆s )
  open InfinitySet {ℓ} using ( ω; sucV )
  open import Cubical.Data.Sigma using ( _×_ )
  import Cubical.Data.Sum as Sum
  import Cubical.Data.Empty as Empty
  open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ ; ∣_∣₁ )

  open hPropStructure 𝒮ᵥ                    -- ambient S = V, _∈ˢ_
  module SL = hPropStructure 𝒮ʟ             -- L-carrier S_L = Σ[ x ∈ V ] isL x
  open Devlin55 using ( comp-inj; ord-emb )

  -- The CODED refutant at the same κ, α, at the L-carrier.
  InjL : SL.S → SL.S → Type (ℓ-suc ℓ)
  InjL a b = ∥ Σ[ F ∈ SL.S ] InjCode F a b ∥₁

  -- ===================================================================
  -- The site, with the coded cardinal added at the same κ.
  -- ===================================================================

  module Beta
    (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
        → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
    (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
    (isLκ : ⟨ isL κ ⟩) (isLα : ⟨ isL α ⟩)
    (cardκL : IsCardinalL (κ , isLκ))
    where

    module BSA = Devlin55.BoundedSubsetAt κ ordκ cardκ κ∉ω
      α ordα α∈κ α∉ω sq x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

    κL : SL.S
    κL = κ , isLκ
    αL : SL.S
    αL = α , isLα

    -- The coded cardinal, applied at the same α, is the CODED refutation of
    -- a CODED injection κ → α.  `α∈κ` is the coded membership, definitionally
    -- (both are the ambient `α ∈ κ` at fst of the L-carrier pairs).
    refutes-coded-inj : InjL κL αL → Empty.⊥
    refutes-coded-inj = cardκL αL α∈κ

    module Co
      (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩)
      (cover : (y : S) → ⟨ y ∈ˢ BSA.HS.M ⟩
             → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
                 × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
      where

      open BSA.Co levelIn cover using ( β; β-isOrd; β↪α; πX↪α; ext )

      -- ===============================================================
      -- W3.  THE TWO LEGS, AND WHICH CARRIES A CODE.
      -- ===============================================================

      -- DEFINABLE leg.  `ord-emb`'s element function is the ordinal inclusion
      -- x ↦ x (BoundedSubset:1371-1375): for m a presented element of the
      -- ordinal κ, the value in β is the same underlying V-element.  A
      -- definable relation, so its graph (the diagonal over κ × β) is a set in
      -- L and a code can carve it.  ord-emb CARRIES a code.
      ord-emb-leg : ⟨ κ ∈ˢ β ⟩ → ⟪ κ ⟫ ↪ ⟪ β ⟫
      ord-emb-leg = ord-emb κ β β-isOrd

      -- OBSTRUCTION leg.  `πX↪α` (BoundedSubset:1691) is
      --   λ p → CSel.h (IC.inv p)
      -- and `CSel.h` (BoundedSubset:1115) is
      --   h m = fst (leastOf w lem (cls m) (nonempty m))
      -- a meta-level choice: for each hull element m it selects, by the
      -- ordinal's own well-order w, the least-count code among ALL codes of the
      -- host-language inductive type HS.H.T.Code that evaluate to m.  That code
      -- type is not a set in the model L, so the map m ↦ CSel.h m is not a set
      -- in L that a code can carve.  `β↪α` (BoundedSubset:1698) is
      -- comp-inj (transported stage-card-lower) πX↪α and inherits the
      -- obstruction.  β↪α DOES NOT carry a code.
      obstruction-leg : ⟪ BSA.HS.C.πX ⟫ ↪ ⟪ α ⟫
      obstruction-leg = πX↪α

      -- Both composites the branches need are `comp-inj (first leg) β↪α`; both
      -- therefore carry the obstruction through the shared `β↪α` leg.  The
      -- coded refutant `InjL κL αL` demands a CODED injection; the only ambient
      -- witness is the composite, which does not carry a code.  The uninhabitable
      -- full term `beta-in-kappa-coded`, with the two productions left as
      -- unsolved holes, is measured in runs/floor-1.agda.txt (runs/floor-1.out).
