{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.456] PROBE.  The counting leg end to end, against the
-- landed chapter.  It runs in agents/tasks/LJ-1-456/ and lands
-- nothing in src/.
--
--   W3 FIRST  `adapter`.  Typechecked ALONE, obligation omitted.
--             Identity from sq-data-closed's type to SqFam.
--             One side quantifies (δ : V ℓ) with ∈, the landed
--             side quantifies (δ : S) with ∈ˢ.
--
--   TERM      `bounded-from-residue`.  Adapter, then ∣_∣₁, then
--             landed bounded-from-trunc.  Residue and
--             sq-data-closed are module hypotheses at the types
--             the GO probes delivered.  This file rebuilds no
--             recursion and rebuilds neither seal.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( _∪_; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-456.Probe456 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; isL; 𝒮ʟ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.BoundedSubset {ℓ} lem using
  ( module UnionKit; module HullStage; IsCardinal; _↪_ )
open import L.StageBound {ℓ} lem using ( SqFam; bounded-from-trunc )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
open hPropStructure 𝒮ʟ using () renaming (S to Sʟ)

-- =====================================================================
-- W3.  adapter.  Typechecked ALONE first, obligation omitted.
-- Domain: Probe452.agda:92-96.  Codomain: StageBound.lagda.md:35-39.
-- S of 𝒮ᵥ is V ℓ (src/V/Hierarchy.lagda.md:80).  ∈ˢ of 𝒮ᵥ is ∈ (:83).
-- sq is the Sigma (src/L/Ordinal/SquareLaw.lagda.md:685-687).
-- =====================================================================

adapter :
    ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
  → SqFam α
adapter f = f

-- =====================================================================
-- THE OBLIGATION.  sq-data-closed at Probe452.agda:92-96, hypothesized,
-- not rebuilt.  Residue at Probe447.agda:208-210.  isL-ord, κL, κC are
-- module hypotheses so Residue can be restated at that type.  Neither
-- seal is rebuilt.  No induction.  The landed telescope of
-- bounded-from-trunc (src/L/StageBound.lagda.md:79-110) is applied,
-- not copied as a proof.
-- =====================================================================

module _
  (ordα : IsOrd α)
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
  (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module UK = UnionKit α lam x ordα ordλ α∈λ x⊆Lα x∈Lλ α∉ω
  module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ

  module _
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
    (sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
    (isL-ord : (y : V ℓ) → IsOrd y → ⟨ isL y ⟩)
    (κL : (a : Sʟ) (oa : IsOrd (fst a)) → Sʟ)
    (κC : (a : Sʟ) (oa : IsOrd (fst a)) → Sʟ)
    where

    Residue : Type (ℓ-suc ℓ)
    Residue =
        (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

    bounded-from-residue : Residue → ⟨ x ∈ˢ Lset κ ⟩
    bounded-from-residue _ =
      bounded-from-trunc κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω
        x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ
        levelIn cover
        ∣ adapter sq-data-closed ∣₁
