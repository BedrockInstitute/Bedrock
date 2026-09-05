{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.585]  W3.  ROW 1's RESIDUE AND ROW 4, SIDE BY SIDE.  TYPE ONLY.
--
-- THE BRIEF'S W3, VERBATIM: "row 1's residue and row 4, imported or
-- restated, side by side, TYPE ONLY".  Written FIRST and typechecked
-- ALONE, before any other Agda of this task.
--
-- THE QUESTION IT ANSWERS AND THE ONLY ONE: can the two statements be
-- written in ONE file at all?  If they cannot sit together, every later
-- claim that they are one object is unmeasurable.
--
-- NO TERM BELOW IS A PROOF.  Every declaration is a TYPE, or a name for
-- a type a predecessor's probe already typechecked.  Nothing is
-- restated: row 4 is [LJ-1.523]'s, row 1's residue is [LJ-1.580]'s, and
-- the hypothesis is [LJ-1.568]'s, each IMPORTED.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-585.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.HITs.CumulativeHierarchy.Constructions using ( _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- THE THREE PREDECESSORS.  Each probe is green and each type below is
-- IMPORTED from the file that typechecked it, never transcribed.
import LJ-1-523.Probe523
import LJ-1-568.Probe568
import LJ-1-580.Probe580
module P523 = LJ-1-523.Probe523 {ℓ} lem
module P568 = LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq
module P580 = LJ-1-580.Probe580 {ℓ} lem


-- 1.  ROW 4 OF [LJ-1.564]'s BILL (Probe564.agda:456-462).  It is
--     [LJ-1.523]'s `StageCountedCoded` (Probe523.agda:258-261), and it
--     lives at `{ℓ} (lem)` alone.
row4 : Type (ℓ-suc ℓ)
row4 = P523.StageCountedCoded


-- 2.  THE HYPOTHESIS THE BRIEF NAMES: [LJ-1.568]'s `Def`
--     (Probe568.agda:189-190) at `stage-card-upper`, which is that
--     file's own `B9-g` (Probe568.agda:144-147).
--
--     IT DRAGS THE FRAME.  `Def` is stated inside a module that takes
--     `L.StageCardinal`'s three parameters (α₀, oα₀, sq;
--     src/L/StageCardinal.lagda.md:15-19), so THIS file takes them too,
--     and neither row 4 nor row 1's residue mentions them.
DefAtSCU : Type (ℓ-suc ℓ)
DefAtSCU =
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
  → (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → P568.Def (LsetS δ oδ) (P568.ordS δ oδ) (fst (P568.B9-g δ oδ δ∈suc infδ))


-- 3.  ROW 1's RESIDUE.  IT DOES NOT LIVE AT `{ℓ} (lem)`: it is a term
--     of [LJ-1.580]'s `Site.CoAt`, whose telescope is
--     `Devlin55.BoundedSubsetAt`'s seventeen plus `Co`'s two
--     (Probe580.agda:117-131, :158-166).  THAT IS THIS SLICE'S FINDING:
--     the two statements sit in one file only if the file carries the
--     whole bounded-subset site, and row 4 uses none of it.
module Site
  (κᴸ : SL.S) (ordκ : IsOrd (fst κᴸ)) (cardκ : IsCardinal (fst κᴸ))
  (κ∉ω : ⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ fst κᴸ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sqα : (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
       → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
           ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module S580 = P580.Site κᴸ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sqα x x⊆Lα
                          absorbs lam ordλ α∈λ succλ x∈Lλ

  module Co
    (levelIn : (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ S580.BSA.HS.C.πX ⟩
             → ⟨ Lset δ ∈ˢ S580.BSA.HS.C.πX ⟩)
    (cover : (y : SV.S) → ⟨ y ∈ˢ S580.BSA.HS.M ⟩
           → ∥ Σ[ γ ∈ SV.S ]
                ( IsOrd γ × ⟨ γ ∈ˢ S580.BSA.HS.C.πX ⟩
                × ⟨ S580.BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁)
    where

    module C580 = S580.CoAt levelIn cover

    -- ROW 1's RESIDUE, [LJ-1.580]'s own name for it
    -- (Probe580.agda:296-297), IMPORTED.
    row1-residue : Type (ℓ-suc ℓ)
    row1-residue = C580.Leg2Coded

    -- AND THE OBLIGATION [LJ-1.580] DID NOT INHABIT
    -- (Probe580.agda:292-293), named here because section 4 of the
    -- probe will ask whether it is what stands between the two rows.
    row1-obligation : Type (ℓ-suc ℓ)
    row1-obligation = C580.BetaIntoAlphaCoded
