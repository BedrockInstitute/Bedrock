{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.626]  TIE PROBE: THE LANDED ROW IS THE SURVEYED TERM, AND THE
-- SITE'S OWN CALL IS ITS PROJECTION.
--
-- VERDICT: GO.  The obligation `landed-tie` IS in this file, at
-- section 2, and it is `refl`.  Section 1 inhabits the surveyed
-- spelling with the landed row.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.
--
-- THE BRIEF FORBIDS IMPORTING ANY PROBE, and this file obeys it: it
-- imports the LANDED chapter only, so both sides of the tie are names
-- of the live tree.  The surveyed spelling is checked against the
-- landed row's type, stated here at the chapter's own carrier `S`;
-- the carrier names agree by one delta step, because both name the
-- same universe.  The site-tie is the projection shape [LJ-1.613]
-- measured green (its full-pair form walled, its projection form is
-- refl).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
import L.StageCardinal
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open InfinitySet using ( ω; sucV )

module LJ-1-626.Probe626 {ℓ₀ : Level} (lem : LEM (ℓ-suc ℓ₀))
  (α₀ : V ℓ₀) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ₀) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ₀} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

  module SC = L.StageCardinal {ℓ₀} lem α₀ oα₀ sq

  open import V.Hierarchy {ℓ₀} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ₀} using ( Lset; 𝒟ₒ )
  open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ₀} using ( IsLeast )
  open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

  -- SECTION 1.  THE LANDED ROW, AT THE SURVEYED SPELLING.  The type
  -- is [LJ-1.625]'s surveyed statement for (ii), written here at the
  -- probe's own opened names in place of the chapter's, at the
  -- chapter's own carrier `S`; the body is the landed row itself, so
  -- the surveyed spelling is the landed row and not a variant.
  survey-spelling : (δ : S) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ₀))
    → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
    → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a
  survey-spelling δ oδ = λ P ne → SC.least-at-site δ oδ P ne

  -- SECTION 2.  THE OBLIGATION.  The projection the site's h takes
  -- IS the landed row at the site's own class-pred and nonempty: one
  -- call, named twice.
  landed-tie : (α : S) (oα : IsOrd α)
    → (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    → (infα : ⟨ α ∈ˢ ω {ℓ₀} ⟩ → Empty.⊥)
    → (D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S)
    → (inv : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    → (ih : (m : ⟪ α ⟫) → Σ[ f ∈ (⟪ Lset (⟪ α ⟫↪ m) ⟫ → ⟪ α ⟫) ]
                   ((x y : ⟪ Lset (⟪ α ⟫↪ m) ⟫) → f x ≡ f y → x ≡ y))
    → (x : ⟪ Lset α ⟫)
    → SC.LimitStep.h α α∈suc oα infα D inv ih x
      ≡ fst (SC.least-at-site α oα
              (SC.LimitStep.class-pred α α∈suc oα infα D inv ih x)
              (SC.LimitStep.nonempty α α∈suc oα infα D inv ih x))
  landed-tie _ _ _ _ _ _ _ _ = refl
