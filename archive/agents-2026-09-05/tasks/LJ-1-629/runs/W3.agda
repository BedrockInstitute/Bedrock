{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.629]  W3, THE WIDEST UNMEASURED TERM: Init's FOURTH conjunct
-- at the bill's site, TYPE ONLY.
--
-- THE SHAPE IS THE CHAPTER'S, not this task's to invent.  `Init` is
-- src/L/Ordinal/SquareLaw.lagda.md:692-698:
--
--     Init α = IsOrd α
--            × ⟨ ω ∈ˢ α ⟩
--            × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
--            × ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
--               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
--               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
--
-- The fourth conjunct is copied below letter for letter, as a function
-- of the ambient site, from src/L/Ordinal/SquareLaw.lagda.md:696-698.
-- The site frame is the bill's own: the three hypotheses [LJ-1.589]
-- fixed on kappa (agents/tasks/LJ-1-589/Probe589.agda:243-247, row 5's
-- kappa slots): IsOrd (fst κ), IsCardinalL κ and the trophy clause
-- ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥ (the clause at :95).
--
-- TYPE ONLY.  No term of this file proves anything.  No term of this
-- file inhabits SiteFrame, and NO TERM OF THIS FILE CARRIES THE
-- OBLIGATION NAME `site-is-init`: the name stays out of scope so the
-- program's witness reads the obligation as undelivered, which is the
-- truth of this task's return.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Cap: TWO MINUTES, set and reported by
-- this task (runs/w3-1.out).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-629.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.Ordinal.SquareLaw {ℓ} lem using ( Init )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- INIT'S FOURTH CONJUNCT AT THE SITE, TYPE ONLY.
--
-- The copy is verbatim from src/L/Ordinal/SquareLaw.lagda.md:696-698,
-- with α := the ambient site.  `init-gives-4` is the projection row
-- that ties this copy to the chapter's own spelling, so the two cannot
-- drift: the conjunct here IS the last component of `Init` there.
-- =====================================================================

Init4 : S → Type (ℓ-suc ℓ)
Init4 α =
    (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
  → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
  → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n)
  → Empty.⊥

init-gives-4 : (α : S) → Init α → Init4 α
init-gives-4 α iα = snd (snd (snd iα))

-- =====================================================================
-- THE SITE FRAME: the bill's three hypotheses, and the fourth conjunct
-- at `fst κ`.  This is the obligation's conjunct-4 shadow, and it is
-- the widest unmeasured term this task names.  NOT INHABITED here.
-- =====================================================================

SiteFrame : Type (ℓ-suc ℓ)
SiteFrame =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → Init4 (fst κ)

-- And the shadow is the obligation's: a `site-is-init` term would
-- restrict to this type by one projection.  TYPE ONLY; no converse is
-- claimed or priced here.
site-init→site4 :
    ((κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
               → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
               → Init (fst κ))
  → SiteFrame
site-init→site4 h κ oκ cκ κ∉ω = init-gives-4 (fst κ) (h κ oκ cκ κ∉ω)
