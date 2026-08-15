{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.323] RULING PROBE.  The proposed statement of `L ⊨ GCH`,
-- typechecked against the delivered tree.
--
-- WHAT THIS FILE IS.  The ruling replaces the trophy statement in
-- src/L/GCH.lagda.md.  A statement that does not typecheck is a sketch,
-- so this file states the replacement over the same telescope and the
-- same imports the delivered chapter uses, plus two certificates:
--
--   * `isPropSuccCardL`:  the successor-cardinal specification is an
--     hProp, so the payload under the truncation is proposition-valued.
--   * `isPropGCHStatement`:  the whole trophy statement is an hProp.
--     A theorem statement is a truth value; this line certifies it
--     mechanically.
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-323.Statement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isPropIsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels
  using ( isProp×; isProp×2; isPropΠ; isPropΠ2; isPropΠ3 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

-- =====================================================================
-- The L-internal injection.  `∥ Σ F ∈ S. InjCode F a b ∥₁` is the
-- model's own truth value of「some F in L is an injection of a into b」:
-- the model's ∃ is the truncated Σ over the carrier, and `InjCode`'s
-- conjuncts are satisfaction facts (src/L/Cardinal.lagda.md:223-228).
-- It is the refutand of `IsCardinalL`, reused positively.
-- =====================================================================

InjL : S → S → Type (ℓ-suc ℓ)
InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

-- =====================================================================
-- δ is THE successor cardinal of κ, in the sense of L: an ordinal
-- L-cardinal above κ, below or equal to every ordinal L-cardinal above
-- κ.  Leastness is the ordinal order, spelled with the model's own
-- subset relation `⊆ˢ` (src/FOL/ZFModel.lagda.md:141-142): for
-- ordinals, δ ⊆ c is δ ≤ c.  Every component is an hProp, so the
-- specification is an hProp and the witness δ is unique.
-- =====================================================================

SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsOrd (fst δ)
  × IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩
             → ⟨ δ ⊆ˢ c ⟩)

isPropIsCardinalL : (κ : S) → isProp (IsCardinalL κ)
isPropIsCardinalL κ =
  isPropΠ3 λ _ _ _ → Empty.isProp⊥

isPropSuccCardL : (δ κ : S) → isProp (SuccCardL δ κ)
isPropSuccCardL δ κ =
  isProp×2 (isPropIsOrd (fst δ))
           (isPropIsCardinalL δ)
           (isProp× (snd (fst κ ∈ fst δ))
                    (isPropΠ2 λ c _ →
                       isPropΠ2 λ _ _ → snd (δ ⊆ˢ c)))

-- =====================================================================
-- THE STATEMENT.  No hypothesis beyond κ itself: an ordinal that is an
-- infinite cardinal in the sense of L.  The conclusion is the internal
-- cardinal equality 2^κ = κ⁺ of the model: at the successor cardinal δ
-- of κ, the model's power set of κ and δ merely inject into each other
-- inside L.  Every existential is the model's ∃; no ambient function
-- type crosses the ⊨ boundary.
-- =====================================================================

GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHStatement zf =
  (κ : S)
  → IsOrd (fst κ)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ]
       ( SuccCardL δ κ
       × InjL (𝒫 κ) δ
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- A theorem statement is a truth value.
isPropGCHStatement : (zf : ModelL.isZFModel) → isProp (GCHStatement zf)
isPropGCHStatement zf =
  isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → PT.squash₁
