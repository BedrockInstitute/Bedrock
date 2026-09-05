{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.541]  THE TWO-SPELLING MEASUREMENT.  [LJ-1.524] measured that
-- two spellings of the carve do not finish (lj-1.524-report.md,
-- section 3).  These files price the SAME separation equation at two
-- spellings of the same set and at nothing else.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.BisC {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; con; _≐_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; domAt; domAt-intro )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))


-- SPELLING 1: the names written afresh.  `Q` is `P529.ordQ a oa` and
-- `bnd` is `P529.Bound′.bnd a oa`, so `fst (rank-graph Q a bnd)` and
-- `P529.Carve.G a oa` are the same set under TWO deltas and not one.
module DomC (a : S) (oa : IsOrd (fst a)) where

  Q : S
  Q = P529.ordQ a oa

  bnd : S
  bnd = P529.Bound′.bnd a oa

  G : S
  G = P529.Carve.G a oa

  Gmem : (w : S)
       → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ P521.rankFo Q a))
  Gmem = snd (P529.rank-graph Q a bnd)

