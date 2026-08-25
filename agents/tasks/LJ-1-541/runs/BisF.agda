{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.BisF {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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


-- SPELLING 3: [LJ-1.529]'s OWN shape, repeated.  `G`'s body is
-- `fst (P529.rank-graph Q a bnd)` at THIS file's local `Q` and `bnd`, so
-- the ascription below is ONE delta on `G` and then a syntactic hit,
-- exactly as `P529.Carve.sat` (Probe529.agda:234-239) is inside its own
-- module.
module DomF (a : S) (oa : IsOrd (fst a)) where

  Q : S
  Q = P529.ordQ a oa

  bnd : S
  bnd = P529.Bound′.bnd a oa

  G : S
  G = fst (P529.rank-graph Q a bnd)

  Gmem : (w : S)
       → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ P521.rankFo Q a))
  Gmem = snd (P529.rank-graph Q a bnd)


-- THE QUESTION THE TWO FAILED SPELLINGS RAISE: are the two carves the
-- same set, and can Agda SAY so?  The compare is at `S` here and not
-- under `_∈_`, so nothing has to be put in constructor form.
carve-is-529s : (a : S) (oa : IsOrd (fst a)) → DomF.G a oa ≡ P529.Carve.G a oa
carve-is-529s a oa = refl
