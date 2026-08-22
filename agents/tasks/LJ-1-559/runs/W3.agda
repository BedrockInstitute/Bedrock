{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.559]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it and it is a NUMBER and not a type: the FLOOR.  The
-- smallest import set under which `domAt-at-carve` can be STATED, and
-- the time that set costs with no proof in the file.  If the floor is
-- already near the timeout, the obligation cannot be met in this frame
-- and the task stops here.
--
-- `Floor` below is the obligation's TYPE and nothing else.  It is a
-- definition and not a hole, so the run exits 0 and the number is
-- comparable with a full run of the same file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-559.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( domAt )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The re-based bound.  [LJ-1.529]'s section 1 (Probe529.agda:104-142),
-- which is itself [LJ-1.490]'s `Bound` at [LJ-1.521]'s rank.  Rebuilt
-- and NOT imported: the brief forbids importing the conjunct probes.
module Bound′ (a : S) (oa : IsOrd (fst a)) where

  w : SWO {ℓc = ℓ} ⟪ fst a ⟫
  w = P521.OrdSWO∈ₛ.w (fst a) oa

  pack = boundingOrd ⟪ fst a ⟫ (P521.swo-rank′ w) (P521.swo-rank′-ord w)

  β : V ℓ
  β = pack .fst

  oβ : IsOrd β
  oβ = pack .snd .fst

  C : S
  C = β , P521.isL-ord β oβ

  module PB = PairBound a C

  bnd : S
  bnd = PB.bnd

-- The carve.  [LJ-1.490]'s (Probe490.agda:105-116) at [LJ-1.521]'s
-- `rankFo`, fed the re-based bound.
ordQ : (a : S) → IsOrd (fst a) → S
ordQ a oa = P521.ord-set-witness a oa .fst

rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ P521.rankFo Q a)))
rank-graph Q a bnd = hasSeparationL bnd (P521.rankFo Q a) .fst

module Carve (a : S) (oa : IsOrd (fst a)) where
  module B = Bound′ a oa

  G : S
  G = fst (rank-graph (ordQ a oa) a B.bnd)

-- =====================================================================
-- THE FLOOR.  The obligation's type, elaborated, with no proof.
-- =====================================================================

Floor : Type (ℓ-suc ℓ)
Floor = (a : S) (oa : IsOrd (fst a))
      → ⟨ (Carve.G a oa ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
