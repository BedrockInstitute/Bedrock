{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.547]  THE CONTROL.  `G` at its SHAPE.
--
-- `AGENTS.md:45` says a measured cure does not transfer by analogy and
-- must be re-measured at its own site.  `[LJ-1.541]` measured, in ITS
-- file, that a `hasSeparationL` carve written at a predecessor's NAME
-- does not finish while the same carve written at its SHAPE costs under
-- two seconds.  Probe547 is built on that cure, so this file and
-- BisName.agda re-measure it HERE.
--
-- This is the TEST: `G` at `[LJ-1.529]`s name.  BisBody.agda is the same file
-- with ONE line changed.  Nothing else differs, comments and the module
-- name aside.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-547.runs.BisName {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Asm (a : S) (oa : IsOrd (fst a)) where

  Q : S
  Q = P521.ord-set-witness a oa .fst

  bnd : S
  bnd = P529.Bound′.bnd a oa

  G : S
  G = P529.Carve.G a oa

  Gmem : (w : S)
       → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ P521.rankFo Q a))
  Gmem = snd (P529.rank-graph Q a bnd)

  into : (w : S) → ⟨ w ∈ˢ bnd ⟩ → ⟨ (w ∷ []) ⊨ P521.rankFo Q a ⟩
       → ⟨ w ∈ˢ G ⟩
  into w hb hs = subst ⟨_⟩ (sym (Gmem w)) (hb , hs)

  outof : (w : S) → ⟨ w ∈ˢ G ⟩ → ⟨ (w ∷ []) ⊨ P521.rankFo Q a ⟩
  outof w h = subst ⟨_⟩ (Gmem w) h .snd
