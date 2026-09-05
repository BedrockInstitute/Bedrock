{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.537]  THE OBLIGATION'S TYPE, PINNED IN A SEPARATE MODULE.
--
-- The brief's type is
--
--   approx-carve : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩
--                → Σ[ f ∈ S ] (f satisfies fnAt, assignAt and supAt)
--
-- and "satisfies" is prose, so `Obligation` below spells it out and does
-- so WITHOUT [LJ-1.521]'s `Env` abbreviations: the three conjuncts are
-- written as satisfaction of `fnAt`, `assignAt` and `supAt` themselves,
-- at the environment `rankFo` puts them in (Probe521.agda:493-501).
-- `obligation-is-delivered` inhabits it by `P537.approx-carve` and by
-- nothing else.  This is [LJ-1.531]'s device (runs/Pin.agda:30-38).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-537.runs.Pin {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Model {ℓ} using ( prʟ )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))

Obligation : Type (ℓ-suc ℓ)
Obligation =
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ]
      ( ⟨ (f ∷ P521.rank-at′ a oa m mx ∷ m
           ∷ P521.ord-set-witness a oa .fst
           ∷ prʟ m (P521.rank-at′ a oa m mx) ∷ [])
          ⊨ P521.fnAt zero (s3 zero) (s2 zero) ⟩
      × ⟨ (f ∷ P521.rank-at′ a oa m mx ∷ m
           ∷ P521.ord-set-witness a oa .fst
           ∷ prʟ m (P521.rank-at′ a oa m mx) ∷ [])
          ⊨ P521.assignAt zero (s3 zero) ⟩
      × ⟨ (f ∷ P521.rank-at′ a oa m mx ∷ m
           ∷ P521.ord-set-witness a oa .fst
           ∷ prʟ m (P521.rank-at′ a oa m mx) ∷ [])
          ⊨ P521.supAt zero (suc zero) ⟩ )

obligation-is-delivered : Obligation
obligation-is-delivered = P537.approx-carve
