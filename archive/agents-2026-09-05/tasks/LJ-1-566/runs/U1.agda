{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
module LJ-1-566.runs.U1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )

import LJ-1-524.Probe524 {ℓ} lem as P524
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- [LJ-1.524]'s carve against [LJ-1.529]'s, at ONE bound.
-- Distance: one rebuilt `rank-graph`, one rebuilt `ordQ`.
u1 : (a : S) (oa : IsOrd (fst a))
   → P524.Carve.G a oa (P529.Bound′.bnd a oa) ≡ P529.Carve.G a oa
u1 a oa = refl
