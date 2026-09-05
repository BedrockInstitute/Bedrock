{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
module LJ-1-566.runs.U2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )

import LJ-1-524.Probe524 {ℓ} lem as P524
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- [LJ-1.559]'s carve against [LJ-1.529]'s.
-- Distance: rebuilt `rank-graph`, `ordQ` AND `Bound′`.
u2 : (a : S) (oa : IsOrd (fst a))
   → P559.Carve.G a oa ≡ P529.Carve.G a oa
u2 a oa = refl
