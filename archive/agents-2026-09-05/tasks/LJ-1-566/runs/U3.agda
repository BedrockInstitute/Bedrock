{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
module LJ-1-566.runs.U3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )

import LJ-1-524.Probe524 {ℓ} lem as P524
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- the two rebuilt bounds alone, with no carve above them.
u3 : (a : S) (oa : IsOrd (fst a))
   → P559.Bound′.bnd a oa ≡ P529.Bound′.bnd a oa
u3 a oa = refl
